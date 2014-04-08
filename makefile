default: pdf

pdf:
	agda --latex Code.lagda
	latexmk -pdf -use-make talk.tex
clean:
	rm *.pdf
	rm *.log
	rm *.out
	rm *.aux
	rm *latexmk
	rm *.toc
	rm *.fls
	rm *.ptb
	rm *.snm
	rm *.nav
