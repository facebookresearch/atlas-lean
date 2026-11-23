# Target terms of closure conversion

The terms of the closure-conversion target language,
with variables as de Bruijn indices, are: a variable $n$ for each natural number $n$; code
$\mathsf{code}\,b$ of one parameter, whose body $b$ is evaluated with only its parameter in scope,
as variable $0$; application $f\,a$ of code to an argument; the unit term $\mathsf{unit}$ (the
empty tuple); pairs $(a, b)$; the projections $\mathsf{fst}\,e$ and $\mathsf{snd}\,e$; and
$\mathsf{let}\ e\ \mathsf{in}\ b$, which binds the value of $e$ as variable $0$ in $b$.
