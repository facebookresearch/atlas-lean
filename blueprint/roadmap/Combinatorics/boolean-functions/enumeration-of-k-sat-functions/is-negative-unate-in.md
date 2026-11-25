# Negatively unate variable

Let $f : \{\mathrm{true}, \mathrm{false}\}^n \to
\{\mathrm{true}, \mathrm{false}\}$ be a Boolean function and $i$ one of its $n$ variables. Then
$f$ is negatively unate in $i$ if for all assignments $x$ and $y$ that agree at every variable
other than $i$ and have $x_i = \mathrm{false}$ and $y_i = \mathrm{true}$, $f(y) = \mathrm{true}$
implies $f(x) = \mathrm{true}$. Equivalently, switching $i$ from false to true never switches
the value of $f$ from false to true.

## Sources

- Abstract *Enumerating k-SAT functions*, in M. Krivelevich, R. Morris, O. Riordan and A. Steger (organisers), *Combinatorics, Probability and Computing*, Oberwolfach Rep. 19 (2022), no. 2, 1165–1237, p. 1222, DOI 10.4171/OWR/2022/22; D. Dong, N. Mani and Y. Zhao, *Enumerating k-SAT functions*, arXiv:2107.09233: unate.
