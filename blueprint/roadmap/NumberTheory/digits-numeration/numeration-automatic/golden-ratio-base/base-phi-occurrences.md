# Occurrence set of a digit block

For an integer $k$ and a word $w = w_1 w_2 \cdots w_\ell$
of natural numbers, the occurrence set of $w$ at position $k$ is the set of natural numbers $N$
that have a base phi expansion $S$ (the set of positions of its digits $1$) whose digits
$d_k d_{k-1} \cdots d_{k-\ell+1}$ spell $w$: for each $j = 1, \dots, \ell$, the position
$k - j + 1$ lies in $S$ if and only if $w_j = 1$.

The paper's $R_w$, the set of $N$ whose expansion has the end block $w$ at positions
$\ell - 1, \dots, 0$, is the case $k = \ell - 1$, and $R_{\cdot w}$, the set of $N$ whose digits at
positions $-1, \dots, -\ell$ spell $w$, is the case $k = -1$.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Sections 6 and 7 (occurrence sequences `R_w`).
