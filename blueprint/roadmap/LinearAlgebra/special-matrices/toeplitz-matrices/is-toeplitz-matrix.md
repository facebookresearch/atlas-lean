# Toeplitz matrix

A real $(n+1) \times (n+1)$ matrix $A = (a_{ij})$, with rows and columns
indexed by $\{0, \dots, n\}$, is Toeplitz if there is a function $c : \mathbb{Z} \to \mathbb{R}$
such that $a_{ij} = c(i - j)$ for all $i, j$. Equivalently, $A$ is constant along each of its
diagonals.

Only the values $c(k)$ with $-n \le k \le n$ enter the condition, so this is the same as asking
for real coefficients $c_{-n}, \dots, c_n$.

## Sources

- https://cs.uwaterloo.ca/journals/JIS/VOL18/Felsner/felsner2.tex
