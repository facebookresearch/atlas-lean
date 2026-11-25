# Existence of GMRES iterates

For every real square matrix $A$, vectors $b, x_0$ and step $k$, a $k$-th GMRES iterate exists.
It is the solution of the least-squares problem
$\min_c \|r_0 - A K_k c\|_2$.

## Informally uses

- [Least-squares estimates exist](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/exists-normal.md): least-squares solutions exist for every matrix, rank-deficient included.
