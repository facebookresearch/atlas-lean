# OMP never selects an atom twice

For a subspace $L$ with orthogonal projection $P_L$ and any $s$, the residual $s - P_L s$ is orthogonal to every $w \in L$: $\langle w, s - P_L s\rangle = 0$. In particular an atom already selected has zero correlation with the residual and is not selected again.

## Background

- [Least squares, ridge and lasso regression](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/README.md): background, the same orthogonality of least-squares residuals (normal equations).

## Sources

- J. A. Tropp, Greed is good: algorithmic results for sparse approximation, IEEE Trans. Inform. Theory 50 (2004), 2231–2242, DOI 10.1109/TIT.2004.834793, proof of Theorem 3.1.
