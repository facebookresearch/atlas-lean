# Gaussian function, Gaussian mass and discrete Gaussian on a lattice

Let $L$ be a full-rank lattice in an $n$-dimensional real inner-product space $E$. For width $s > 0$ and center $c \in E$, the Gaussian function is $\rho_{s,c}(x) = e^{-\pi\|x - c\|^2/s^2}$ and the Gaussian mass of a countable set $A$ is $\rho_{s,c}(A) = \sum_{x \in A}\rho_{s,c}(x)$. The *discrete Gaussian* $D_{L, s, c}$ is the probability distribution on $L$ with $D_{L,s,c}(x) = \rho_{s,c}(x)/\rho_{s,c}(L)$.

## Depends on

- [Gaussian mass of a lattice](../../../../../NumberTheory/diophantine-approximation/uniform-distribution-metric/reverse-minkowski-theorem/untitled.md)

## Sources

- D. Micciancio and O. Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing 37(1), 2007.
- O. Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", Journal of the ACM 56(6), 2009.
