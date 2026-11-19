# Lieb's concavity theorem

Fix a Hermitian $d \times d$ complex matrix $H$. The map

$$A \longmapsto \operatorname{tr} \exp(H + \log A)$$

is concave on the convex cone of positive-definite matrices, where $\log A$ is the standard matrix function (given by the functional calculus). In the scalar case $a \mapsto e^{h + \log a} = e^h a$ is linear; concavity is a genuinely noncommutative phenomenon. With Jensen's inequality it gives, in matrix concentration, $\mathbb{E}\operatorname{tr}\exp(H + X) \le \operatorname{tr}\exp(H + \log \mathbb{E}\, e^{X})$ (Tropp's Corollary 3.4.2), the engine of the subadditivity of matrix cumulant generating functions. Tropp's Chapter 8 proves it from the joint convexity of matrix relative entropy.

## Background

- [Peierls' inequality for the exponential](../../../Analysis/operator-theory/eigenvalue-inequalities/peierls-and-klein-inequalities/peierls-exp.md): background, an elementary trace-convexity inequality for $\operatorname{tr} e^{A}$ of the same family.

## Sources

- E. H. Lieb, Convex trace functions and the Wigner–Yanase–Dyson conjecture, Adv. Math. 11 (1973), 267–288, Theorem 6.
- J. A. Tropp, An Introduction to Matrix Concentration Inequalities, Found. Trends Mach. Learn. 8 (2015), 1–230, arXiv:1501.01571, Theorem 3.4.1 and Theorem 8.1.1.
