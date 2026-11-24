# The moments of the Dirichlet process are the Blackwell–MacQueen urn

Let $\alpha > 0$, $H$ a probability measure on a measurable space $X$, $n \in \mathbb{N}$ and $A_0, \dots, A_{n-1} \subseteq X$ measurable. For the [Dirichlet process](dirichlet-process.md) $\mathrm{DP}(\alpha, H)$,

$$\int \prod_{i<n} \nu(A_i)\, \mathrm{DP}(\alpha, H)(d\nu) = P_n(X_0 \in A_0, \dots, X_{n-1} \in A_{n-1}),$$

where $P_n$ is the law of the first $n$ draws of the [Blackwell–MacQueen urn](../blackwell-macqueen-urn/blackwell-mac-queen.md) with parameter $\alpha$ and base measure $H$.

## Sources

- David Blackwell and James B. MacQueen, *Ferguson distributions via Pólya urn schemes*, Ann. Statist. 1 (1973), no. 2, 353–355, DOI 10.1214/aos/1176342372.
