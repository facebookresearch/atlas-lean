# Strongly Rayleigh probability measures on subsets of a ground set

Let $\mu$ be a probability measure on $2^{[m]}$. Its generating polynomial is

$$
g_\mu(z_1,\dots,z_m)=\sum_{S \subseteq [m]}\mu(S)\prod_{i \in S}z_i \in \mathbb{R}_{\ge 0}[z_1,\dots,z_m].
$$

The measure $\mu$ is strongly Rayleigh if $g_\mu$ is real stable, that is, $g_\mu(z) \ne 0$ whenever $\mathrm{Im}(z_i) > 0$ for all $i$. It is $k$-homogeneous if $\mu$ is supported on $k$-element sets. For disjoint $A_1,\dots,A_n \subseteq [m]$ and $S \sim \mu$ we write $A_i$ also for the random count $|S \cap A_i|$ and $A_I=\sum_{i \in I}A_i$ for $I \subseteq [n]$.

## Depends on

- [Real stable polynomials](../../../../Algebra/zeros-of-polynomials/stable-polynomials/is-real-stable.md)

## Sources

- Julius Borcea, Petter Branden, Thomas M. Liggett, "Negative Dependence and the Geometry of Polynomials", Journal of the American Mathematical Society (2009), arXiv:0707.2340.
