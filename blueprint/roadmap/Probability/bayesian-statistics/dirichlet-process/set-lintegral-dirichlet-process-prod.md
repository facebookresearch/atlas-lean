# Ferguson's conjugacy

Let $\alpha > 0$, $H$ a probability measure on a measurable space $X$, $n \in \mathbb{N}$, $A_0, \dots, A_{n-1} \subseteq X$ measurable and $S$ a measurable set of measures on $X$. Then

$$\int_S \prod_{i<n} \nu(A_i)\, \mathrm{DP}(\alpha, H)(d\nu) = \int_{A_0 \times \dots \times A_{n-1}} \mathrm{DP}\Big(\alpha + n, \frac{\alpha H + \sum_{i<n} \delta_{x_i}}{\alpha + n}\Big)(S)\, P_n(dx_0 \cdots dx_{n-1}),$$

where $P_n$ is the law of $n$ draws of the [Blackwell–MacQueen urn](../blackwell-macqueen-urn/blackwell-mac-queen.md). In words: given $n$ observations $x_0, \dots, x_{n-1}$ from $G \sim \mathrm{DP}(\alpha, H)$, the posterior law of $G$ is $\mathrm{DP}(\alpha + n, (\alpha H + \sum_i \delta_{x_i})/(\alpha + n))$.

## Sources

- Thomas S. Ferguson, *A Bayesian analysis of some nonparametric problems*, Ann. Statist. 1 (1973), no. 2, 209–230, DOI 10.1214/aos/1176342360, Theorem 1.
