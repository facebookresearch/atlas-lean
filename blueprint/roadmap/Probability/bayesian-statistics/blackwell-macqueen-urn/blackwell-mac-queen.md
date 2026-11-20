# Blackwell–MacQueen urn

Let $X$ be a measurable space, $\alpha \in \mathbb{R}$ and $H$ a measure on $X$. The Blackwell–MacQueen urn with parameter $\alpha$ and base measure $H$ is the sequence of measures $P_n$ on $X^n$ defined recursively: $P_0$ is the point mass at the empty sequence, and $P_{n+1}$ is the law of $(x_0, \dots, x_{n-1}, x)$ when $(x_0, \dots, x_{n-1}) \sim P_n$ and, given these, $x$ has the [Pólya urn predictive law](../dirichlet-process/polya-urn-predictive.md) $(\alpha H + \sum_{i<n} \delta_{x_i})/(\alpha + n)$. For $\alpha > 0$ and a probability measure $H$ it is the joint law of the first $n$ draws of the urn.

## Sources

- David Blackwell and James B. MacQueen, *Ferguson distributions via Pólya urn schemes*, Ann. Statist. 1 (1973), no. 2, 353–355, DOI 10.1214/aos/1176342372.
