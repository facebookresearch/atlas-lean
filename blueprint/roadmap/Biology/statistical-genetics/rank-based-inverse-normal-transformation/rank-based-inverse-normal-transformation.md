# Rank-based inverse normal transformation

Let $W_1, \dots, W_n$ be observations of a continuous phenotype, with $\operatorname{rank}(W_i) \in \{1, \dots, n\}$ (no ties), $\Phi$ the standard normal distribution function and $c \in [0, 1/2]$ an offset. The rank-based inverse normal transformation is

$$\mathrm{INT}(W_i) = \Phi^{-1}\!\left(\frac{\operatorname{rank}(W_i) - c}{n + 1 - 2c}\right),$$

conventionally with the Blom offset $c = 3/8$.

**Properties.**

1. For every $c \in [0, 1/2]$ the fractional ranks $(r - c)/(n + 1 - 2c)$, $r = 1, \dots, n$, lie strictly in $(0, 1)$, so all transformed values are finite.
2. The transformed sample is symmetric: the values for ranks $r$ and $n + 1 - r$ are negatives of each other, so $\sum_i \mathrm{INT}(W_i) = 0$.
3. If the $W_i$ are independent with a common continuous distribution function $F_W$, then $F_W(W_i)$ is uniform on $(0, 1)$, the empirical distribution function $F_n$ converges uniformly to $F_W$, and $\mathrm{INT}(W_i)$ is asymptotically standard normal whatever $F_W$ is.

Different offsets give $Z$-scores that are nearly linear transformations of one another, so the choice of $c$ has little effect on association tests.

## Expansion

For $r = 1$ the fractional rank is $(1-c)/(n+1-2c) > 0$, and for $r = n$ it is $(n-c)/(n+1-2c) < 1$ because $c < 1$. Symmetry holds since $\frac{(n+1-r) - c}{n+1-2c} = 1 - \frac{r - c}{n+1-2c}$ and $\Phi^{-1}(1-u) = -\Phi^{-1}(u)$. Asymptotic normality combines the probability integral transform, the Glivenko–Cantelli theorem and continuity of $\Phi^{-1}$ on $(0,1)$.

## Sources

- Z. R. McCaw, J. M. Lane, R. Saxena, S. Redline and X. Lin, "Operating characteristics of the rank-based inverse normal transformation for quantitative trait analysis in genome-wide association studies", Biometrics 76 (2020), <https://doi.org/10.1111/biom.13214> (PMC8643141); preprint version <https://doi.org/10.1101/635706>, section 2.3, Equation (3).
