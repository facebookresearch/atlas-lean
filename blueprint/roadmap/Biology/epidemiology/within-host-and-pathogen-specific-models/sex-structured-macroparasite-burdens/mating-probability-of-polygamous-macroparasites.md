# Mating probability of polygamous macroparasites

**Setting.** Let the number $W$ of parasites per host have probability mass function $(p_n)_{n\ge0}$, probability generating function $G(s) = \sum_n p_n s^n$ and mean $m = G'(1)$. Each parasite is independently female with probability $\alpha$ and male with probability $\beta = 1 - \alpha$. Then the number of females per host is the stopped sum $F = \sum_{i=1}^{W} Y_i$, with $Y_i \sim \mathrm{Bernoulli}(\alpha)$ i.i.d. and independent of $W$, and $M = W - F$. Mating is polygamous: one male in a host fertilises all females in that host.

**Sex distribution.** $F$ has generating function $G_F(s) = G(\beta + \alpha s)$, mean $\mu_F = \alpha m$, variance $\sigma_F^2 = \alpha^2\sigma_W^2 + \alpha\beta m$, and variance-to-mean ratio

$$\frac{\sigma_F^2}{\mu_F} = \alpha\frac{\sigma_W^2}{m} + \beta,$$

so overdispersion of the total burden passes to the females. $F$ and $M$ are dependent unless $W$ is Poisson.

**Proposition.** The mean number of fertilised females per host is $\alpha m - \alpha G'(\alpha)$. Hence the mating probability of a female, the ratio of mean fertilised females to mean females, is

$$\phi = 1 - \frac{G'(\alpha)}{m}.$$

Examples: a Poisson burden with mean $m$ gives $\phi = 1 - e^{-\beta m}$; a negative binomial burden with mean $m$ and aggregation $k$, with $G(s) = (1 + m(1-s)/k)^{-k}$, gives $\phi = 1 - (1 + \beta m/k)^{-(k+1)}$.

## Proof sketch

Conditional on $W = n$, the female count is $\mathrm{Binomial}(n, \alpha)$. All $j$ females are fertilised unless $j = n$, i.e. unless every parasite in the host is female. Hence the expected number fertilised is $\sum_j j\binom nj\alpha^j\beta^{n-j} - n\alpha^n = n\alpha - n\alpha^n$. Averaging over $W$ gives $\alpha m - \alpha\sum_n n p_n\alpha^{n-1} = \alpha m - \alpha G'(\alpha)$. Dividing by the mean female count $\alpha m$ gives $\phi$. The moments of $F$ come from differentiating $G(\beta + \alpha s)$ at $s = 1$. The examples follow by evaluating $G'(\alpha)$.

## Sources

- Gonzalo Maximiliano Lopez and Juan Pablo Aparicio, "Mathematical Modeling of Mating Probability and Fertile Egg Production in Helminth Parasites", *Bulletin of Mathematical Biology* 86 (2024), 131, <https://doi.org/10.1007/s11538-024-01356-3>. Preprint version: arXiv:2202.11552 (2022), Sections 2, 3 and 5 and Proposition A.1, <https://doi.org/10.48550/arXiv.2202.11552>.
