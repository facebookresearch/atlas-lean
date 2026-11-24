# Binomial conditioning of Poisson counts with exposures

Let $X$ and $Y$ be independent counts on a measure space (of total mass $1$, as the Poisson laws force) with $X \sim \mathrm{Poisson}(s_1r)$ and $Y \sim \mathrm{Poisson}(s_2r)$, for exposures (library sizes) $s_1, s_2 \ge 0$ with $s_1 + s_2 > 0$ and a common rate $r \ge 0$; write $\pi = s_1/(s_1 + s_2)$. Let $X$ and $Y$ be measurable. Then for every total $n$ with $P(X + Y = n) > 0$ and every $k$, $P(X = k \mid X + Y = n) = \mathrm{Bin}(n, \pi)\{k\}$, which does not depend on the nuisance rate $r$. The case $r = 0$ is included.

## Sources

- Lehmann–Romano (2005), §4.5; Przyborowski–Wileński (1940).
