# Binomial conditioning of Poisson counts, joint form

Let $X$ and $Y$ be independent counts on a measure space (of total mass $1$, as the Poisson laws force) with $X \sim \mathrm{Poisson}(s_1r)$ and $Y \sim \mathrm{Poisson}(s_2r)$, for exposures (library sizes) $s_1, s_2 \ge 0$ with $s_1 + s_2 > 0$ and a common rate $r \ge 0$; write $\pi = s_1/(s_1 + s_2)$. Then for all $n, k \in \mathbb{N}$, $P(X + Y = n, X = k) = \mathrm{Bin}(n, \pi)\{k\}\cdot P(X + Y = n)$.
