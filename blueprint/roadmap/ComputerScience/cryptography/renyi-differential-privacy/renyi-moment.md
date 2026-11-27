# Rényi moment

For probability mass functions $P, Q$ on a finite type and $\alpha \in \mathbb{R}$, the formal Rényi moment of order $\alpha$ is an extended real: if $P$ has [support inside](support.md) that of $Q$ and $\alpha > 1$, it is the [real Rényi moment](renyi-moment-real.md) $\sum_{w \,:\, Q(w) > 0} P(w)^{\alpha} / Q(w)^{\alpha - 1}$; otherwise it is $+\infty$. Setting it to $+\infty$ for every $\alpha \le 1$ is a convention of the formalization, matching the formal [Rényi divergence](renyi-div.md); only orders $\alpha > 1$ are used for Rényi differential privacy.
