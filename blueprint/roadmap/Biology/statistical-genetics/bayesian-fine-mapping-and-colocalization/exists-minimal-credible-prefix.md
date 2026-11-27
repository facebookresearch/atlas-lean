# A minimum-size credible set exists and is a sorted prefix

Let $\iota$ be a finite set with $m$ elements, let $\alpha : \iota \to \mathbb{R}$, and let $\sigma : \{0, \dots, m-1\} \to \iota$ be a bijection such that $i \mapsto \alpha_{\sigma(i)}$ is nonincreasing. Let $\rho \in \mathbb{R}$ with $\rho \le \sum_{j \in \iota} \alpha_j$. Then there is a natural number $k$ such that

- the [prefix](sorted-prefix.md) $\mathrm{Pre}_\sigma(k)$ is a [$\rho$-credible set](is-credible-set.md);
- $\mathrm{Pre}_\sigma(k)$ has exactly $k$ elements;
- every $\rho$-credible set $S \subseteq \iota$ has at least $k$ elements.
