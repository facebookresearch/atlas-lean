# OSSS inequality for the Bernoulli product measure

Let $E$ be a finite set, $0 \le p \le 1$, $T$ a [decision tree](decision-tree.md) on $E$ computing the $0/1$-valued function $f_T$, and $g : \{0, 1\}^E \to \mathbb{R}$. Under the $p$-biased product measure,

$$\mathrm{Cov}(f_T, g) \le \sum_{i \in E} \delta_i(T)\, \mathrm{Inf}_i(g),$$

where $\delta_i(T)$ is the [revealment](reveal.md), the probability that $T$ queries $i$, and $\mathrm{Inf}_i(g) = \mathbb{E}\lvert g(\omega^{i \to 1}) - g(\omega^{i \to 0})\rvert$.
