# OSSS covariance inequality over all product weights

For every finite set $E$ and every [decision tree](decision-tree.md) $T$ on $E$, with computed $0/1$-valued function $f_T$: for every [product probability weight](is-prob-weight.md) $\nu$ on $\{0, 1\}^E$ and every $g : \{0, 1\}^E \to \mathbb{R}$,

$$\mathrm{Cov}_\nu(f_T, g) \le \sum_{i \in E} \delta_i(T)\, \mathrm{Inf}_i(g),$$

where $\delta_i(T)$ is the [revealment](reveal.md) of $i$ and $\mathrm{Inf}_i(g)$ the [influence](infl.md), both under $\nu$. Quantifying over all product probability weights lets the inequality be proved by induction on $T$.
