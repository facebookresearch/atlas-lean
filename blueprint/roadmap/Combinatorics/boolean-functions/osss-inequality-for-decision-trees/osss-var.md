# OSSS inequality

Let $E$ be a finite set, $\nu$ a [product probability weight](is-prob-weight.md) on $\{0, 1\}^E$ and $T$ a [decision tree](decision-tree.md) on $E$ computing the $0/1$-valued function $f_T$. Then

$$\mathrm{Var}_\nu(f_T) \le \sum_{i \in E} \delta_i(T)\, \mathrm{Inf}_i(f_T),$$

where $\delta_i(T)$ is the [revealment](reveal.md) of $i$ and $\mathrm{Inf}_i$ the [influence](infl.md) under $\nu$ (O'Donnell, Saks, Schramm, Servedio, *Every decision tree has an influential variable*, FOCS 2005).
