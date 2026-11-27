# OSSS inequality

Let $E$ be a finite set, $\nu$ a [product probability weight](is-prob-weight.md) on $\{0, 1\}^E$, $T$ a [decision tree](decision-tree.md) on $E$ computing the $0/1$-valued function $f_T$, and $g : \{0, 1\}^E \to \mathbb{R}$. Then

$$\mathrm{Cov}_\nu(f_T, g) \le \sum_{i \in E} \delta_i(T)\, \mathrm{Inf}_i(g),$$

where $\delta_i(T)$ is the [revealment](reveal.md) of $i$ and $\mathrm{Inf}_i(g) = \mathbb{E}_\nu\lvert g(\omega^{i \to 1}) - g(\omega^{i \to 0})\rvert$ (O'Donnell, Saks, Schramm, Servedio, *Every decision tree has an influential variable*, FOCS 2005; in this covariance form Duminil-Copin, Raoufi, Tassion, Ann. of Math. 2019).
