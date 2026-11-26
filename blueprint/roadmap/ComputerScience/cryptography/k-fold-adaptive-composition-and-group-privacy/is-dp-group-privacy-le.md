# Group privacy for chains of at most k steps

Let $M$ be [$\varepsilon$-differentially private](../differential-privacy/is-dp.md) for [replace-one adjacency](../differential-privacy/replace-one.md) on databases $\mathrm{Fin}\,n \to X$, with $\varepsilon \ge 0$. If $d$ and $d'$ are joined by a [replace-one chain](replace-one-chain.md) of length $j$ and $j \le k$, then $M(d)(o) \le e^{k\varepsilon}\, M(d')(o)$ for every output $o$.
