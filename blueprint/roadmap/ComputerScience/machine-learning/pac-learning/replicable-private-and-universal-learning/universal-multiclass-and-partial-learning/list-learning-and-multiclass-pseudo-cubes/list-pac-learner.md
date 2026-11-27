# List PAC learners and list learnability

Let $H \subseteq Y^X$ and $k \ge 1$. A **$k$-list predictor** (a $k$-menu) is a map $\mu : X \to \binom{Y}{\le k}$ assigning to each point a set of at most $k$ labels; its error on a distribution $D$ over $X \times Y$ is $\mathrm{er}_D(\mu) = D\{(x,y) : y \notin \mu(x)\}$. The class $H$ is **$k$-list PAC learnable** if there is a function $m(\varepsilon,\delta)$ and an algorithm mapping samples to $k$-list predictors such that for every $H$-realizable $D$ and all $\varepsilon, \delta \in (0,1)$, on $m(\varepsilon,\delta)$ i.i.d. examples it outputs $\mu$ with $\mathrm{er}_D(\mu) \le \varepsilon$ with probability at least $1-\delta$. For $k = 1$ this is ordinary multiclass PAC learnability.

## Depends on

- [Learners and agnostic PAC learnability](../../../agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)
- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Sources

- N. Brukhim, D. Carmon, I. Dinur, S. Moran, A. Yehudayoff, "A Characterization of Multiclass Learnability", FOCS (2022), arXiv:2203.01550.
- M. Charikar, C. Pabbaraju, "A Characterization of List Learnability", STOC (2023), arXiv:2211.04956.
