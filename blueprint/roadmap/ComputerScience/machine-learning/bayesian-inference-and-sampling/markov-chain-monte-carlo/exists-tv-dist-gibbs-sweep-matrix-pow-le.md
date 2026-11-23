# The systematic-scan Gibbs sampler converges to its target

Let $\pi$ be a probability distribution on the configurations $x : \iota \to S$, with $\iota$ and
$S$ finite, such that $\pi(x) \ne 0$ for every $x$, and let $l$ be a list of coordinates in which
every coordinate occurs. Let $P$ be the [transition matrix of the systematic-scan Gibbs
sweep](gibbs-sweep-matrix.md) along $l$. Then there are constants $C$ and $0 \le \rho < 1$ such
that for every $n \in \mathbb{N}$ and every starting configuration $x$,
$d_{\mathrm{TV}}(P^n(x, \cdot), \pi) = \frac12 \sum_y \lvert P^n(x, y) - \pi(y) \rvert \le C \rho^n$.
