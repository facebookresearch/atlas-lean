# The Metropolis–Hastings chain converges to its target

Let $\alpha$ be a finite set, $\pi$ a probability distribution on $\alpha$ with $\pi(x) \ne 0$ for
every $x$, and $Q$ a proposal assigning to each $x$ a probability distribution $Q(x, \cdot)$ on
$\alpha$, whose support is symmetric ($Q(x, y) \ne 0$ implies $Q(y, x) \ne 0$) and whose transition
matrix is primitive (some power has all entries positive). Let $P$ be the
[Metropolis–Hastings transition matrix](mh-matrix.md). Then there are constants $C$ and
$0 \le \rho < 1$ such that for every $n \in \mathbb{N}$ and every start $x$,
$d_{\mathrm{TV}}(P^n(x, \cdot), \pi) = \frac12 \sum_y \lvert P^n(x, y) - \pi(y) \rvert \le C \rho^n$.
