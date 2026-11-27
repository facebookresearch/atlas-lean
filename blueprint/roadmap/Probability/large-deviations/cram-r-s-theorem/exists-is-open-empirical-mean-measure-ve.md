# Local Chernoff bound near a point

Let $\mu$ be a probability measure, let $X_0, X_1, \dots$ be measurable, independent random vectors
in $\mathbb{R}^d$, each identically distributed with $X_0$, with
$\mathbb{E}[e^{\langle t, X_0\rangle}] < \infty$ for every $t$, and let $\mu_n$ be the [law of the
empirical mean](empirical-mean-measure-vec.md). If $x \in \mathbb{R}^d$ and $q \in \mathbb{R}$
satisfy $q < I(x)$, where $I$ is the [Cramér rate function](cramer-rate-function.md) of $X_0$,
then there is an open set $U \ni x$ (an open half-space) with $\mu_n(U) \le e^{-nq}$ for every
$n \in \mathbb{N}$.
