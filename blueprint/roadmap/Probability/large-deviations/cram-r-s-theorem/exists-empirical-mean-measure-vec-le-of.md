# Chernoff bound on a compact set

Let $\mu$ be a probability measure, let $X_0, X_1, \dots$ be measurable, independent random vectors
in $\mathbb{R}^d$, each identically distributed with $X_0$, with
$\mathbb{E}[e^{\langle t, X_0\rangle}] < \infty$ for every $t$, and let $\mu_n$ be the [law of the
empirical mean](empirical-mean-measure-vec.md). Let $D \subseteq \mathbb{R}^d$ be compact and
$q \in \mathbb{R}$ with $q < I(x)$ for every $x \in D$, where $I$ is the [Cramér rate
function](cramer-rate-function.md) of $X_0$. Then there is a finite constant $M$ such that
$\mu_n(D) \le M e^{-nq}$ for every $n \in \mathbb{N}$. The proof covers $D$ by finitely many open
half-spaces.
