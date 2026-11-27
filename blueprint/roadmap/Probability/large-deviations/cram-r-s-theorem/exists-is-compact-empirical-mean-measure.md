# Exponential tightness of the empirical means

Let $\mu$ be a probability measure, let $X_0, X_1, \dots$ be measurable, independent random vectors
in $\mathbb{R}^d$, each identically distributed with $X_0$, with
$\mathbb{E}[e^{\langle t, X_0\rangle}] < \infty$ for every $t$, and let $\mu_n$ be the [law of the
empirical mean](empirical-mean-measure-vec.md). Then for every $\ell \in \mathbb{R}$ there is a
compact set $K \subseteq \mathbb{R}^d$ (a coordinate box) such that
$\mu_n(\mathbb{R}^d \setminus K) \le 2d\, e^{-n\ell}$ for every $n \in \mathbb{N}$; the proof
uses the Chernoff bound in the $2d$ coordinate directions.
