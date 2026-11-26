# Fixed-direction Chernoff bound, rate form

Let $\mu$ be a probability measure, let $X_0, X_1, \dots$ be measurable, independent random vectors
in $\mathbb{R}^d$, each identically distributed with $X_0$, and let $\mu_n$ be the [law of the
empirical mean](empirical-mean-measure-vec.md). Let $F \subseteq \mathbb{R}^d$ be measurable and
$\xi \in \mathbb{R}^d$ with $e^{\langle \xi, X_0\rangle}$ integrable, let $\Lambda$ be the [real
log moment generating function](log-mgfvec.md) of $X_0$, and suppose that the set
$\{\langle \xi, x\rangle - \Lambda(\xi) : x \in F\}$ is bounded below, with infimum $s$ (taken to
be $0$ if $F$ is empty). Then

$$\limsup_{n \to \infty} \mu_n(F)^{1/n} \le e^{-s} .$$

Optimizing over admissible $\xi$ gives the supremum of these fixed-direction rates; the Cramér
upper bound with the Legendre rate needs further arguments.
