# Fixed-direction Chernoff bound

Let $\mu$ be a probability measure, let $X_0, X_1, \dots$ be measurable, independent random vectors
in $\mathbb{R}^d$, each identically distributed with $X_0$, and let $\mu_n$ be the [law of the
empirical mean](empirical-mean-measure-vec.md). Let $F \subseteq \mathbb{R}^d$ be measurable,
$\xi \in \mathbb{R}^d$ with $e^{\langle \xi, X_0\rangle}$ integrable, and $a \in \mathbb{R}$ with
$a \le \langle \xi, x\rangle - \Lambda(\xi)$ for every $x \in F$, where $\Lambda$ is the [real log
moment generating function](log-mgfvec.md) of $X_0$. Then $\mu_n(F) \le e^{-na}$ for every
$n \in \mathbb{N}$.
