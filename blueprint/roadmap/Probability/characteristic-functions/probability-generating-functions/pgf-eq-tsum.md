# Series form of the probability generating function

Let $\mu$ be a finite measure on
$\Omega$, let $X : \Omega \to \mathbb{N}$ be measurable, and let $s$ be a real number with
$|s| \le 1$. Then the probability generating function
$G_X(s) = \int_\Omega s^{X(\omega)} \, d\mu(\omega)$ of $X$ under $\mu$ satisfies

$$G_X(s) = \sum_{k=0}^{\infty} s^k \, \mu(\{\omega \in \Omega : X(\omega) = k\}).$$
