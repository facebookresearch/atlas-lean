# Birkhoff limit of a function

For a map $T : X \to X$ and a function $f : X \to \mathbb{R}$, the Birkhoff limit of $f$ is

$$\bar f(x) = \limsup_{n \to \infty} A_n f(x),$$

the [upper limit of the Birkhoff averages](f-star.md) $A_n f(x) = \frac{1}{n} \sum_{k=0}^{n-1} f(T^k x)$ ($A_0 f = 0$), taken in $[-\infty, \infty]$ and read as a
real number, with $\pm\infty$ replaced by $0$. When $T$ preserves a finite measure and $f$ is integrable, the
Birkhoff averages [converge almost everywhere](tendsto-birkhoff-average-ae.md) to $\bar f$.
