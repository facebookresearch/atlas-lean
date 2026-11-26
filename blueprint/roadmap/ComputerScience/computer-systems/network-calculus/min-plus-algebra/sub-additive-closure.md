# Sub-additive closure

A function $f$ in the set $\mathcal F$ of [min-plus convolution](min-plus-convolution-and-deconvolution.md) is *sub-additive* if $f(t + s) \le f(t) + f(s)$ for all $s, t \ge 0$. Let $f^{(0)} = \delta_0$, the function equal to $0$ on $(-\infty, 0]$ and $+\infty$ on $(0, \infty)$, and $f^{(n)} = f \otimes f^{(n-1)}$ for $n \ge 1$, so $f^{(1)} = f$ and $f^{(2)} = f \otimes f$. The *sub-additive closure* of $f$ is

$$
\bar f = \delta_0 \wedge f \wedge (f \otimes f) \wedge (f \otimes f \otimes f) \wedge \dots = \inf_{n \ge 0} f^{(n)} .
$$

A function $f \in \mathcal F$ is called *good* if $f$ is sub-additive and $f(0) = 0$; equivalently $f(0) = 0$ and $f = f \otimes f$, or $f = \bar f$. The condition $f(0) = 0$ cannot be dropped from the second form: the absorbing zero $\varepsilon$ ($+\infty$ for $t \ge 0$) satisfies $\varepsilon \otimes \varepsilon = \varepsilon$ but is not good, and its closure is $\delta_0$.

## Depends on

- [Min-plus convolution and deconvolution](min-plus-convolution-and-deconvolution.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 3.1.7, Definition 3.1.11 (sub-additive function), Section 3.1.8, Definition 3.1.12 (sub-additive closure) and Corollary 3.1.1, and Section 1.2.3, Definition 1.2.4 (good functions).
