# Vertical and horizontal deviations

For $f, g$ in the set $\mathcal F$ of [min-plus convolution](min-plus-convolution-and-deconvolution.md), the *vertical deviation*, defined when $f$ is finite (that is, $f(t) < \infty$ for every $t$), and the *horizontal deviation*, defined for all $f$ and $g$, are

$$
v(f, g) = \sup_{t \ge 0} \{ f(t) - g(t) \}, \qquad h(f, g) = \sup_{t \ge 0} \inf \{ d \ge 0 : f(t) \le g(t + d) \} .
$$

So $h(f, g)$ is the infimum of the $d \ge 0$ with $f(t) \le g(t + d)$ for all $t \ge 0$; the infimum need not be attained (for $f = 1$ on $[0, \infty)$ and $g = 1$ on $(1, \infty)$, $0$ elsewhere, $h(f, g) = 1$ but $f(0) > g(1)$), and $v(f, g) = (f \oslash g)(0)$, $h(f, g) = \inf\{d \ge 0 : (f \oslash g)(-d) \le 0\}$. The finiteness of $f$ makes the differences $f(t) - g(t)$ and the deconvolution defined: for $f = g = \delta_0$ every difference $f(t) - g(t)$ with $t > 0$ would be $+\infty - (+\infty)$. The horizontal deviation itself needs no such hypothesis; its definition uses only the order, and it is defined for all $f, g \in \mathcal F$.

## Depends on

- [Min-plus convolution and deconvolution](min-plus-convolution-and-deconvolution.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 3.1.11, Definition 3.1.15 and equations (3.20)–(3.22).
