# Vertical and horizontal deviations

For $f, g$ in the set $\mathcal F$ of [min-plus convolution](min-plus-convolution-and-deconvolution.md), the *vertical deviation* and the *horizontal deviation* are

$$
v(f, g) = \sup_{t \ge 0} \{ f(t) - g(t) \}, \qquad h(f, g) = \sup_{t \ge 0} \inf \{ d \ge 0 : f(t) \le g(t + d) \} .
$$

So $h(f, g)$ is the smallest $d \ge 0$ with $f(t) \le g(t + d)$ for all $t \ge 0$, and $v(f, g) = (f \oslash g)(0)$, $h(f, g) = \inf\{d \ge 0 : (f \oslash g)(-d) \le 0\}$.

## Depends on

- [Min-plus convolution and deconvolution](min-plus-convolution-and-deconvolution.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 3.1.11, Definition 3.1.15 and equations (3.20)–(3.22).
