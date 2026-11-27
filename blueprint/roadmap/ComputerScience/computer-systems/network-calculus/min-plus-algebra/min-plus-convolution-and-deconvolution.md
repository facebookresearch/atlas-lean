# Min-plus convolution and deconvolution

Let $\mathcal F$ be the set of wide-sense increasing functions $f : \mathbb R \to [0, +\infty]$ (so $f(s) \le f(t)$ for $s \le t$) with $f(t) = 0$ for $t < 0$, with time continuous and no continuity assumed. The source also takes these functions left-continuous; that convention is not used here, since it would exclude $\varepsilon$ (equal to $+\infty$ for $t \ge 0$) and right-continuous flows, and sub-additive closures need not preserve it. Time is continuous on these pages; the source's discrete-time setting, with integer parameters, is not treated. Sums and pointwise minima of functions are taken pointwise, and $f \le g$ means $f(t) \le g(t)$ for all $t$.

The *min-plus convolution* of $f, g \in \mathcal F$ is

$$
(f \otimes g)(t) = \inf_{0 \le s \le t} \{ f(t - s) + g(s) \} \quad (t \ge 0), \qquad (f \otimes g)(t) = 0 \quad (t < 0).
$$

The *min-plus deconvolution* of $f$ by $g$ is

$$
(f \oslash g)(t) = \sup_{u \ge 0} \{ f(t + u) - g(u) \},
$$

defined for every real $t$ whenever $f(t+u)$ and $g(u)$ are never both infinite; unlike convolution it need not vanish for $t < 0$, so $\mathcal F$ is not closed under deconvolution.

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 3.1.3 (the set $\mathcal F$), Section 3.1.6, Definition 3.1.10 (min-plus convolution), and Section 3.1.9, Definition 3.1.13 (min-plus deconvolution).
