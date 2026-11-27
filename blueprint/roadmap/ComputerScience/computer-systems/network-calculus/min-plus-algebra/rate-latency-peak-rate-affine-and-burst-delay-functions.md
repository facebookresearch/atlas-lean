# Rate-latency, peak-rate, affine and burst-delay functions

The following functions belong to the set $\mathcal F$ of [min-plus convolution](min-plus-convolution-and-deconvolution.md); each vanishes for $t \le 0$ and is given for $t > 0$.

- *Peak-rate function* with rate $R \ge 0$: $\lambda_R(t) = Rt$.
- *Burst-delay function* with delay $T \ge 0$: $\delta_T(t) = +\infty$ for $t > T$ and $\delta_T(t) = 0$ for $t \le T$.
- *Rate-latency function* with rate $R \ge 0$ and latency $T \ge 0$: $\beta_{R,T}(t) = R\,[t - T]^+ = R \max(t - T, 0)$.
- *Affine function* with rate $r \ge 0$ and burst $b \ge 0$: $\gamma_{r,b}(t) = rt + b$; it jumps from $0$ to $b$ at $t = 0$.

For example $\beta_{R,T} = \delta_T \otimes \lambda_R$, and for $0 < r < R$, $(\gamma_{r,b} \otimes \beta_{R,T})(t) = \min\{b + r(t - T), R(t - T)\}$ for $t > T$ and $0$ for $t \le T$.

## Depends on

- [Min-plus convolution and deconvolution](min-plus-convolution-and-deconvolution.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 3.1.3, Definitions 3.1.1–3.1.4, Section 3.1.6, the example after Definition 3.1.10 (the convolution of $\gamma_{r,b}$ and $\beta_{R,T}$), and Section 1.4.3 for $\beta_{R,T} = \delta_T \otimes \lambda_R$.
