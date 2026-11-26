# Service curves

Consider a system $S$ and a flow through it with input and output [cumulative functions](cumulative-flows-backlog-and-virtual-delay.md) $R$ and $R^*$. The system *offers to the flow a service curve* $\beta$ if $\beta$ is wide-sense increasing with $\beta(0) = 0$ and $R^* \ge R \otimes \beta$, that is

$$
R^*(t) \ge \inf_{s \le t} \{ R(s) + \beta(t - s) \} \qquad \text{for all } t \ge 0 .
$$

When $\beta$ is continuous, this means that for each $t$ there is some $t_0 \le t$ with $R^*(t) \ge R_l(t_0) + \beta(t - t_0)$, where $R_l(t_0) = \sup_{s < t_0} R(s)$ is the limit of $R$ from the left at $t_0$. Common examples are the [rate-latency functions](min-plus-algebra/rate-latency-peak-rate-affine-and-burst-delay-functions.md) $\beta_{R,T}$ and the burst-delay functions $\delta_T$.

## Depends on

- [Cumulative flows, backlog and virtual delay](cumulative-flows-backlog-and-virtual-delay.md)
- [Min-plus convolution and deconvolution](min-plus-algebra/min-plus-convolution-and-deconvolution.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.3.1, Definition 1.3.1 and Proposition 1.3.1.
