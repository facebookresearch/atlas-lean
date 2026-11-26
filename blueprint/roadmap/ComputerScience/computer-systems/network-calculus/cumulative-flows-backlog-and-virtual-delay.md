# Cumulative flows, backlog and virtual delay

A data *flow* is described by its cumulative function $R$, where $R(t)$ is the amount of data (for example, bits) seen on the flow in the interval $[0, t]$, a finite number, with $R(0) = 0$ and $R(t) = 0$ for $t < 0$ unless said otherwise. $R$ is wide-sense increasing, so it belongs to the set $\mathcal F$ of [min-plus convolution](min-plus-algebra/min-plus-convolution-and-deconvolution.md). Time is continuous, $t \ge 0$, and $R$ may be continuous (a fluid model), left-continuous or right-continuous, or neither, since $\mathcal F$ assumes no continuity.

A *system* (a buffer, a node, a network) takes an input flow $R$ and produces an output flow $R^*$; it is *lossless* when all input data eventually leaves, and $R^* \le R$ (it is causal). For a lossless system:

- the *backlog* at time $t$ is $R(t) - R^*(t)$;
- the *virtual delay* at time $t$ is $d(t) = \inf\{\tau \ge 0 : R(t) \le R^*(t + \tau)\}$.

The backlog is the vertical distance between input and output, the data held in the system. The virtual delay is the horizontal distance: for a system that serves the flow first in, first out, it is the delay of a bit arriving at $t$ (for left-continuous functions, of a hypothetical bit arriving just before $t$).

## Depends on

- [Min-plus convolution and deconvolution](min-plus-algebra/min-plus-convolution-and-deconvolution.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.1.1 (cumulative functions and the time models) and Section 1.1.2, Definition 1.1.1 (backlog and virtual delay).
