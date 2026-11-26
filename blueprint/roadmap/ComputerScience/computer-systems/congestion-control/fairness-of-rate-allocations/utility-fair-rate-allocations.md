# Utility-fair rate allocations

In the [network model](network-model-and-feasible-rate-allocations.md), give each source $s$ a utility function $u_s$, the value to $s$ of a rate $x_s$, and each link $l$ a cost function $g_l$, the cost of carrying an amount $f$ of flow on it. A *utility-fair* allocation is a feasible allocation maximizing

$$
H(x) = \sum_{s=1}^{S} u_s(x_s) - \sum_{l=1}^{L} g_l(f_l), \qquad f_l = \sum_{s} A_{l,s} x_s .
$$

[Proportional fairness](proportionally-fair-rate-allocations.md) is the case $u_s = \ln$ with $g_l(f) = 0$ for $f \le c_l$ and $g_l(f) = +\infty$ for $f > c_l$ (the source puts the boundary on the other side, which would give every Pareto-efficient allocation the value $-\infty$), and weighted proportional fairness the case $u_s = w_s \ln$.

## Depends on

- [Network model and feasible rate allocations](network-model-and-feasible-rate-allocations.md)

## Sources

- J.-Y. Le Boudec, *Rate adaptation, congestion control and fairness: a tutorial*, EPFL, version of 1 November 2021, <https://leboudec.github.io/leboudec/latex/cc/LEB3132.pdf>, Section 1.2.3.
