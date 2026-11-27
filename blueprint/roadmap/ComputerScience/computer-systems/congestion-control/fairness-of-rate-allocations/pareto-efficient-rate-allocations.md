# Pareto-efficient rate allocations

A feasible allocation $x$ in the [network model](network-model-and-feasible-rate-allocations.md) is *Pareto-efficient* (Pareto-optimal) if no rate can be increased within the feasible allocations without decreasing another: for every feasible $y$, if $y_s > x_s$ for some $s$ then $y_{s'} < x_{s'}$ for some $s'$. In general there are many Pareto-efficient allocations; any allocation in which every source uses at least one saturated link is one.

## Depends on

- [Network model and feasible rate allocations](network-model-and-feasible-rate-allocations.md)

## Sources

- J.-Y. Le Boudec, *Rate adaptation, congestion control and fairness: a tutorial*, EPFL, version of 1 November 2021, <https://leboudec.github.io/leboudec/latex/cc/LEB3132.pdf>, Section 1.1.2, Definition 1.1.1 and the example of Figure 1.4.
