# Bottleneck links

In the [network model](network-model-and-feasible-rate-allocations.md), link $l$ is a *bottleneck* for source $s$ under a feasible allocation $x$ if

1. link $l$ is saturated: $\sum_i A_{l,i} x_i = c_l$; and
2. source $s$ uses $l$ and has the largest rate among the sources using it: $A_{l,s} > 0$ and $x_s \ge x_{s'}$ for all $s'$ with $A_{l,s'} > 0$.

## Depends on

- [Network model and feasible rate allocations](network-model-and-feasible-rate-allocations.md)

## Sources

- J.-Y. Le Boudec, *Rate adaptation, congestion control and fairness: a tutorial*, EPFL, version of 1 November 2021, <https://leboudec.github.io/leboudec/latex/cc/LEB3132.pdf>, Section 1.2.1, Definition 1.2.2. The source writes the second condition for the sources $s'$ using $l$; that $s$ itself uses $l$ is the reading of its examples.
