# Max-min fair rate allocations

A feasible allocation $x$ in the [network model](network-model-and-feasible-rate-allocations.md) is *max-min fair* if increasing any rate within the feasible allocations must be at the cost of decreasing some rate that is already no larger: for every feasible $y$, if $y_s > x_s$ then there is some $s'$ with $x_{s'} \le x_s$ and $y_{s'} < x_{s'}$. Priority thus goes to the sources with small rates. In the network of two links of capacity $10$ shared by one source crossing both, one source on the first and nine sources on the second, the max-min fair allocation gives $1$ to the long source and to each of the nine, and $9$ to the single source on the first link.

## Depends on

- [Network model and feasible rate allocations](network-model-and-feasible-rate-allocations.md)

## Sources

- J.-Y. Le Boudec, *Rate adaptation, congestion control and fairness: a tutorial*, EPFL, version of 1 November 2021, <https://leboudec.github.io/leboudec/latex/cc/LEB3132.pdf>, Section 1.2.1, Definition 1.2.1 and the example of Figure 1.4.
