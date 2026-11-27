# Network model and feasible rate allocations

A network carries the flows of sources $s = 1, \dots, S$ over links $l = 1, \dots, L$. Link $l$ has capacity $c_l > 0$, and $A_{l,s} \ge 0$ is the fraction of the traffic of source $s$ that flows on link $l$; the links with $A_{l,s} > 0$ form the route of source $s$, and $A_{l,s} \in \{0, 1\}$ when there is no load sharing. A *rate allocation* is a vector $x = (x_1, \dots, x_S)$, and it is *feasible* if $x_s \ge 0$ for all $s$ and

$$
\sum_{s=1}^{S} A_{l,s} x_s \le c_l \qquad \text{for every link } l .
$$

Link $l$ is *saturated* by $x$ when equality holds. The feasible allocations form a convex polyhedron, which is a bounded polytope when every source uses at least one link (a source on no link can take any rate), and it contains a positive allocation.

## Sources

- J.-Y. Le Boudec, *Rate adaptation, congestion control and fairness: a tutorial*, EPFL, version of 1 November 2021, <https://leboudec.github.io/leboudec/latex/cc/LEB3132.pdf>, Section 1.2.1, the paragraph "Network model".
