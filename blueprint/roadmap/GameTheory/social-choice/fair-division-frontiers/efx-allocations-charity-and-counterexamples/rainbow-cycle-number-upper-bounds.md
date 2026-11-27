# Upper bounds on the rainbow cycle number

For every $d \ge 1$ the rainbow cycle number satisfies $R(d) \le d^4 + d$, and in a $k$-partite digraph as in its definition with $k > d^4 + d$ parts a rainbow cycle can be found in time polynomial in $k$. Moreover $R(d) \le (1 + o(1))\, d \log d$, and this is tight up to the logarithmic factor since $R(d) \ge d$.

## Proof sketch

For the polynomial bound, fix a part $V$ and trace a path backwards that alternates between $V$ and the other parts, using that every vertex has an in-arc from every part; since $V$ has at most $d$ vertices, the pigeonhole principle closes a cycle that visits every part other than $V$ at most once. With more than $d^4 + d$ parts, each two-step connection through $V$ can be rerouted through a distinct bypass part, which yields a cycle visiting every part at most once. For the $d \log d$ bound, choose one vertex from each part independently and uniformly at random. A fixed chosen vertex lacks a chosen in-neighbour with probability at most $(1 - 1/d)^{k-1}$, so by the union bound, if $k(1 - 1/d)^{k-1} < 1$, with positive probability every chosen vertex has a chosen in-neighbour; the induced subgraph then contains a cycle, which is rainbow since it uses one vertex per part.

## Depends on

- [Rainbow cycle number](rainbow-cycle-number.md)

## Sources

- B. R. Chaudhury, J. Garg, K. Mehlhorn, R. Mehta, P. Misra, "Improving EFX Guarantees through Rainbow Cycle Number", EC 2021, arXiv:2103.01628.
- H. Akrami, N. Alon, B. R. Chaudhury, J. Garg, K. Mehlhorn, R. Mehta, "EFX: A Simpler Approach and an (Almost) Optimal Guarantee via Rainbow Cycle Number", EC 2023; Operations Research (2024); arXiv:2205.07638 (titled "EFX Allocations: Simplifications and Improvements").
