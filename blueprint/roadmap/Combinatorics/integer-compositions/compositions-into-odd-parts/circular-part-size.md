# Part sizes of a circular composition

For a natural number $n$, a finite set $S \subseteq \mathbb{N}$ and $s \in \mathbb{N}$, the part size $\ell_{n,S}(s)$ is the least $d \in \{1, \dots, n\}$ with $(s + d) \bmod n \in S$, and $0$ if there is no such $d$ (in particular for $n = 0$).

Picture the cycle $C_n$ with vertices $0, \dots, n - 1$ and edges $\{s, s + 1 \bmod n\}$, the edge labelled $s$. A nonempty set $S \subseteq \{0, \dots, n-1\}$ of removed edges cuts the cycle into arcs, and for $s \in S$ the arc that starts right after edge $s$ ends at the next removed edge, so it has $\ell_{n,S}(s)$ vertices.

## Sources

- Joshua P. Bowman, *Compositions with an Odd Number of Parts, and Other Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Section 2.
