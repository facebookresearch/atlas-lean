# The integral expectation-threshold theorem implies the fractional one

For every nontrivial increasing family $\mathcal{F}$, $q(\mathcal{F}) \le q_f(\mathcal{F})$. Consequently, for families with $\ell(\mathcal{F}) \ge 2$, the Park-Pham bound $p_c(\mathcal{F}) \le K q(\mathcal{F})\log\ell(\mathcal{F})$ implies the Frankston-Kahn-Narayanan-Park bound $p_c(\mathcal{F}) \le K q_f(\mathcal{F})\log\ell(\mathcal{F})$, and every application obtained from spread measures (which certify upper bounds on $q_f$) also follows from the Park-Pham theorem.

## Proof sketch

A $p$-small cover $\mathcal{G}$ with $\sum_G p^{|G|} \le 1/2$ is in particular a fractional cover: assigning weight $1$ to each $G \in \mathcal{G}$ gives a function $g$ with $\sum_{G \subseteq F} g(G) \ge 1$ for every $F \in \mathcal{F}$ and cost at most $1/2$, so $\mathcal{F}$ is weakly $p$-small and $q \le q_f$. Substitute into the Park-Pham inequality.

## Depends on

- [Park-Pham theorem: thresholds are within a logarithmic factor of expectation thresholds](park-pham-theorem.md)
- [The Kahn-Kalai expectation threshold q(F)](kahn-kalai-expectation-threshold.md)
- [Thresholds versus fractional expectation-thresholds](../thresholds-and-expectation-thresholds/theorem-1-1.md)
- [Weakly $p$-small families](../thresholds-and-expectation-thresholds/is-weakly-small.md)

## Sources

- Jinyoung Park, Huy Tuan Pham, "A proof of the Kahn-Kalai conjecture", Journal of the AMS 37(1) (2024); arXiv:2203.17207.
- Keith Frankston, Jeff Kahn, Bhargav Narayanan, Jinyoung Park, "Thresholds versus fractional expectation-thresholds", Annals of Mathematics 194(2) (2021); arXiv:1910.13433.
- Michel Talagrand, "Are many small sets explicitly small?", STOC (2010).
