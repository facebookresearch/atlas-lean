# Packing lower bound for pure differential privacy

Let $d_0, d_1, \dots, d_N$ be datasets with each $d_i$ at distance at most $k$ from $d_0$, and let $M$ be $\varepsilon$-differentially private. If $S_1, \dots, S_N$ are pairwise disjoint sets of outputs with $\Pr[M(d_i) \in S_i] \ge 1/2$ for every $i \ge 1$, then $N \le 2 e^{\varepsilon k}$. Consequently, for $\varepsilon > 0$, a pure differentially private mechanism whose outputs distinguish $N$ such datasets requires $k \ge \ln(N/2)/\varepsilon$.

## Depends on

- [Pure differential privacy as a measure inequality](differentially-private-zero-iff-le-smul.md)

## Proof depends on

- [Group privacy along a chain](group.md)

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Section 8.2
- M. Hardt and K. Talwar, "On the geometry of differential privacy", *Proceedings of the 42nd ACM STOC*, 2010
