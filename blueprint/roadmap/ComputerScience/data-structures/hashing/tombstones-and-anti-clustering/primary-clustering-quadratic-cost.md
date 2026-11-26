# Primary clustering: insertion-only linear probing costs $\Theta(x^2)$

For insertion-only linear probing with a uniformly random hash function at load factor $\alpha = 1 - 1/x$ with $x > 1$ fixed, the expected cost of an insertion (an unsuccessful search) tends to $\frac12\left(1 + x^2\right)$ as $n \to \infty$, and the expected cost of a successful search tends to $\frac12(1 + x)$. In particular insertion cost is $\Theta(x^2)$, a phenomenon called primary clustering.

## Proof sketch

Knuth's limits for linear probing give unsuccessful-search cost $\frac12\left(1 + (1-\alpha)^{-2}\right)$ and successful-search cost $\frac12\left(1 + (1-\alpha)^{-1}\right)$; substitute $(1 - \alpha)^{-1} = x$.

## Depends on

- [Expected cost of an unsuccessful linear-probing search at a fixed load factor](../analysis-of-linear-probing/tendsto-insertion-cost.md)
- [Expected cost of a successful linear-probing search at a fixed load factor](../analysis-of-linear-probing/tendsto-successful-search-cost.md)

## Proof depends on

- [Expected cost of an unsuccessful linear-probing search at a fixed load factor](../analysis-of-linear-probing/tendsto-insertion-cost.md)
- [Expected cost of a successful linear-probing search at a fixed load factor](../analysis-of-linear-probing/tendsto-successful-search-cost.md)

## Sources

- Donald E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd ed., Addison-Wesley (1998).
- Michael A. Bender, Bradley C. Kuszmaul, William Kuszmaul, "Linear Probing Revisited: Tombstones Mark the Demise of Primary Clustering", FOCS (2021), arXiv:2107.01250.
