# De's lower bound for pure privacy over a small universe

Let the data universe $X$ have $d \ge 33$ items, let $k \ge 2$ and $\varepsilon \in (0, 1/18]$, and let databases have at least $\Omega(\min(k, d)/\varepsilon)$ rows. Then for every $(\varepsilon, 0)$-differentially private mechanism answering $k$ counting queries (sensitivity $1$) over $X$, there is a family of queries and a database on which, with probability at least $1/2$, some answer has error at least $\Omega(\min(k, d)/\varepsilon)$. The proof constructs queries that are symmetric Lipschitz extensions: given finitely many datasets $D_h$ with real labels $g_h$ satisfying $g_h \le g_{h'} + \mathrm{excess}(D_{h'}, D_h)$, there is a query of sensitivity $1$ agreeing with every label; a packing argument over $2^{\Omega(\min(k,d))}$ datasets at small Hamming distance then applies.

## Proof sketch

Choose $2^{\Omega(L)}$ datasets, with $L = \min(k, d)/16$, that pairwise differ in many rows but are all within $O(L/\varepsilon)$ of a centre, together with Lipschitz-extension queries whose answers separate them by large margins. Accurate answers would place most mass of the mechanism in disjoint regions, contradicting the pure packing bound.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Neighbouring row databases](../differential-privacy/hamming-adj.md)

## Proof depends on

- [Packing lower bound for approximate differential privacy](packing-bound-approximate-dp.md)
- [Packing lower bound for pure differential privacy](../differential-privacy/packing-lower-bound-for-pure-differential.md)

## Sources

- Cynthia Dwork and Aaron Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science, 2014.
