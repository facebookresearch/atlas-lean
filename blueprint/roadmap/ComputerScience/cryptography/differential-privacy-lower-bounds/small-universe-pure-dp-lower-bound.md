# De's lower bound for pure privacy over a small universe

Let $k, d, n \in \mathbb{N}$ and $\varepsilon \in (0, 1/40]$ with $n \ge \min(k, d)/\varepsilon$. There is a query $F : \mathbb{N}^{d} \to \mathbb{R}^{k}$ on histograms over a universe of $d$ items, with sensitivity at most $1$ in each coordinate, such that every $(\varepsilon, 0)$-differentially private mechanism adds noise of $L_\infty$ norm $\Omega(\min(k, d)/\varepsilon)$ with probability at least $1/2$ on some database with at most $n$ rows. The coordinates of $F$ are not counting queries. The proof constructs queries that are symmetric Lipschitz extensions: given finitely many datasets $D_h$ with real labels $g_h$ satisfying $|g_h - g_{h'}| \le \tfrac12\|D_h - D_{h'}\|_1$ for all $h, h'$ (half the $\ell_1$ distance of the histograms, which is the number of rows to replace when the sizes agree), there is a query of sensitivity $1$ agreeing with every label; a packing argument over $2^{\Omega(\min(k,d))}$ datasets at small Hamming distance then applies.

## Proof sketch

With $\ell = \min(k, d)$, choose $2^s$ datasets, $s = \ell/400$, each of weight at most $w = \ell/(1280\varepsilon)$ and pairwise at $\ell_1$ distance at least $w/10$, together with Lipschitz-extension queries whose answers separate them by large margins. Accurate answers would place most mass of the mechanism in disjoint regions, contradicting the pure packing bound.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Neighbouring row databases](../differential-privacy/hamming-adj.md)

## Proof depends on

- [Packing lower bound for approximate differential privacy](packing-bound-approximate-dp.md)
- [Packing lower bound for pure differential privacy](../differential-privacy/packing-lower-bound-for-pure-differential.md)

## Sources

- Cynthia Dwork and Aaron Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science, 2014, Theorem 8.8.
