# De's lower bound for pure privacy over a small universe

Let $k, d, n \in \mathbb{N}$ and $\varepsilon \in (0, 1/40]$ with $n \ge \min(k, d)/\varepsilon$, and take databases to be histograms $x \in \mathbb{N}^d$ over a universe of $d$ items, neighbouring when $\|x - y\|_1 \le 1$ (so neighbours may differ in size by one row). There is a query $F : \mathbb{N}^{d} \to \mathbb{R}^{k}$ with sensitivity at most $1$ in each coordinate with respect to this $\ell_1$ distance such that every $(\varepsilon, 0)$-differentially private mechanism adds noise of $L_\infty$ norm $\Omega(\min(k, d)/\varepsilon)$ with probability at least $1/2$ on some database of weight $\|x\|_1$ at most $n$. The coordinates of $F$ are not counting queries.

## Proof sketch

With $\ell = \min(k, d)$, choose $2^s$ histograms $x_1, \dots, x_{2^s}$, $s = \ell/400$, each of weight at most $w = \ell/(1280\varepsilon)$ and pairwise at $\ell_1$ distance at least $w/10$. The map $L_S$ whose $i$-th coordinate is $\max(w/30 - \|x_i - z\|_1, 0)$ is $1$-Lipschitz in $\ell_1$ (Dwork and Roth, Claim 8.9), and $F$ takes the inner products of $L_S$ with $k$ independent uniform $\pm 1$ vectors; by a Chernoff and union bound some choice separates every pair $x_h, x_j$ by at least $w/15$ in a tenth of the coordinates. Accurate answers would then place most mass of the mechanism in disjoint regions, contradicting the pure packing bound.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Neighbouring histograms](../differential-privacy/histogram-adj.md)

## Proof depends on

- [Packing lower bound for approximate differential privacy](packing-bound-approximate-dp.md)
- [Packing lower bound for pure differential privacy](../differential-privacy/packing-lower-bound-for-pure-differential.md)

## Sources

- Cynthia Dwork and Aaron Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science, 2014, Theorem 8.8.
