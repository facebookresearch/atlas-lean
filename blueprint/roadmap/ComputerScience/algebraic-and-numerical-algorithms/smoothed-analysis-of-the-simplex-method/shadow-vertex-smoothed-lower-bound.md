# Smoothed lower bound for the shadow vertex simplex method

For every $d > 5$ and $n = 4d - 13$ there are a two-dimensional subspace $W \subseteq \mathbb{R}^d$ and vectors $\bar a_1, \dots, \bar a_n \in \mathbb{R}^d$ with $\|\bar a_i\|_1 \le 1$ such that the following holds. Perturb the constraint normals only, by independent $a_i \sim \mathcal{N}_d(\bar a_i, \sigma^2 I)$ with $\sigma \le 1/(7200\,d\sqrt{\log n})$, keeping the right-hand side $\mathbf{1}$. Then with probability at least $1 - \binom{n}{d}^{-1}$,

$$
\mathrm{edges}\big(\mathrm{conv}(a_1, \dots, a_n) \cap W\big) \ge \Omega\!\left(\min\left(\frac{1}{\sqrt{d\sigma\sqrt{\log n}}},\; 2^d\right)\right).
$$

Consequently, for $d > 5$ and $\sigma \le 1/(360\,d\sqrt{\log(4d)})$ the polar-section smoothed shadow size of Huiberts–Lee–Zhang, equation (1), satisfies $S_{\mathrm{e}}(4d - 13, d, \sigma) = \Omega\big(\min(\sigma^{-1/2} d^{-1/2} \log^{-1/4} d,\, 2^d)\big)$, and since the smoothed complexity of the shadow vertex simplex algorithm is at least $S_{\mathrm{e}}(n, d, \sigma)/4$ (Huiberts–Lee–Zhang, Theorem 1.1), with the two objectives spanning $W$ chosen adversarially, it is at least of this order. This is the first nontrivial lower bound on the smoothed complexity of a simplex method.

## Proof sketch

The instances come from a variation of the extended formulation of the regular polygon: for $k = d - 5$, a polytope $P \subseteq \mathbb{R}^{k+5}$ with $n = 4k + 7$ constraints whose projection onto the plane $W$ of its first two coordinates is close to a regular polygon with $2^{k+1}$ vertices, with $\ell_\infty$-balls of comparable radii inside and around $P$. The polar $Q = \mathrm{conv}(\bar a_1, \dots, \bar a_n)$ of a shift of $P$ then lies between $\ell_1$-balls of comparable radii, and $Q \cap W$ approximates a disk. Any perturbation with $\|a_i - \bar a_i\|_1 \le \varepsilon < 1/180$ for all $i$ keeps $\Omega(\min(1/\sqrt\varepsilon, 2^d))$ edges of the section, and Gaussian concentration gives $\max_i \|a_i - \bar a_i\|_2 \le 4\sigma\sqrt{d\log n}$ with the stated probability.

## Depends on

- [Gaussian-smoothed linear programs and smoothed pivot complexity](gaussian-smoothed-linear-programs.md)
- [The shadow vertex pivot rule and the smoothed shadow bound](shadow-vertex-rule-and-shadow-bound.md)

## Proof depends on

- [Huiberts-Lee-Zhang smoothed shadow bound O(sigma^{-3/2} d^{13/4} log^{5/4} n)](huiberts-lee-zhang-upper-bound.md)
- [Shadow vertices are bounded by edges of the polar section](shadow-vertices-and-polar-section.md)

## Sources

- S. Huiberts, Y. T. Lee, X. Zhang, "Upper and Lower Bounds on the Smoothed Complexity of the Simplex Method", STOC (2023), TheoretiCS 4 (2025), arXiv:2211.11860, Theorems 1.1 and 1.3 and Section 6 (Theorems 6.1 and 6.2).
