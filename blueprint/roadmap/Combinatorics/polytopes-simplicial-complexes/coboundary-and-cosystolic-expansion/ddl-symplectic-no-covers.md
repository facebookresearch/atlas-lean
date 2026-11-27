# Dikstein–Dinur–Lubotzky: bounded-degree complexes without small connected covers

For every $m \ge 2$, every $g \ge 100\sqrt{m \log m}$ and every prime $p$, there is an infinite family of connected finite quotients $X$ of the affine Bruhat–Tits building $\tilde C_g(\mathbb{Q}_p)$ of $\mathrm{Sp}(2g, \mathbb{Q}_p)$ (bounded-degree complexes, the degree depending only on $g$ and $p$) such that no $X$ has a connected $m'$-sheeted cover for any $1 < m' \le m$. Moreover, for every integer $d \ge 1$ there is $p_0(d)$ such that for every prime $p > p_0(d)$ and every $g \ge \max(d^5, 3d + 2)$, every quotient of $\tilde C_g(\mathbb{Q}_p)$ has $(\exp(-O(\sqrt{d})), d)$-swap cocycle expansion in the sense of the swap-complex page (the source writes this as a $(d, \exp(-O(\sqrt{d})))$-swap cocycle expander, with the parameters in the other order; the bound $g \ge 3d + 2$ makes $F^{d+1}X$ defined, and is implied by $g \ge d^5$ once $d \ge 2$).

## Proof sketch

Connected $m'$-sheeted covers of a quotient $\Gamma \backslash \tilde C_g$ correspond to subgroups of index $m'$ of its fundamental group; for suitable arithmetic lattices $\Gamma$ in $\mathrm{Sp}(2g)$, the congruence subgroup property shows that these lattices have no subgroups of small index, so the quotients have no small connected covers. Swap cocycle expansion is reduced via a local-to-global argument to coboundary expansion of links, which are spherical symplectic buildings handled by cone constructions.

## Depends on

- [Connected covers of a simplicial complex](covers-of-complexes.md)
- [The swap complex (faces complex) of a high-dimensional expander](swap-complex.md)
- [Cosystolic expansion and cosystolic distance](cosystolic-expansion.md)

## Proof depends on

- [Dikstein–Dinur: cosystolic expansion without dependence on dimension or degree](dikstein-dinur-degree-free.md)

## Sources

- Y. Dikstein, I. Dinur, A. Lubotzky, "Low acceptance agreement tests via bounded-degree symplectic HDXs", FOCS (2024), arXiv:2402.01078 (Theorems 1.2 and 1.3).
