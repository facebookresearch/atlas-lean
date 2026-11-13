# Shafarevich's relation-rank bound

Let $F$ be a number field, let $p$ be an odd prime,
and let $G = \mathrm{Gal}(F^{\mathrm{un},p}/F)$ be the Galois group of the maximal unramified
pro-$p$ extension of $F$. Write $d(G)$ for the generator rank and $r(G)$ for the relation rank
of $G$, $r_1$ and $r_2$ for the numbers of real and complex places of $F$, and $\delta$ for $1$
if $F$ contains a primitive $p$-th root of unity and $0$ otherwise. Then the continuous
cohomology group $H^2(G, \mathbb{F}_p)$ with trivial coefficients is finite-dimensional over
$\mathbb{F}_p$, and

$$r(G) \le d(G) + (r_1 + r_2 - 1) + \delta.$$

## Sources

- D. C. Mayer, *New number fields with known p-class tower*, Tatra Mt. Math. Publ. 64 (2015), 21–57 (Theorem 5.1, S=∅; arXiv:1510.00565); H. Koch, *Galois Theory of p-Extensions*, Springer 2002 (Theorems 11.5 and 11.8); I. R. Shafarevich, *Extensions with prescribed ramification points* (1963). Lean hypothesis: https://github.com/logical-intelligence/erdos-unit-distance (Hyp_ShafarevichRelationRankBound). Problem `shafarevich_relation_rank_bound` of the lean-eval benchmark.
