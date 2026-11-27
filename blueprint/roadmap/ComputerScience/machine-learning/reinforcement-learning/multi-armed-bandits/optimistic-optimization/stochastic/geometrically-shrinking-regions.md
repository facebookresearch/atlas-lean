# Geometrically shrinking regions

Let $(P_{h,i})$ be a [tree of coverings](tree-of-coverings.md) of a measurable space $\mathcal X$ and $\ell$ a
[dissimilarity](dissimilarity.md) on $\mathcal X$, and let $\nu_1 > 0$, $0 < \rho < 1$ and $\nu_2 > 0$. The regions
*shrink geometrically* with constants $\nu_1$, $\rho$ and $\nu_2$ if, for every depth $h \ge 0$:

1. $\ell(x, y) \le \nu_1 \rho^h$ for all $x, y \in P_{h,i}$, for every $1 \le i \le 2^h$;
2. for every $1 \le i \le 2^h$ there is a point $x^\circ_{h,i} \in P_{h,i}$ with
   $B_{h,i} = B(x^\circ_{h,i}, \nu_2 \rho^h) \subseteq P_{h,i}$;
3. the balls $B_{h,i}$, $1 \le i \le 2^h$, are pairwise disjoint.

Then every region is nonempty, by 2, and 1 says that $\operatorname{diam}(P_{h,i}) \le \nu_1 \rho^h$. The diameter here
is taken over all pairs of points of the region, whereas the deterministic case
[bounds the diameters](../bounded-diameters.md) from the center only; and the balls of a given depth are assumed
disjoint, as the regions may overlap. When $\ell$ is a semi-metric and the regions are the cells of a hierarchical
partition whose centers are the points $x^\circ_{h,i}$, condition 2 says that the cells are
[well shaped](../well-shaped-cells.md) for $\delta(h) = \nu_1\rho^h$ with constant $\nu_2/\nu_1$, and condition 3 holds
as the cells of a depth are disjoint. The powers $\rho^h$ are read as real powers.

For example (the source's Example 2 with $D = 1$), the regions obtained from $[0, 1]$ by halving each region in the
middle, with $\ell(x, y) = \lvert x - y \rvert$, shrink geometrically with $\nu_1 = 2$, $\rho = 1/2$ and $\nu_2 = 1/2$.

## Sources

- S. Bubeck, R. Munos, G. Stoltz and Cs. Szepesvári, *X-armed bandits*, Journal of Machine Learning Research 12
  (2011), 1655–1695, <https://jmlr.org/papers/v12/bubeck11a.html>, Section 4.1, Assumption A1 and Examples 1–2.

## Depends on

- [Tree of coverings](tree-of-coverings.md)
- [Dissimilarity](dissimilarity.md)
- [Real power of a real number](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow.md)
