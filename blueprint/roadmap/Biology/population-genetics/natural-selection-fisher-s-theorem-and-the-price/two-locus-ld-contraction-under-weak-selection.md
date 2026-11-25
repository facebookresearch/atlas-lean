# A uniform weak-selection bound on two-locus linkage disequilibrium

Use the [diploid viability-selection/meiosis map](two-locus-viability-selection-with-recombination.md),
including symmetric viabilities and equality of the double-heterozygote
viabilities. Let $w_{ij}=1+\varepsilon a_{ij}$ with $|a_{ij}|\le1$,
$0\le\varepsilon\le1/2$, and $r\in[0,1/2]$. For every simplex state,

$$|D'-(1-r)D|\le6\varepsilon.$$

If these hypotheses hold at every generation with the same uniform
$\varepsilon$ and $r_t\ge r_0>0$, then

$$|D_t|\le(1-r_0)^t|D_0|
+\frac{6\varepsilon}{r_0}\bigl(1-(1-r_0)^t\bigr)
\le(1-r_0)^t|D_0|+\frac{6\varepsilon}{r_0}.$$

The constant does not depend on the state or the permitted fitness
array. The assertion is order $\varepsilon$ only for a fixed positive
lower recombination bound; it is not a quasi-linkage-equilibrium expansion.

## Depends on

- [Diploid two-locus map](two-locus-viability-selection-with-recombination.md)

## Proof depends on

- [Neutral recombination identity](../linkage-disequilibrium-and-haldane-s-map-functio/recombine-eq-sub.md)

## Expansion

Put $y_i=x_i-e_irD$. Then
$x_i'-y_i=[x_i(w_i-\bar w)-e_irD(w_{14}-\bar w)]/\bar w$.
Both fitness differences are bounded by $2\varepsilon$,
$\bar w\ge1-\varepsilon$, $|D|\le1/4$ and $r|D|\le1/8$.
Thus $\sum_i|x_i'-y_i|\le3\varepsilon/(1-\varepsilon)\le6\varepsilon$.
Both vectors lie on the simplex, and the bilinear determinant obeys
$|D(x')-D(y)|\le\sum_i|x_i'-y_i|$.
Direct expansion gives $D(y)=(1-r)D(x)$, proving the first inequality.
The second follows by iterating
$|D_{t+1}|\le(1-r_0)|D_t|+6\varepsilon$ and summing the finite
geometric series. If $\varepsilon=0$ the neutral contraction is exact.
Stronger QLE statements, a slow-manifold formula and positive-recombination
interference results remain separate objectives, not consequences of this bound.

## Sources

- T. Nagylaki, "The evolution of multilocus systems under weak selection", Genetics 134 (1993), 627–647, <https://doi.org/10.1093/genetics/134.2.627>. The bound is derived above.
