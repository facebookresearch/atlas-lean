# Balanced minimum-evolution length

For an [unrooted binary tree](utree.md) $T$ and a real dissimilarity $d$ on $X$, the balanced minimum-evolution length is

$$\mathrm{BME}(T, d) = \sum_{(x, y, \ell, \tau)} 2^{1 - \tau}\, \frac{d(x, y) + d(y, x)}{2},$$

the sum over the [leaf pairs](pairs-2.md) of $T$ (Desper and Gascuel 2002). It depends on $T$ only through the edge counts $\tau$.

## Sources

- R. Desper and O. Gascuel, *Fast and accurate phylogeny reconstruction algorithms based on the minimum-evolution principle*, J. Comput. Biol. 9 (2002), 687–705.
