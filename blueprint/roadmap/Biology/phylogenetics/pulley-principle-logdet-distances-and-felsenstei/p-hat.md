# Empirical p-distance

For an alignment $\mathrm{seq}$ (with $\mathrm{seq}(i, x)$ the base of taxon $x$ at site $i$), a natural number $n$ and taxa $x, y$, the empirical p-distance is

$$\hat p_n(x, y) = \frac1n\, \#\{i < n : \mathrm{seq}(i, x) \ne \mathrm{seq}(i, y)\},$$

with the convention $0^{-1} = 0$.
