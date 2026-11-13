# Half-turn fixed points on the rectangular torus, $n$ odd and $m$ even

Let $T$ be a
finite set of tile designs, $\sigma$ a permutation of $T$ with $\sigma^2 = 1$, $n$ a positive
odd integer and $m$ a positive even integer. For a shift
$(a, b) \in \mathbb{Z}/n \times \mathbb{Z}/m$, count the maps
$F : \mathbb{Z}/n \times \mathbb{Z}/m \to T$ with $F(-1-x-a, -1-y-b) = \sigma(F(x, y))$ for all
cells $(x, y)$, and let $\mathrm{fxpt}$ be the sum of these counts over all $nm$ shifts (the
torus fixed-point count of the half-turn $r^2$). Write $t_{\mathrm{id}} = |T|$ and let
$t_{r^2}$ be the number of designs $d \in T$ with $\sigma(d) = d$. Then

$$2\,\mathrm{fxpt} = nm\left(t_{\mathrm{id}}^{nm/2} + t_{\mathrm{id}}^{nm/2-1}\,t_{r^2}^2\right).$$

## Sources

- Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*, Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 35.
