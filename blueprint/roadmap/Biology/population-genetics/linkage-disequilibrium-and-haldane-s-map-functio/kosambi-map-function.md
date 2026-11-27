# Kosambi's map function

Kosambi's map function $r_K(d) = \tfrac12 \tanh(2d)$ is the unique solution on $d \ge 0$ of

$$\frac{dr}{dd} = 1 - 4 r^2, \qquad r(0) = 0 .$$

It satisfies $0 \le r_K(d) < \tfrac12$, $r_K(d) \to \tfrac12$ as $d \to \infty$, and as $d \to 0^+$

$$\frac{r_K(d) - d}{d^3} \to -\frac43, \qquad \text{whereas} \qquad \frac{r_H(d) - d}{d^2} \to -1$$

for [Haldane's map function](haldane.md)
$r_H(d) = (1 - e^{-2d})/2$, the map function without interference. Thus the two agree to first order and
differ at second order, where Haldane's has a $-d^2$ term and Kosambi's none.

The function is defined analytically by the differential equation; no stochastic model of crossing over is
asserted. Indeed $r_K' = \operatorname{sech}^2(2d) = 1 - \tanh^2(2d) = 1 - 4 r_K^2$, uniqueness holds because
$r \mapsto 1 - 4r^2$ is locally Lipschitz, and the expansions follow from $\tanh y = y - y^3/3 + O(y^5)$ and
$e^{-2d} = 1 - 2d + 2d^2 + O(d^3)$.

## Proof depends on

- [Haldane's map function](haldane.md)

## Sources

- D. D. Kosambi, "The estimation of map distances from recombination values", Annals of Eugenics 12 (1943), 172–175, <https://doi.org/10.1111/j.1469-1809.1943.tb02321.x> (background; the statements above are derived here).
