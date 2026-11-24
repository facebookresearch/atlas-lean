# The Markov property of the form of a sub-Markovian generator

Let $S$ be a finite set, $m : S \to \mathbb{R}$ with $m \ge 0$, and $Q$ a real $S \times S$ matrix
with $Q(x, y) \ge 0$ for $x \ne y$ and nonnegative [killing rate](killing-rate.md)
$k(x) = -\sum_y Q(x, y) \ge 0$. Then the [unit contraction](unit-contraction.md)
$\bar u = (0 \vee u) \wedge 1$ does not increase the energy of the [form](form.md) of $(m, Q)$:

$$\mathcal E(\bar u, \bar u) \le \mathcal E(u, u) \qquad \text{for every } u : S \to \mathbb{R} .$$

This is condition (E.4)′ of Fukushima, Oshima and Takeda; their Example 1.2.5 shows that the form
(1.2.27) is a Dirichlet form.

## Sources

- M. Fukushima, Y. Oshima and M. Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd revised and extended ed., de Gruyter Studies in Mathematics 19, de Gruyter, 2011, Section 1.1, condition (E.4)′, and Example 1.2.5.
