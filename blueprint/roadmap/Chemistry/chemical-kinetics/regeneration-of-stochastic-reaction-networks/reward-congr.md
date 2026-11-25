# Rewards up to step $m \le n$ depend only on the first $n$ steps

Let $S$ be a set, $q, g : S \to \mathbb{R}$, $x \in S$ and $n \in \mathbb{N}$, and let
$\omega, \omega'$ be step sequences that agree in their first $n$ steps, $\omega'_i = \omega_i$ for
every $i < n$. Then their [rewards](reward.md) $R_m = \sum_{i < m} g(Y_i)\, E_i / q(Y_i)$ from
$x$ (with $a / 0 = 0$) agree up to step $n$:

$$R_m(x, \omega) = R_m(x, \omega') \qquad \text{for every } m \le n .$$
