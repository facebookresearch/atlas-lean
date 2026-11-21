# Deterministic chaining

Let $f : \mathbb{R} \to \mathbb{R}$, $\gamma > 0$ and $D > 0$, and suppose that every adjacent dyadic increment
at level $m$ is at most $D\, 2^{-m\gamma}$:

$$\Bigl| f\Bigl(\frac{k + 1}{2^m}\Bigr) - f\Bigl(\frac{k}{2^m}\Bigr) \Bigr| \le D\, 2^{-m\gamma} \qquad \text{for all } m \in \mathbb{N},\ 0 \le k < 2^m .$$

Then for all [dyadic rationals](dyadic-rationals.md) $q, r \in [0, 1]$,

$$|f(q) - f(r)| \le D \Bigl( 4 + \frac{2 \cdot 2^{-\gamma}}{1 - 2^{-\gamma}} \Bigr) |q - r|^\gamma .$$
