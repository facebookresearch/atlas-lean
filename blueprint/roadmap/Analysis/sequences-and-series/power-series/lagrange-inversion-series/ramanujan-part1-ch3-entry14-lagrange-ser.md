# Ramanujan's Lagrange series

Let $p > 0$ and $q > 0$ be real numbers with $p \ne q$, and
let $a$ be a complex number with $|a| \le p^{-p/q} |p - q|^{(p - q)/q}$. Then there is a complex
number $L$ with $a q e^{p L} - e^{q L} + 1 = 0$ such that, for every real number $n$, the series

$$1 + \sum_{k=1}^{\infty} \frac{n a^k}{k!} \prod_{j=1}^{k-1} (n + k p - j q)$$

converges unconditionally to $e^{n L}$.

Proof: The argument uses the Hagen--Rothe convolution, a Stirling-type coefficient bound uniform
through the boundary circle, and a continuous exponential lift.

## Sources

- Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 14, formulas (14.1)--(14.5), printed pp. 70--71 / PDF pp. 80--81; attribution on printed p. 72 / PDF p. 82.
