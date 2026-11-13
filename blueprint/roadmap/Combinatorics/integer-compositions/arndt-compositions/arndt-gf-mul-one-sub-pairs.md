# Pair decomposition of the Arndt generating function

Let $S$ be a set of positive
integers and let $A_S(x, y)$ be the generating function of Arndt compositions with parts in $S$:
the formal power series in $x$ over $\mathbb{Z}[y]$ whose coefficient of $x^n y^k$ is the number
of Arndt compositions of $n$ with $k$ parts, all in $S$. Put $P_S(x) = \sum_{i \in S} x^i$ and
$Q_S(x) = \sum_{i, j \in S,\ j < i} x^{i+j}$. Then

$$A_S(x, y) \, (1 - y^2 Q_S(x)) = 1 + y P_S(x).$$

Equivalently, $A_S(x, y) = (1 + y P_S(x)) \sum_{m \ge 0} Q_S(x)^m y^{2m}$.

## Sources

- Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer Sequences 28 (2025), Article 25.3.6, Theorem 1 (`jis-2025-25.3.6-thm-1`).
