# Generating functions and closed form for the subword $UDD$ in non-decreasing Dyck paths

For $n \ge 0$ let $\mathcal{D}_n$ be the set of non-decreasing Dyck paths of semilength $n$, let
$\#_{UDD}(P)$ be the number of occurrences of the subword $UDD$ in a path $P$, and let
$d_{UDD}(n) = \sum_{P \in \mathcal{D}_n} \#_{UDD}(P)$. Let
$F_{UDD}(x, y) = \sum_{n \ge 1} \sum_{P \in \mathcal{D}_n} y^{\#_{UDD}(P)} x^n$, a power series
in $x$ with coefficients in $\mathbb{Z}[y]$, and $D_{UDD}(x) = \sum_{n \ge 0} d_{UDD}(n) x^n$ in
$\mathbb{Z}[[x]]$. Then

$$(1 - 3x + x^2 (2 - y)) (1 - 2x + x^2 (1 - y)) F_{UDD}(x, y) = (1 - x)(1 - 2x)(1 - x(1 - y)) x$$

and

$$(1 - 2x)(1 - 3x + x^2)^2 D_{UDD}(x) = (1 - x)(1 - 3x + 2x^2 - x^3) x^2,$$

and for every $n \ge 2$,

$$5\, d_{UDD}(n) = (5n - 9) F_{2n} + (5 - 2n) L_{2n} - 5 \cdot 2^{n-2},$$

where $F_k$ and $L_k$ are the Fibonacci and Lucas numbers ($F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = 1$).

## Sources

- Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 6 (`jis-2025-25.1.6-thm-6`).
