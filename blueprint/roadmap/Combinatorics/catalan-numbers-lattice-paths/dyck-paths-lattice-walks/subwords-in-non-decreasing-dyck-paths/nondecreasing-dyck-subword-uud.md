# Generating functions and closed form for the subword $UUD$ in non-decreasing Dyck paths

For $n \ge 0$ let $\mathcal{D}_n$ be the set of non-decreasing Dyck paths of semilength $n$, let
$\#_{UUD}(P)$ be the number of occurrences of the subword $UUD$ in a path $P$, and let
$d_{UUD}(n) = \sum_{P \in \mathcal{D}_n} \#_{UUD}(P)$. Let
$F_{UUD}(x, y) = \sum_{n \ge 1} \sum_{P \in \mathcal{D}_n} y^{\#_{UUD}(P)} x^n$, a power series
in $x$ with coefficients in $\mathbb{Z}[y]$, and $D_{UUD}(x) = \sum_{n \ge 0} d_{UUD}(n) x^n$ in
$\mathbb{Z}[[x]]$. Then

$$(1 - 3x + x^2 (3 - 2y) - x^3 (1 - y)) F_{UUD}(x, y) = (1 - x) x (1 - x(1 - y))$$

and $(1 - 3x + x^2)^2 D_{UUD}(x) = (1 - x)^2 x^2$, and for every $n \ge 3$,

$$10\, d_{UUD}(n) = (11 - 5n) F_{2n} + (3n - 5) L_{2n},$$

where $F_k$ and $L_k$ are the Fibonacci and Lucas numbers ($F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = 1$).

## Sources

- Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 11 (`jis-2025-25.1.6-thm-11`).
