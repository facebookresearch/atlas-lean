# Generating functions and closed form for the subword $UD$ in non-decreasing Dyck paths

For $n \ge 0$ let $\mathcal{D}_n$ be the set of non-decreasing Dyck paths of semilength $n$, let
$\#_{UD}(P)$ be the number of occurrences of the subword $UD$ in a path $P$, and let
$d_{UD}(n) = \sum_{P \in \mathcal{D}_n} \#_{UD}(P)$. Let
$F_{UD}(x, y) = \sum_{n \ge 1} \sum_{P \in \mathcal{D}_n} y^{\#_{UD}(P)} x^n$, a power series in
$x$ with coefficients in $\mathbb{Z}[y]$, and $D_{UD}(x) = \sum_{n \ge 0} d_{UD}(n) x^n$ in
$\mathbb{Z}[[x]]$. Then $(1 - 2x + x^2 - xy) F_{UD}(x, y) = (1 - x) x y$ and
$(1 - 3x + x^2)^2 D_{UD}(x) = x (1 - x)^3$, and for every $n \ge 1$,

$$10\, d_{UD}(n) = (5n - 7) F_{2n} - (n - 5) L_{2n},$$

where $F_k$ and $L_k$ are the Fibonacci and Lucas numbers ($F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = 1$).

## Sources

- Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 1 (`jis-2025-25.1.6-thm-1`).
