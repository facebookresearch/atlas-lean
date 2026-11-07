# Generating functions and closed form for the subword $UDU$ in non-decreasing Dyck paths

For $n \ge 0$ let $\mathcal{D}_n$ be the set of non-decreasing Dyck paths of semilength $n$, let
$\#_{UDU}(P)$ be the number of occurrences of the subword $UDU$ in a path $P$, and let
$d_{UDU}(n) = \sum_{P \in \mathcal{D}_n} \#_{UDU}(P)$. Let
$F_{UDU}(x, y) = \sum_{n \ge 1} \sum_{P \in \mathcal{D}_n} y^{\#_{UDU}(P)} x^n$, a power series
in $x$ with coefficients in $\mathbb{Z}[y]$, and $D_{UDU}(x) = \sum_{n \ge 0} d_{UDU}(n) x^n$ in
$\mathbb{Z}[[x]]$. Then $(1 - x(2 + y) + x^2 y) F_{UDU}(x, y) = (1 - x) x$ and
$(1 - 3x + x^2)^2 D_{UDU}(x) = x^2 (1 - x)^2$, and for every $n \ge 1$,

$$10\, d_{UDU}(n) = (11 - 5n) F_{2n} + (3n - 5) L_{2n},$$

where $F_k$ and $L_k$ are the Fibonacci and Lucas numbers ($F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = 1$).

## Sources

- Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 5 (`jis-2025-25.1.6-thm-5`).
