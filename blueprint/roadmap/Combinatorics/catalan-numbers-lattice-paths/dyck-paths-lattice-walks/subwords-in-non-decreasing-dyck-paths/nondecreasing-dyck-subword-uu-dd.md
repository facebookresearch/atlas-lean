# Generating functions and closed form for the subwords $UU$ and $DD$ in non-decreasing Dyck paths

**Generating functions and closed form for the subwords $UU$ and $DD$ in non-decreasing Dyck
paths.** Let $w$ be $UU$ or $DD$. For $n \ge 0$ let $\mathcal{D}_n$ be the set of non-decreasing
Dyck paths of semilength $n$, let $\#_w(P)$ be the number of occurrences of the subword $w$ in a
path $P$, and let $d_w(n) = \sum_{P \in \mathcal{D}_n} \#_w(P)$. Let
$F_w(x, y) = \sum_{n \ge 1} \sum_{P \in \mathcal{D}_n} y^{\#_w(P)} x^n$, a power series in $x$
with coefficients in $\mathbb{Z}[y]$, and $D_w(x) = \sum_{n \ge 0} d_w(n) x^n$ in
$\mathbb{Z}[[x]]$. Then $(1 - x - 2xy + x^2 y^2) F_w(x, y) = x (1 - xy)$ and
$(1 - 3x + x^2)^2 D_w(x) = x^2 (1 - x + x^2)$, and for every $n \ge 1$,

$$10\, d_w(n) = (7 - 10n) F_{2n} + (6n - 5) L_{2n},$$

where $F_k$ and $L_k$ are the Fibonacci and Lucas numbers ($F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = 1$).

## Sources

- Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 3 (`jis-2025-25.1.6-thm-3`).
