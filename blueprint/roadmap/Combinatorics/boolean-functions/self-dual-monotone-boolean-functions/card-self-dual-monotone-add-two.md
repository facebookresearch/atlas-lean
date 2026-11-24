# Counting self-dual monotone functions on $n + 2$ variables

Let $n \ge 0$ and let
$\lambda_{n+2}$ be the number of self-dual monotone Boolean functions on $n + 2$ variables. For
a monotone Boolean function $b$ on $n$ variables let $r(b)$ be the number of monotone Boolean
functions $z$ on $n$ variables with $b \lor b^* \le z$, where $b^*$ is the dual of $b$, $\lor$
is pointwise disjunction and functions are ordered pointwise. Then $\lambda_{n+2}$ is the sum
of $r(b)$ over all monotone Boolean functions $b$ on $n$ variables. Moreover, for a permutation
$\pi$ of the $n$ coordinates write $b^\pi$ for the function $x \mapsto b(x \circ \pi)$, and let
$R$ be any finite set of monotone Boolean functions on $n$ variables such that for every
monotone $f$ there is exactly one $b \in R$ with $f = b^\pi$ for some permutation $\pi$. Then
$\lambda_{n+2} = \sum_{b \in R} \gamma(b) \, r(b)$, where $\gamma(b)$ is the number of distinct
functions $b^\pi$ as $\pi$ ranges over all permutations.

## Sources

- Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Theorem 10 (`jis-2025-25.6.5-thm-10`).
