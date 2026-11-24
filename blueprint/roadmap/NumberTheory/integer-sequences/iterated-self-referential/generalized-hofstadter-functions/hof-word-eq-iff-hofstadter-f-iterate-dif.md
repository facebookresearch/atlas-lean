# The letters of $x_k$ from the increments of the iterates of $F_k$

Let $k \ge 1$, let $F_k$
be the generalized Hofstadter function with $j$-th iterate $F_k^j$ ($F_k^0$ the identity), and
let $x_k = x_k[0]\,x_k[1] \cdots$ be the fixed point of the substitution $\tau_k$
($k \mapsto k\,1$, $i \mapsto i + 1$ for $i \ne k$). For every natural number $n$: for each $j$
with $1 \le j < k$, $x_k[n] = j$ if and only if $F_k^{j-1}(n+1) = F_k^{j-1}(n) + 1$ and
$F_k^j(n+1) = F_k^j(n)$; and $x_k[n] = k$ if and only if $F_k^{k-1}(n+1) = F_k^{k-1}(n) + 1$.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Proposition 11 (`jis-2026-26.3.3-prop-11`).
