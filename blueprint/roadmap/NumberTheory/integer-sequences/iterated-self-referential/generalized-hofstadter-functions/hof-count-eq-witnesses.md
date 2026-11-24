# Witnesses that the letter counts of $x_k$ and $x_{k+1}$ are not ordered

For a natural
number $k$, let $\tau_k$ be the substitution sending the letter $k$ to $k\,1$ and every other
letter $a$ to $a + 1$, let $x_k = x_k[0]\,x_k[1] \cdots$ be its fixed point beginning with $k$,
let $C_k^{(=i)}(n)$ be the number of indices $j < n$ with $x_k[j] = i$, let $L_k(n)$ be the
length of the word $\tau_k(x_k[0] \cdots x_k[n-1])$, and write $L_k^j$ for the $j$-fold iterate
of $L_k$. For all natural numbers $i$ and $k$ with $3 \le i < k$, put $n = i + L_k^{2k+2}(1)$
and $m = i + L_{k+1}^{k+i}(1)$. Then $C_k^{(=i)}(n) < C_{k+1}^{(=i)}(n)$ and
$C_{k+1}^{(=i)}(m) < C_k^{(=i)}(m)$, so for these letters $i$ the letter counts of $x_k$ and
$x_{k+1}$ are not ordered.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Proposition 27 (`jis-2026-26.3.3-prop-27`).
