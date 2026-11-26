# Galois insertion between iterated Hofstadter functions

Let $k \ge 1$ and $j \ge 0$. Let
$F_k$ be the generalized Hofstadter function, let $x_k[0]\,x_k[1] \cdots$ be the fixed point,
beginning with $k$, of the substitution $\tau_k$ that sends $k$ to $k\,1$ and every other letter
$i$ to $i + 1$, let $L_k(m)$ be the length of the word $\tau_k(x_k[0] \cdots x_k[m-1])$, and
write $f^j$ for the $j$-fold iterate of a function $f$. Then for all $n, m \ge 0$,
$F_k^j(n) \le m$ if and only if $n \le L_k^j(m)$, so $F_k^j$ and $L_k^j$ form a Galois
connection; and $F_k^j(L_k^j(m)) = m$ for every $m \ge 0$, so it is a Galois insertion.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Corollary 7 (`jis-2026-26.3.3-cor-7`).
