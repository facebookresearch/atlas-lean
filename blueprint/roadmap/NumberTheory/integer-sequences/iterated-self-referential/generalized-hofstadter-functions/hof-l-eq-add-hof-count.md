# The image length $L_k$ as a letter count

Let $k \ge 1$. Let $F_k$ be the generalized
Hofstadter function and $F_k^{k-1}$ its $(k-1)$-fold iterate, let $x_k[0]\,x_k[1] \cdots$ be the
fixed point, beginning with $k$, of the substitution $\tau_k$ that sends $k$ to $k\,1$ and every
other letter $i$ to $i + 1$, let $L_k(n)$ be the length of the word
$\tau_k(x_k[0] \cdots x_k[n-1])$, and let $C_k^{(=k)}(n)$ be the number of indices $0 \le i < n$
with $x_k[i] = k$. Then for every natural number $n$, $L_k(n) = n + C_k^{(=k)}(n)$ and
$L_k(n) = n + F_k^{k-1}(n)$.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Proposition 9 (`jis-2026-26.3.3-prop-9`).
