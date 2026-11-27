# Generalized Hofstadter function as a letter count

Let $k > 1$ and $n \ge 0$. Let $F_k$ be
the generalized Hofstadter function, defined by $F_k(0) = 0$ and $F_k(m) = m - F_k^k(m - 1)$ for
$m \ge 1$, where $F_k^k$ is the $k$-fold iterate of $F_k$. Let $x_k[0]\,x_k[1] \cdots$ be the
fixed point, beginning with $k$, of the substitution $\tau_k$ that sends $k$ to $k\,1$ and every
other letter $i$ to $i + 1$, and for a property $P$ of letters let $C_k^{(P)}(n)$ be the number
of indices $0 \le i < n$ with $P(x_k[i])$. Then $F_k(n) = n - C_k^{(=1)}(n)$ and
$F_k(n) = C_k^{(\ne 1)}(n)$. Moreover, $F_k(n+1) = F_k(n)$ if and only if $x_k[n] = 1$, and
$F_k(n+1) = F_k(n) + 1$ whenever $x_k[n] \ne 1$.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Proposition 10 (`jis-2026-26.3.3-prop-10`).
