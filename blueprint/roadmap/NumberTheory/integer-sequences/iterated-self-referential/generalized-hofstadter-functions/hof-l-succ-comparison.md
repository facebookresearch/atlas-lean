# Comparing $L_k$ with $L_{k+1}$

Let $x_k[0]\,x_k[1] \cdots$ be the fixed point,
beginning with $k$, of the substitution $\tau_k$ that sends $k$ to $k\,1$ and every other
letter $i$ to $i + 1$, let $L_k(n)$ be the length of the word $\tau_k(x_k[0] \cdots x_k[n-1])$,
write $L_k^j$ for the $j$-fold iterate of $L_k$, and let $C_k^{(=k)}(n)$ be the number of
indices $i < n$ with $x_k[i] = k$. For all $k \ge 1$, $n \ge 1$ and $j$ with $0 \le j \le k$:
$L_{k+1}(n) \le L_k(n)$, $C_{k+1}^{(=k+1)}(n) \le C_k^{(=k)}(n)$, and
$L_k^j(n) < L_{k+1}^{j+1}(n)$.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Theorem 20 (`jis-2026-26.3.3-thm-20`).
