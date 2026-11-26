# Iterated Hofstadter functions as letter counts

Let $k \ge 1$ and $n \ge 0$. Let $F_k$ be
the generalized Hofstadter function and $F_k^j$ its $j$-fold iterate, let $x_k[0]\,x_k[1] \cdots$
be the fixed point, beginning with $k$, of the substitution $\tau_k$ that sends $k$ to $k\,1$ and
every other letter $i$ to $i + 1$, and for a property $P$ of letters let $C_k^{(P)}(m)$ be the
number of indices $0 \le i < m$ with $P(x_k[i])$. Then $F_k^{k-1}(n) = C_k^{(=k)}(n)$;
$F_k^j(n) = C_k^{(>j)}(n)$ for every $0 \le j < k$; and $F_k^{k+i-1}(n) = C_k^{(=i)}(n+i)$ for
every $1 \le i < k$.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Proposition 8 (`jis-2026-26.3.3-prop-8`).
