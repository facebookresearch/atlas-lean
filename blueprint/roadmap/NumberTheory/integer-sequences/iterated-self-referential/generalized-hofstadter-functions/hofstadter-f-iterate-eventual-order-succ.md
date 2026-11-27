# Eventual order of iterates of consecutive Hofstadter functions

Let $k \ge 1$, let $F_k$ be
the generalized Hofstadter function, write $F_k^i$ for its $i$-fold iterate, let $\alpha > 0$ be
a root of $X^k + X - 1$, and let $\alpha' > 0$ be a root of $X^{k+1} + X - 1$. Then for all
sufficiently large $n$, $F_k(n) < F_{k+1}(n)$, $F_{k+1}^{k+1}(n) < F_k^k(n)$ and
$F_{k+1}^{k+2}(n) < F_k^{k+1}(n)$. Moreover, for every $j \ge 0$: if $j/(j+1) \le \alpha$ or
$j^2 \le k$, then $F_{k+1}^{k+j+1}(n) < F_k^{k+j}(n)$ for all sufficiently large $n$; and if
$\alpha' \le j/(j+1)$ or $k < j$, then $F_k^{k+j}(n) < F_{k+1}^{k+j+1}(n)$ for all sufficiently
large $n$.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Corollary 17 (`jis-2026-26.3.3-cor-17`).
