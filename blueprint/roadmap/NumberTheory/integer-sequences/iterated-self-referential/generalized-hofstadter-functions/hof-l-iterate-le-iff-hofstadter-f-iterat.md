# Order of iterates of $L_k$ against order of iterates of $F_k$

Let $F_k$ be the
generalized Hofstadter function, let $x_k[0]\,x_k[1] \cdots$ be the fixed point, beginning with
$k$, of the substitution $\tau_k$ that sends $k$ to $k\,1$ and every other letter $i$ to
$i + 1$, let $L_k(n)$ be the length of the word $\tau_k(x_k[0] \cdots x_k[n-1])$, and write
$f^j$ for the $j$-fold iterate of a function $f$. Let $k, k' \ge 1$ and $j, j' \ge 0$. Then
$L_k^j(n) \le L_{k'}^{j'}(n)$ for every $n$ if and only if $F_{k'}^{j'}(n) \le F_k^j(n)$ for
every $n$. Moreover, for every natural number $n$:
(a) $L_k^j(n) \le L_{k'}^{j'}(n)$ if and only if $F_{k'}^{j'}(m) \le F_k^j(m)$ for
$m = L_k^j(n)$;
(b) $L_k^j(n) < L_{k'}^{j'}(n)$ if and only if $F_{k'}^{j'}(m) < F_k^j(m)$ for
$m = L_{k'}^{j'}(n)$;
(c) if $L_k^j(m) \le L_{k'}^{j'}(m)$ for $m = F_k^j(n)$, then $F_{k'}^{j'}(n) \le F_k^j(n)$;
(d) if $F_k^j(n) < F_{k'}^{j'}(n)$, then $L_{k'}^{j'}(m) < L_k^j(m)$ for $m = F_k^j(n)$.

In (d) the paper prints $m = F_{k'}^{j'}(n)$; its proof derives (d) as the contrapositive of
(c), which gives $m = F_k^j(n)$. The printed form fails for $k = 1$, $j = 1$, $k' = 4$,
$j' = 2$ and $n = 8$: $F_1(8) = 4 < F_4^2(8) = 5$, but $L_4^2(5) = L_1(5) = 10$.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Proposition 19 (`jis-2026-26.3.3-prop-19`).
