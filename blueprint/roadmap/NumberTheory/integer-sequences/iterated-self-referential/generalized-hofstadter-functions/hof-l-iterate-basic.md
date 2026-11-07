# Basic properties of the iterates of $L_k$

Let $k \ge 1$, let $x_k$ be the fixed point of
the substitution $\tau_k$, with letters $x_k[0], x_k[1], \dots$ and prefixes
$x_k[0:n) = x_k[0] \cdots x_k[n-1]$, let $L_k(n) = |\tau_k(x_k[0:n))|$, and write $f^j$ for the
$j$-fold iterate of a map $f$ (so $f^0$ is the identity). Then for every $j \ge 0$:
(1) $L_k^j(n) = |\tau_k^j(x_k[0:n))|$ for every $n$;
(2) $L_k^j(0) = 0$, and $L_k^j(n+1) = L_k^j(n) + |\tau_k^j(x_k[n])|$ for every $n$;
(3) $L_k^j(1) = j + 1$ if $j \le k$, and $L_k^j(1) = L_k^{j-1}(1) + L_k^{j-k}(1)$ if $j \ge k$;
(4) $n \mapsto L_k^j(n)$ is strictly increasing;
(5) $L_k^j(n) \ge n$ for every $n$, with equality if and only if $j = 0$ or $n = 0$;
(6) for every $n \ge 1$, the sequence $i \mapsto L_k^i(n)$ is strictly increasing.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Proposition 4 (`jis-2026-26.3.3-prop-4`).
