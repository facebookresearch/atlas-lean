# Recurrences for alternating binomial power sums

Let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (kx + y)^\ell$. For all complex numbers
$x, y$ and natural numbers $\ell, m$ (sums over an empty range are $0$, and $m - 1$ means $0$ when
$m = 0$):
(i) $p_{\ell,m+1}(x, y) = p_{\ell,m}(x, y) - p_{\ell,m}(x, x + y)$;
(ii) $p_{\ell,m}(x, x + y) = \sum_{j=m}^{\ell} \binom{\ell}{j} p_{j,m}(x, y)\, x^{\ell-j}$;
(iii) $p_{\ell,m+1}(x, y) = -\sum_{j=m}^{\ell-1} \binom{\ell}{j} p_{j,m}(x, y)\, x^{\ell-j}$;
(iv) $p_{\ell+1,m}(x, y) = y\, p_{\ell,m}(x, y) - m x\, p_{\ell,m-1}(x, x + y)$;
(v) $p_{\ell+1,m+1}(x, y) = ((m + 1) x + y)\, p_{\ell,m+1}(x, y) -
(m + 1) x\, p_{\ell,m}(x, y)$;
(vi) if $\ell \ge 1$, the complex derivative of $z \mapsto p_{\ell,m}(x, z)$ at $z = y$ is
$\ell\, p_{\ell-1,m}(x, y)$;
(vii) if $\ell \ge 1$, then
$p_{\ell,m}(x, y) = (m x + y)\, p_{\ell-1,m}(x, y) - m x\, p_{\ell-1,m-1}(x, y)$.

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*, INTEGERS 24 (2024), Article A70, Proposition 4 (`integers-2024-A70-prop-4`).
