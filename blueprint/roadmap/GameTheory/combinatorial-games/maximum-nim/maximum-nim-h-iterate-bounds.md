# Linear bounds on h_k and their iterates

Let $k \ge 2$ be a natural number, let
$h_k(x) = x + \lfloor x/(k-1) \rfloor + 1$ on natural numbers, and define the real maps
$h_k^-(x) = x + \frac{x}{k-1}$ and $h_k^+(x) = x + \frac{x}{k-1} + 1$. Writing $g^p$ for the
$p$-fold iterate of a map $g$, for all natural numbers $p$ and $x$: (i)
$(h_k^-)^p(x) = \left(\frac{k}{k-1}\right)^p x$, (ii)
$(h_k^+)^p(x) = \left(\frac{k}{k-1}\right)^p (x + k - 1) - (k - 1)$, and (iii)
$h_k^-(x) \le h_k(x) \le h_k^+(x)$.

## Sources

- Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*, INTEGERS 24 (2024), Article G5, Lemma 7 (`integers-2024-G5-lem-7`).
