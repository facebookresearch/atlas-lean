# Lambert bounds for the left factorial

Let $n \ge 5$ be an integer, let
$!n = \sum_{k=0}^{n-1} k!$ be the left factorial, let
$K_n(x) = \int_0^x e^{-t} \sum_{k=0}^{n-1} t^k \, dt$ be Kurepa's partial integral, let
$h(y) = y e^y$ be the Lambert map, and let $a$ be a real number with $a \ge n - 1$ and

$$h\left(-\frac{a}{n-1}\right) = -\frac{1}{n-1}\left(\frac{4}{7}\right)^{1/(n-1)}.$$

Then $K_n(a) < {!n} < K_n(a) + 1$.

The two conditions on $a$ say exactly that
$a = -(n-1)\, W_{-1}\left(-\frac{1}{n-1}\left(\frac{4}{7}\right)^{1/(n-1)}\right)$, where $W_{-1}$
is the lower real branch of the Lambert $W$ function; this is the paper's $a(n)$, and $K_n(a)$
is its $b(n)$.

## Sources

- Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio, Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024), Article 24.5.7, Theorem 10 (`jis-2024-24.5.7-thm-10`).
