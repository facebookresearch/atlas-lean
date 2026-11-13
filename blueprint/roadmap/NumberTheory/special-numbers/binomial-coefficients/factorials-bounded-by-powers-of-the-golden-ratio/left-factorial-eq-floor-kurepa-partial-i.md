# Floor formulas for the left factorial

Let $!n = \sum_{k=0}^{n-1} k!$ be the left
factorial, let $K_n(x) = \int_0^x e^{-t} \sum_{k=0}^{n-1} t^k \, dt$ be Kurepa's partial integral,
let $h(y) = y e^y$ be the Lambert map, and let $\alpha(n)$ be the least positive integer $m$ with
$n! \le \varphi^m$, where $\varphi$ is the golden ratio. Then the following hold.
(i) For every integer $n \ge 1$, $\lfloor K_n(\alpha(n)) \rfloor + 1 = {!n}$.
(ii) For every integer $n > 4$ and every real $a \ge n - 1$ with
$h(-\frac{a}{n-1}) = -\frac{1}{n-1} (\frac{4}{7})^{1/(n-1)}$, we have
$\lfloor K_n(a) \rfloor + 1 = {!n}$.
(iii) For all integers $n > 4$ and $m \ge 1$ and every real $A \ge n - 1$ with
$h(-\frac{A}{n-1}) = -\frac{1}{n-1} (\frac{4}{7m})^{1/(n-1)}$, we have
$\lfloor K_n(A) + \frac{1}{m} \rfloor = {!n}$.

## Sources

- Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio, Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024), Article 24.5.7, Corollary 15 (`jis-2024-24.5.7-cor-15`).
