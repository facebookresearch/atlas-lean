# Inverse of a multiplicative function under the square-splitting convolution

Let $f$ be a
multiplicative complex arithmetic function (an arithmetic function $h$ is multiplicative when
$h(1) = 1$ and $h(mn) = h(m)\, h(n)$ for coprime $m$ and $n$), let $\star$ be the square-splitting
convolution, and let $\varepsilon$ be the arithmetic function with $\varepsilon(1) = 1$ and
$\varepsilon(n) = 0$ for $n \ne 1$. Then there is a complex arithmetic function $g$ with
$f \star g = \varepsilon$ such that every complex arithmetic function $g'$ with
$f \star g' = \varepsilon$ equals $g$. Moreover, $g$ is multiplicative; for every prime $p$ and
every $k \ge 1$, $\sum_{j=0}^{\lfloor k/2 \rfloor} f(p^{2j})\, g(p^{k-2j}) = 0$ if $k$ is even and
$\sum_{j=0}^{\lfloor k/2 \rfloor} (f(p^{2j}) g(p^{k-2j}) + f(p^{2j+1}) g(p^{k-2j-1})) = 0$ if $k$ is
odd; $g(1) = 1/f(1)$; and for every prime $p$, $g(p) = -f(p)/f(1)^2$,
$g(p^2) = -f(p^2)/f(1)^2$ and $g(p^3) = \big(2 f(p) f(p^2) - f(p^3) f(1)\big)/f(1)^3$.

Multiplicativity includes $f(1) = 1$, so the source's hypothesis $f(1) \ne 0$ holds automatically.

## Sources

- Champak Talukdar and Helen K. Saikia, *A Square-Splitting A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 5 (`integers-2026-A56-thm-5`).
