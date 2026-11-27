# Campbell's auxiliary function $h_3^{(m)}$

For a natural number $m$, let
$H(m) = h_2(10^m) - h_2(10^m - 1)$, where $h_2$ is Campbell's sequence (in the paper's notation
$H(m) = y_1(m + 1) - y_2(m)$ with $y_1(n) = h_2(10^{n-1})$ and $y_2(n) = h_2(10^n - 1)$). Define
$h_3^{(m)} : \mathbb{R} \to \mathbb{R}$ by $h_3^{(m)}(t) = a(m)\,t + b(m)$ for
$t \le 10^m - 1/10$ and $h_3^{(m)}(t) = c(m)\,t + d(m)$ for $t > 10^m - 1/10$, where
$a(m) = (20H(m) - 11 \cdot 10^m)/9 + 9 \cdot 10^{m-1}$,
$b(m) = (10^m - 1)(-20H(m) + 11 \cdot 10^m)/9 + 10^m - 9 \cdot 10^{2m-1}$,
$c(m) = -20H(m) + 9 \cdot 10^{m-1} + 11 \cdot 10^m$ and
$d(m) = 20 \cdot 10^m H(m) - 11 \cdot 10^{2m} - 9 \cdot 10^{2m-1} + 10^m$, with the exponents
$m - 1$ and $2m - 1$ read as $0$ when $m = 0$.

The paper uses $h_3^{(m)}$ only on $[10^m - 1, 10^m]$ for $m \ge 2$.

## Sources

- John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*, Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2.2, Equations (16)-(20).
