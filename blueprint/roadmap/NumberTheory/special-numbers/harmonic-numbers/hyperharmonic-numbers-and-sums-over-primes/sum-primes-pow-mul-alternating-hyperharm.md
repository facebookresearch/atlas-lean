# Prime-weighted power sums of type I alternating hyperharmonic numbers

Let
$\alpha, m, y \ge 1$ and $q \ge 2$ be integers. Let $p_\ell$ be the $\ell$-th prime ($p_1 = 2$),
let $H_n^{(s,r,1)}$ be the signed iterated partial sum of order $r$, with alternating signs, of the
generalized harmonic numbers $H_n^{(s)} = \sum_{j=1}^{n} j^{-s}$, let
$\zeta(q) = \sum_{n \ge 1} n^{-q}$, and let $\bar\zeta$ be the alternating zeta function. For a
real sequence $f$ write

$$S_x(f) = \sum_{\ell=1}^{x} p_\ell^\alpha f(\ell)^m, \qquad
T_x(f) = \sum_{\substack{1 \le \ell \le x \\ p_\ell \le x}} p_\ell^\alpha f(\ell)^m,$$

put $E = my + 1$, $F = m(y-1) + 1$, $A = \alpha + E$ and $B = \alpha + F$, and let
$f_1(\ell) = H_\ell^{(1,2y+1,1)}$, $f_2(\ell) = H_\ell^{(q,2y+1,1)}$,
$f_3(\ell) = (-1)^{\ell-1} H_\ell^{(1,2y,1)}$, $f_4(\ell) = H_{2\ell-1}^{(1,2y,1)}$,
$f_5(\ell) = -H_{2\ell}^{(1,2y,1)}$, $f_6(\ell) = H_{2\ell-1}^{(q,2y,1)}$ and
$f_7(\ell) = -H_{2\ell}^{(q,2y,1)}$. Then, as the natural number $x$ tends to infinity,

$$S_x(f_1) \sim \frac{x^A (\log x)^{\alpha+m}}{(2^y y!)^m A}, \qquad
T_x(f_1) \sim \frac{x^A}{(2^y y!)^m A (\log x)^{m(y-1)+1}},$$



$$S_x(f_2) \sim \frac{\zeta(q)^m x^A (\log x)^\alpha}{(2^y y!)^m A}, \qquad
T_x(f_2) \sim \frac{\zeta(q)^m x^A}{(2^y y!)^m A (\log x)^E},$$



$$S_x(f_3) \sim \frac{x^B (\log x)^{\alpha+m}}{(2^y (y-1)!)^m B}, \qquad
T_x(f_3) \sim \frac{x^B}{(2^y (y-1)!)^m B (\log x)^{m(y-2)+1}},$$

for $i = 4, 5$

$$S_x(f_i) \sim \frac{x^B (\log x)^{\alpha+m}}{(2 (y-1)!)^m B}, \qquad
T_x(f_i) \sim \frac{x^B}{(2 (y-1)!)^m B (\log x)^{m(y-2)+1}},$$

and

$$S_x(f_6) \sim \frac{(\zeta(q) + \bar\zeta(q))^m x^B (\log x)^\alpha}{(2 (y-1)!)^m B}, \qquad
T_x(f_6) \sim \frac{(\zeta(q) + \bar\zeta(q))^m x^B}{(2 (y-1)!)^m B (\log x)^F},$$



$$S_x(f_7) \sim \frac{(\zeta(q) - \bar\zeta(q))^m x^B (\log x)^\alpha}{(2 (y-1)!)^m B}, \qquad
T_x(f_7) \sim \frac{(\zeta(q) - \bar\zeta(q))^m x^B}{(2 (y-1)!)^m B (\log x)^F}.$$

The exponent $m(y-2)+1$ of $\log x$ may be negative; the power is then an integer power.

## Sources

- Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024), Article 24.4.1, Theorem 11 (`jis-2024-24.4.1-thm-11`).
