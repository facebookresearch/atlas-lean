# Representation numbers of the quaternary forms $(1,1,10,10)$ and $(2,2,5,5)$

For a complex number $q$ write $f_k = \prod_{m \ge 1} (1 - q^{km})$. For
integers $a, b, c, d$ and $n$, let $N(a,b,c,d;n)$ be the number of $(x_1, x_2, x_3, x_4) \in
\mathbb{Z}^4$ with $a x_1^2 + b x_2^2 + c x_3^2 + d x_4^2 = n$, and let $\sigma(n/k)$ be the sum
of the positive divisors of $n/k$ if $k \mid n$ and $0$ otherwise. Let $b_1, b_2, b_3$ be sequences
of complex numbers indexed by $n \ge 0$ such that for every complex $q$ with $|q| < 1$ the
series $\sum_{n \ge 0} b_i(n) q^n$ converge, with sums $q f_2^2 f_{10}^2$, $q^2 f_4^2 f_{20}^2$
and $q^3 f_4^5 f_{10} f_{40}^2 / (f_2 f_8^2 f_{20})$ for $i = 1, 2, 3$ respectively. For
$n \ge 1$ put

$$
T(n) = \tfrac{2}{3}\sigma(n) - \tfrac{2}{3}\sigma(n/2) + \tfrac{4}{3}\sigma(n/4) +
\tfrac{10}{3}\sigma(n/5) - \tfrac{16}{3}\sigma(n/8) - \tfrac{10}{3}\sigma(n/10) +
\tfrac{20}{3}\sigma(n/20) - \tfrac{80}{3}\sigma(n/40).
$$

Then for every $n \ge 1$,

$$
N(1,1,10,10;n) = T(n) + \tfrac{10}{3} b_1(n) + \tfrac{8}{3} b_2(n) + 4b_3(n)
$$

and

$$
N(2,2,5,5;n) = T(n) - \tfrac{2}{3} b_1(n) + \tfrac{8}{3} b_2(n) - 4b_3(n).
$$

With $\eta_k = q^{k/24} f_k$, the three generating functions are the eta quotients
$\eta_2^2\eta_{10}^2$, $\eta_4^2\eta_{20}^2$ and
$\eta_4^5\eta_{10}\eta_{40}^2/(\eta_2\eta_8^2\eta_{20})$. These formulas are due to Alaca and
Altiary; Vasuki and Nagendra reprove them elementarily.

## Sources

- K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*, INTEGERS 25 (2025), Article A24, Theorem 1.1 (Alaca and Altiary).
