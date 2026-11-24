# Representation numbers of the quaternary forms $(1,1,15,15)$, $(3,3,5,5)$ and $(1,3,5,15)$

**Representation numbers of the quaternary forms $(1,1,15,15)$, $(3,3,5,5)$ and
$(1,3,5,15)$.** For a complex number $q$ write $f_k = \prod_{m \ge 1} (1 - q^{km})$. For
integers $a, b, c, d$ and $n$, let $N(a,b,c,d;n)$ be the number of $(x_1, x_2, x_3, x_4) \in
\mathbb{Z}^4$ with $a x_1^2 + b x_2^2 + c x_3^2 + d x_4^2 = n$, and let $\sigma(n/k)$ be the sum
of the positive divisors of $n/k$ if $k \mid n$ and $0$ otherwise. Let $a_1, \dots, a_5$ be
sequences of complex numbers indexed by $n \ge 0$ such that for every complex $q$ with
$|q| < 1$ the series $\sum_{n \ge 0} a_i(n) q^n$ converge, with sums $q f_1 f_3 f_5 f_{15}$,
$q^2 f_2 f_6 f_{10} f_{30}$, $q^4 f_4 f_{12} f_{20} f_{60}$, $q f_3 f_5 f_6 f_{10}$ and
$q^2 f_6 f_{10} f_{12} f_{20}$ for $i = 1, \dots, 5$ respectively. For $n \ge 1$ put

$$
S(n) = \tfrac{2}{3}\sigma(n) - \tfrac{4}{3}\sigma(n/2) + \tfrac{8}{3}\sigma(n/4) - 2\sigma(n/3) +
4\sigma(n/6) - 8\sigma(n/12) + \tfrac{10}{3}\sigma(n/5) - \tfrac{20}{3}\sigma(n/10) +
\tfrac{40}{3}\sigma(n/20) - 10\sigma(n/15) + 20\sigma(n/30) - 40\sigma(n/60).
$$

Then for every $n \ge 1$,

$$
N(1,1,15,15;n) = S(n) + \tfrac{2}{3}(a_1(n) - 2a_2(n) + 4a_3(n) + 4a_4(n) + 8a_5(n)),
$$



$$
N(3,3,5,5;n) = S(n) + \tfrac{2}{3}(-5a_1(n) - 14a_2(n) - 20a_3(n) + 4a_4(n) + 8a_5(n))
$$

and

$$
N(1,3,5,15;n) = \tfrac{1}{2}(\sigma(n) - 2\sigma(n/2) + 4\sigma(n/4) + 3\sigma(n/3) -
6\sigma(n/6) + 12\sigma(n/12) - 5\sigma(n/5) + 10\sigma(n/10) - 20\sigma(n/20) -
15\sigma(n/15) + 30\sigma(n/30) - 60\sigma(n/60)) + \tfrac{3}{2} a_1(n) + a_2(n) + 6a_3(n).
$$

With $\eta_k = q^{k/24} f_k$, the five generating functions are the eta quotients
$\eta_1\eta_3\eta_5\eta_{15}$, $\eta_2\eta_6\eta_{10}\eta_{30}$,
$\eta_4\eta_{12}\eta_{20}\eta_{60}$, $\eta_3\eta_5\eta_6\eta_{10}$ and
$\eta_6\eta_{10}\eta_{12}\eta_{20}$. These formulas are due to Alaca; Vasuki and Nagendra
reprove them elementarily.

## Sources

- K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*, INTEGERS 25 (2025), Article A24, Theorem 1.2 (Alaca).
