# Euler product for the mean value of a multiplicative function of several variables

Let $f : \mathbb{N}^k \to \mathbb{C}$ satisfy $f(a_0 b_0, \dots, a_{k-1} b_{k-1}) = f(a) f(b)$
for all $a, b \in \mathbb{N}^k$ with $\gcd(a_0 \cdots a_{k-1}, b_0 \cdots b_{k-1}) = 1$. Let $\mu$
be the Möbius function, and for $n \in \mathbb{N}^k$ with every $n_i \ge 1$ put
$(\mu * f)(n) = \sum_{d} \mu(d_0) \cdots \mu(d_{k-1}) f(n_0/d_0, \dots, n_{k-1}/d_{k-1})$, the
sum over all $d \in \mathbb{N}^k$ with each $d_i$ a positive divisor of $n_i$. For a prime $p$
and $\nu \in \mathbb{N}^k$ write $p^\nu = (p^{\nu_0}, \dots, p^{\nu_{k-1}})$ and
$|\nu| = \nu_0 + \dots + \nu_{k-1}$. Assume that the family $|(\mu * f)(p^\nu)| / p^{|\nu|}$,
indexed by the pairs of a prime $p$ and a nonzero $\nu \in \mathbb{N}^k$, is summable. Then there
is a complex number $M$ such that the averages

$$\frac{1}{x_0 \cdots x_{k-1}} \sum_{1 \le n_i \le x_i} f(n)$$

(the sum over all $n \in \mathbb{N}^k$ with $1 \le n_i \le x_i$ for every $i$) tend to $M$ as
$x \in \mathbb{N}^k$ tends to infinity in every coordinate jointly, and

$$M = \prod_p \Bigl(1 - \frac{1}{p}\Bigr)^k \sum_{\nu} \frac{f(p^\nu)}{p^{|\nu|}},$$

the product running over all primes $p$ and the sum over all $\nu \in \mathbb{N}^k$.

The averages are taken over integer $x_i$; this is equivalent to real $x_i$, since only
$\lfloor x_i \rfloor$ enters the sum and $\lfloor x_i \rfloor / x_i \to 1$. The multiplicativity
hypothesis is the source's multivariable one, weaker than coordinatewise multiplicativity.

## Sources

- László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5, Theorem 3 (`jis-2024-24.8.5-thm-3`).
