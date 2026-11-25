# Euler product for mean values of coordinatewise multiplicative functions

Let $k$ be a natural
number, write $\mathbb{N} = \{0, 1, 2, \dots\}$, and let $f \colon \mathbb{N}^k \to \mathbb{C}$
satisfy $f(a_1 b_1, \dots, a_k b_k) = f(a) f(b)$ for all $a, b \in \mathbb{N}^k$ with
$\gcd(a_i, b_i) = 1$ for every $i$. For a prime $p$ and $\nu = (\nu_1, \dots, \nu_k) \in
\mathbb{N}^k$ write $p^\nu = (p^{\nu_1}, \dots, p^{\nu_k})$, $|\nu| = \nu_1 + \dots + \nu_k$ and

$$
(\mu * f)(p^\nu) = \sum_{d_1 \mid p^{\nu_1}, \dots, d_k \mid p^{\nu_k}}
\mu(d_1) \cdots \mu(d_k) \, f(p^{\nu_1} / d_1, \dots, p^{\nu_k} / d_k),
$$

where $\mu$ is the Möbius function and each $d_i$ runs over the positive divisors of $p^{\nu_i}$.
Suppose that the family $|(\mu * f)(p^\nu)| / p^{|\nu|}$, indexed by the pairs $(p, \nu)$ of a
prime $p$ and a nonzero $\nu \in \mathbb{N}^k$, is summable. Then there is a complex number $M$
such that

$$
\frac{1}{N^k} \sum_{n \in \{1, \dots, N\}^k} f(n) \to M \quad (N \to \infty)
$$

and

$$
M = \prod_p \Bigl(1 - \frac{1}{p}\Bigr)^k \sum_{\nu \in \mathbb{N}^k} \frac{f(p^\nu)}{p^{|\nu|}},
$$

where the product runs over all primes and the product and the inner sums are unconditional (an
unconditional sum that does not converge is read as $0$, a product as $1$).

This is the Wintner–Ushiroya theorem (Ushiroya, Theorem 4; Tóth, Proposition 19) under a
stronger multiplicativity hypothesis: the source asks for $f(a_1 b_1, \dots, a_k b_k) = f(a) f(b)$
only when $\gcd(a_1 \cdots a_k, b_1 \cdots b_k) = 1$. The hypothesis used here forces $f$ to be a
product of one-variable multiplicative functions of the coordinates, and the proof reduces to the
one-variable Wintner theorem in each coordinate. The averages over the cubes $\{1, \dots, N\}^k$
are the diagonal of the source's multi-parameter limit, so they converge to the same value.

## Sources

- László Tóth, "On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components," Journal of Integer Sequences 27 (2024), Article 24.8.5, Theorem (unlabeled; multiplicative-function form), equation, lines 314–326, https://cs.uwaterloo.ca/journals/JIS/VOL27/Toth/toth27.tex
