# Girstmair's cotangent power sums, odd case

Let $n \ge 2$, let $r$ be odd, and let $\chi$
be a complex Dirichlet character modulo $n$ with $\chi(-1) = -1$. Let $f$ be the conductor of
$\chi$, $\chi_f$ the primitive character modulo $f$ attached to $\chi$, and $c_{r,j}$
Girstmair's cotangent power coefficients. Write
$\tau(\overline{\chi_f}) = \sum_{k=1}^{f} \overline{\chi_f(k)} e^{2 \pi i k/f}$ for the Gauss sum
and $B_{j,\chi_f} = f^{j-1} \sum_{k=1}^{f} B_j(k/f) \chi_f(k)$, where $B_j$ is the $j$-th
Bernoulli polynomial. Then

$$\sum_{k} \overline{\chi(k)} \left(i \cot \frac{\pi k}{n}\right)^r = -\tau(\overline{\chi_f})
\sum_{j} \frac{c_{r,j} (2n)^j}{j f^j}
\prod_{p \mid n} \Bigl(1 - \frac{\overline{\chi_f(p)}}{p^j}\Bigr) B_{j,\chi_f},$$

where $k$ runs over $1 \le k \le n$ with $\gcd(k, n) = 1$, $j$ runs over the odd numbers with
$1 \le j \le r$, and $p$ runs over the primes dividing $n$.

The left side is $\tau(\overline{\chi_f})$ times the character coordinate
$y(\chi \mid i^r \cot^r(\pi/n))$ of the source, defined by Equation (3), since
$\sigma_k(i^r \cot^r(\pi/n)) = i^r \cot^r(\pi k/n)$ (Equation (4)).

## Sources

- Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025), Article A63, Theorem 1, first case.
