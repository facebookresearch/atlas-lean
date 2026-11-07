# Girstmair's cotangent power sums, even case

Let $n \ge 2$, let $r \ge 2$ be even, and let
$\chi$ be a complex Dirichlet character modulo $n$ with $\chi(-1) = 1$. Let $f$ be the conductor
of $\chi$, $\chi_f$ the primitive character modulo $f$ attached to $\chi$, and $c_{r,j}$
Girstmair's cotangent power coefficients. Write
$\tau(\overline{\chi_f}) = \sum_{k=1}^{f} \overline{\chi_f(k)} e^{2 \pi i k/f}$ for the Gauss sum,
$B_{j,\chi_f} = f^{j-1} \sum_{k=1}^{f} B_j(k/f) \chi_f(k)$, where $B_j$ is the $j$-th Bernoulli
polynomial, and $\varepsilon_\chi = \varphi(n)$ if $\chi$ is the principal character modulo $n$
and $\varepsilon_\chi = 0$ otherwise. Then

$$\sum_{k} \overline{\chi(k)} \left(i \cot \frac{\pi k}{n}\right)^r = \tau(\overline{\chi_f}) \,
\Bigl(\varepsilon_\chi + \sum_{j} \frac{c_{r,j} (2n)^j}{j f^j}
\prod_{p \mid n} \Bigl(1 - \frac{\overline{\chi_f(p)}}{p^j}\Bigr) B_{j,\chi_f}\Bigr),$$

where $k$ runs over $1 \le k \le n$ with $\gcd(k, n) = 1$, $j$ runs over the even numbers with
$1 \le j \le r$, and $p$ runs over the primes dividing $n$.

The left side is $\tau(\overline{\chi_f})$ times the character coordinate
$y(\chi \mid i^r \cot^r(\pi/n))$ of the source (Equation (3)), and $\varepsilon_\chi$ is
$y(\chi \mid 1)$ (Equation (11)).

## Sources

- Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025), Article A63, Theorem 1, second case (`integers-2025-A63-thm-1`).
