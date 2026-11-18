# Cartier operator applied to a power times a monomial

Let $p$ be a prime and $P$ a
Laurent polynomial in $r$ variables with integer coefficients. Write $\mathrm{coef}_e[F]$ for the
coefficient of $x^e$ in a Laurent polynomial $F$, $\deg F$ for the largest absolute value of an
exponent of a variable occurring in $F$, and $\Lambda_p$ for the Cartier operator with
$\mathrm{coef}_j[\Lambda_p F] = \mathrm{coef}_{pj}[F]$. Let $m \in \mathbb{N}$ with
$\deg P \le m + 1$, put $T = [-m, m]^r \subset \mathbb{Z}^r$, and let $k < p$ be a natural
number and $i \in T$. Then
$\Lambda_p(P^k x^i) = \sum_{j \in T} \mathrm{coef}_{pj - i}[P^k] \, x^j$.

In Kohen's notation $\mathrm{coef}_{pj - i}[P^k]$ is $a^k_{i - pj}$.

## Sources

- Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2, Proposition 6 (`jis-2026-26.4.2-prop-6`).
