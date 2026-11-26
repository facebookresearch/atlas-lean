# Limiting area between even cosine powers

For natural numbers $n$ and $k$, let
$A_n(k) = \int_0^\pi |\cos^n x - \cos^n(kx)|\,dx$. As $k \to \infty$ through the natural numbers:
if $n \equiv 2 \pmod 4$, then

$$A_n(k) \to \frac{16}{2^n \pi} \sum_{j=0}^{(n-2)/4} \frac{\binom{n}{2j}}{(n/2 - 2j)^2},$$

and if $n \equiv 0 \pmod 4$, then

$$A_n(k) \to \frac{16}{2^n \pi} \sum_{j=0}^{(n-4)/4} \frac{\binom{n}{2j+1}}{(n/2 - 2j - 1)^2}.$$

For $n = 0$ the right-hand side is $0$, as is $A_0(k)$ for every $k$, so no positivity hypothesis
is needed.

## Sources

- Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*, Journal of Integer Sequences 28 (2025), Article 25.2.3, Theorem 2 (`jis-2025-25.2.3-thm-2`).
