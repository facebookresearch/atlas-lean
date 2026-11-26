# Generating function for hook tableau counts

For a natural number $k$, let
$\mathrm{SYT}_k(2,1;n)$ be the number of standard Young tableaux of order $n$ in the
$(2,1)$-hook whose first row is longer than its second row by exactly $k$, and let
$M(x) = \sum_{n \ge 0} m_n x^n$ be the generating function of the Motzkin numbers $m_n$. Then,
in the ring of formal power series with integer coefficients,

$$
(1 + x) \sum_{n \ge k} \mathrm{SYT}_k(2,1;n)\, x^n = x^k \bigl(1 + x\, M(x)^{k+1}\bigr).
$$

The factor $1 + x$ is cleared, so the identity involves no division.

## Sources

- Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal of Integer Sequences 28 (2025), Article 25.8.1, Corollary 9 (`jis-2025-25.8.1-cor-9`).
