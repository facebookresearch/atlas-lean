# Constituent coefficients for bishops on one color

For natural numbers $k$, $d$ and a
complex number $z$, the constituent coefficient $c_{k,d}(z)$ is

$$c_{k,d}(z) = \sum_{i=d}^{2k} \frac{(-1)^{i-d}}{i!} {i \brack d}
\sum_{p=\max(0, i-k)}^{k} \sum_{j=p}^{k} S_2(p+j, p) \, \beta_i(p+j, k-j, z),$$

where ${i \brack d}$ is the unsigned Stirling number of the first kind, $S_2(n, r)$ is the
2-associated Stirling number of the second kind, and $\beta_i(p, q, z)$ is the coefficient
$\beta$ of Santos's Lemma 2.7.

Taking $z = -\pi(m)$ and $z = \pi(m)$, where $\pi(m) \in \{0, 1\}$ is the parity of $m$, gives
the coefficients of $m^d$ in the quasi-polynomials (13) and (14) for $k$ bishops on the white
and black squares.

## Sources

- Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*, Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 2.8.
