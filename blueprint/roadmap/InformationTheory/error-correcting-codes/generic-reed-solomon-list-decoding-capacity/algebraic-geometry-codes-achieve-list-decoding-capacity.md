# Brakensiek-Dhar-Gopi-Zhang: random AG codes achieve capacity over constant-size fields

For every rational $\varepsilon, R \in (0, 1)$ with $R + \varepsilon < 1$, let $L = \lceil 2(1-R)/\varepsilon \rceil$. For every sufficiently large prime $p$ with $\log_2 p \gg_R 1/\varepsilon^2$ (giving constant field size $q = p^2 = 2^{O_R(1/\varepsilon^2)}$) and every sufficiently large length $n$ for which there exists an integer $t$ with $Rn/2 \ge p^t \ge Rn/4$, a random puncturing of the Garcia–Stichtenoth algebraic-geometry code $\mathrm{GS}(p, t, s)$ over $\mathbb{F}_{p^2}$ with $s = Rn + g(G_{p,t}) - 1$ is, with probability at least $1 - 2^{-Ln}$, a $(1 - R - \varepsilon, L)$ average-radius list-decodable $[n, Rn]$-code (Brakensiek–Dhar–Gopi–Zhang, Corollary 4.34; Theorem 1.3 gives the trade-off $(\frac{L}{L+1}(1-R-\varepsilon), L)$ over fields of size $\exp(O(L/\varepsilon))$). This gives the first proof that algebraic-geometry codes, by random puncturing, achieve list-decoding capacity, yielding linear codes over constant-size fields with list size $O(1/\varepsilon)$.

## Proof sketch

Generalize the GM-MDS machinery from polynomials to Riemann-Roch spaces of divisors on a curve: generic evaluation points on a curve of bounded genus relative to length again attain the generic intersection dimensions up to an error controlled by the genus. Combined with the reduced intersection matrix analysis, the gap to capacity incurred by the genus is absorbed into $\varepsilon$ for curves with many rational points.

## Depends on

- [List-decodable code](../list-decoding/is-list-decodable.md)

## Proof depends on

- [Alrabiah-Guruswami-Li: randomly punctured RS codes achieve capacity over linear-size fields](random-reed-solomon-codes-list-decodable-over-linear-fields.md)
- [Generic Reed-Solomon codes are MDS(l) for every l](generic-reed-solomon-codes-are-higher-order-mds.md)

## Sources

- Joshua Brakensiek, Manik Dhar, Sivakanth Gopi, Zihan Zhang, "AG codes achieve list decoding capacity over constant-sized fields", STOC (2024); arXiv:2310.12898.
