# Brakensiek-Dhar-Gopi-Zhang: random AG codes achieve capacity over constant-size fields

For every $\varepsilon > 0$ there is $q_0 = 2^{O(1/\varepsilon^2)}$ such that for every $q \ge q_0$ and rate $R$, algebraic-geometry codes from suitable curves over $\mathbb{F}_q$ with randomly chosen evaluation points (of growing length $n$) are, with high probability, $\big(1 - R - \varepsilon, O(1/\varepsilon)\big)$-list decodable, giving the first algebraic code families over constant-size fields achieving list-decoding capacity with optimal list size.

## Proof sketch

Generalize the GM-MDS machinery from polynomials to Riemann-Roch spaces of divisors on a curve: generic evaluation points on a curve of bounded genus relative to length again attain the generic intersection dimensions up to an error controlled by the genus. Combined with the reduced intersection matrix analysis, the gap to capacity incurred by the genus is absorbed into $\varepsilon$ for curves with many rational points.

## Depends on

- [List-decodable code](../list-decoding/is-list-decodable.md)

## Proof depends on

- [Alrabiah-Guruswami-Li: randomly punctured RS codes achieve capacity over linear-size fields](random-reed-solomon-codes-list-decodable-over-linear-fields.md)
- [Generic Reed-Solomon codes are MDS(l) for every l](generic-reed-solomon-codes-are-higher-order-mds.md)

## Sources

- Joshua Brakensiek, Manik Dhar, Sivakanth Gopi, Zihan Zhang, "AG codes achieve list decoding capacity over constant-sized fields", STOC (2024); arXiv:2310.12898.
