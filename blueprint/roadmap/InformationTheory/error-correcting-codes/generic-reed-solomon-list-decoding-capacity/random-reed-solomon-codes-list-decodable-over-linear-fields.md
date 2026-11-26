# Alrabiah-Guruswami-Li: randomly punctured RS codes achieve capacity over linear-size fields

For every $\varepsilon > 0$ and $R \in (0,1)$ there is $C_\varepsilon = 2^{O(1/\varepsilon^2)}$ such that, with high probability, a randomly punctured Reed-Solomon code of length $n$ and rate $R$ over a field of size $q \ge C_\varepsilon\, n$ is $\big(1 - R - \varepsilon, O(1/\varepsilon)\big)$-list decodable. The linear dependence of $q$ on $n$ is optimal up to the constant factor.

## Proof sketch

Using weak partition connectivity, a bad event for a received word implies the existence of a small weakly partition connected sub-hypergraph whose intersection matrix is singular. Alrabiah, Guruswami and Li bound the probability that a fixed such hypergraph is singular by revealing evaluation points and tracking a potential that drops by a factor $O(n/q)$ per coordinate in a large set, and then sum over hypergraphs encoded compactly by their reduced form, obtaining field size $O_\varepsilon(n)$.

## Depends on

- [Generic and randomly punctured Reed-Solomon codes](generic-reed-solomon-codes.md)

## Proof depends on

- [Weak partition connectivity gives generic full rank of intersection matrices](weakly-partition-connected-hypergraphs-give-generic-full-rank.md)
- [Guo-Zhang: randomly punctured RS codes achieve capacity over polynomial-size fields](random-reed-solomon-codes-list-decodable-over-polynomial-fields.md)

## Sources

- Omar Alrabiah, Venkatesan Guruswami, Ray Li, "Randomly punctured Reed-Solomon codes achieve list-decoding capacity over linear-sized fields", STOC (2024); arXiv:2304.09445.
