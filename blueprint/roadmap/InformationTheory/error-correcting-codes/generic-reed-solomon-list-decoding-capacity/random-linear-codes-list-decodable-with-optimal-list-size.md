# Random linear codes achieve list-decoding capacity with optimal list size O(1/epsilon)

For every $\varepsilon > 0$ and $R \in (0,1)$, a uniformly random linear code of rate $R$ over an alphabet of size $q \ge 2^{O(1/\varepsilon^2)}$ is, with high probability, list decodable from radius $1 - R - \varepsilon$ with list size $O(1/\varepsilon)$. This was the first linear code family over constant-size alphabets known to achieve capacity with optimal list size.

## Proof sketch

Replace generic evaluation vectors by uniformly random columns of a generator matrix: the analysis of agreement hypergraphs and weak partition connectivity carries over, with Schwartz-Zippel replaced by the exact probability that random vectors fall into prescribed subspaces, which is controlled for alphabets of size $2^{O(1/\varepsilon^2)}$.

## Depends on

- [List-decodable code](../list-decoding/is-list-decodable.md)

## Proof depends on

- [Weak partition connectivity gives generic full rank of intersection matrices](weakly-partition-connected-hypergraphs-give-generic-full-rank.md)
- [Alrabiah-Guruswami-Li: randomly punctured RS codes achieve capacity over linear-size fields](random-reed-solomon-codes-list-decodable-over-linear-fields.md)

## Sources

- Omar Alrabiah, Venkatesan Guruswami, Ray Li, "Randomly punctured Reed-Solomon codes achieve list-decoding capacity over linear-sized fields", STOC (2024); arXiv:2304.09445.
