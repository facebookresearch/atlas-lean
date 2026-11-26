# Guo-Zhang: randomly punctured RS codes achieve capacity over polynomial-size fields

For every $\varepsilon > 0$ and $R \in (0,1)$, with high probability a randomly punctured Reed-Solomon code of length $n$ and rate $R$ over $\mathbb{F}_q$ with $q \ge 2^{\mathrm{poly}(1/\varepsilon)} n^2$ is $\big(1 - R - \varepsilon, O(1/\varepsilon)\big)$-list decodable.

## Proof sketch

For each bad configuration (an agreement hypergraph of a list of size $L + 1 = O(1/\varepsilon)$), the determinant witnessing full rank of a reduced intersection matrix is a nonzero polynomial of degree $O(nL)$ in the evaluation points. Instead of union bounding over all configurations, Guo and Zhang reveal the evaluation points one at a time and bound the probability that a given hypergraph becomes bad by a product of per-step probabilities $O(nL/q)$, which, combined with a careful count of hypergraphs, yields quadratic field size.

## Depends on

- [Generic and randomly punctured Reed-Solomon codes](generic-reed-solomon-codes.md)

## Proof depends on

- [Agreement hypergraphs and reduced intersection matrices](agreement-hypergraphs-and-intersection-matrices.md)
- [Brakensiek-Gopi-Makam: generic Reed-Solomon codes achieve list-decoding capacity](generic-reed-solomon-codes-achieve-list-decoding-capacity.md)

## Sources

- Zeyu Guo, Zihan Zhang, "Randomly punctured Reed-Solomon codes achieve the list decoding capacity over polynomial-size alphabets", FOCS (2023); arXiv:2304.01403.
