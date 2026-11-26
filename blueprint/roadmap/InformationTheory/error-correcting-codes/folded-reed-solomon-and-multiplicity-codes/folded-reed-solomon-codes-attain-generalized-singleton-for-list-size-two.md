# Tamo: improved list sizes and generalized Singleton for list size two

Folded Reed-Solomon and multiplicity codes of rate $R$ are list decodable up to radius $1 - R - \varepsilon$ with list size $(1/\varepsilon)^{O(1/\varepsilon)}$ via a streamlined argument, with an improved randomized algorithm, and folded Reed-Solomon codes asymptotically attain the generalized Singleton bound $\frac{2}{3}(1 - R)$ for list size $2$ over relatively small alphabets, the first explicit codes with this property.

## Proof sketch

Bound the number of codewords in an affine subspace of dimension $r$ close to the received word by induction on $r$: a close codeword forces agreement on many coordinates, each imposing a linear condition on the subspace, and a counting of incidences between codewords and coordinates shows the subspace must shrink after a bounded number of codewords.

## Depends on

- [List recovery and relaxed generalized Singleton bounds](list-recovery-of-folded-codes.md)
- [Generalized Singleton bound for list decoding (Shangguan-Tamo)](../generic-reed-solomon-list-decoding-capacity/generalized-singleton-bound-for-list-decoding.md)
- [Folded Reed-Solomon codes](folded-reed-solomon-codes.md)
- [Univariate multiplicity codes](univariate-multiplicity-codes.md)

## Proof depends on

- [Guruswami-Wang: the list of folded RS and multiplicity codes lies in a low-dimensional subspace](linear-algebraic-list-decoding-into-a-subspace.md)

## Sources

- Itzhak Tamo, "Tighter list-size bounds for list-decoding and recovery of folded Reed-Solomon and multiplicity codes", IEEE Transactions on Information Theory (2024); arXiv:2312.17097.
