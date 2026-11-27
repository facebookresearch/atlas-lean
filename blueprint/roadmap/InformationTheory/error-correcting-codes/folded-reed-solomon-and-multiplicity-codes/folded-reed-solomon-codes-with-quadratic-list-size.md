# Srivastava: folded Reed-Solomon codes with list size O(1/epsilon^2)

For every $\varepsilon > 0$ and $R \in (0,1)$ there are explicit folded Reed-Solomon codes of rate $R$ that are list decodable up to radius $1 - R - \varepsilon$ with lists of size $O(1/\varepsilon^2)$. More generally, for every $k \ge 1$, explicit folded Reed-Solomon codes of rate $R$ and distance $1 - R$ are list decodable arbitrarily close to radius $\frac{k}{k+1}(1 - R)$ with lists of size $(k-1)^2 + 1$.

## Proof sketch

Analyse intersections of Hamming balls with affine subspaces combinatorially: consider the close codewords inside the Guruswami-Wang subspace and the coordinates where several of them agree with the received word. Folded Wronskian determinants show that $r$ linearly independent close polynomials cannot jointly agree on too many coordinates, which feeds an induction on the dimension of the span and yields the quadratic bound.

## Depends on

- [Folded Reed-Solomon codes](folded-reed-solomon-codes.md)

## Proof depends on

- [Guruswami-Wang: the list of folded RS and multiplicity codes lies in a low-dimensional subspace](linear-algebraic-list-decoding-into-a-subspace.md)
- [Folded Wronskian criterion for linear independence](folded-wronskian-criterion-for-linear-independence.md)

## Sources

- Shashank Srivastava, "Improved list size for folded Reed-Solomon codes", SODA (2025); arXiv:2410.09031.
