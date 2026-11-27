# Shangguan-Tamo: Reed-Solomon codes list-decode beyond the Johnson radius for lists of size two and three

For $L \in \{2, 3\}$ and every rate $R \in (0,1)$, there exist Reed-Solomon codes of rate $R$ (over sufficiently large fields, with suitably chosen evaluation points) that are $\big(\frac{L}{L+1}(1 - R), L\big)$-list decodable; this radius exceeds the Johnson radius $1 - \sqrt R$ for the rates $R$ with $\frac{L}{L+1}(1 - R) > 1 - \sqrt{R}$.

## Proof sketch

Write the conditions for $L + 1$ polynomials to agree with a received word on sets $A_1, \dots, A_{L+1}$ as a linear system whose coefficient matrix has entries that are monomials in the evaluation points. For $L \le 3$ a direct combinatorial analysis of the possible intersection patterns shows this matrix has full rank as a polynomial matrix, so it is nonsingular for evaluation points avoiding a hypersurface.

## Depends on

- [Generic and randomly punctured Reed-Solomon codes](generic-reed-solomon-codes.md)
- [List-decodable code](../list-decoding/is-list-decodable.md)

## Proof depends on

- [Generalized Singleton bound for list decoding (Shangguan-Tamo)](generalized-singleton-bound-for-list-decoding.md)
- [Reed–Solomon codes are list decodable up to the Johnson radius](../list-decoding/card-le-of-agree-ge.md)

## Sources

- Chong Shangguan, Itzhak Tamo, "Combinatorial list-decoding of Reed-Solomon codes beyond the Johnson radius", STOC (2020); arXiv:1911.01502.
