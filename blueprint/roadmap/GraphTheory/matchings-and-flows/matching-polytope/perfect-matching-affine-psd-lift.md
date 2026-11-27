# Superpolynomial affine PSD lifts for perfect matching

For all $C>0$ there is $n_0\ge4$ such that for all even $n\ge n_0$: if an affine subspace $L$ of the space of all real $r\times r$ matrices and an affine map $T$ from that matrix space have $T(L\cap\mathbb S^r_+)$ equal to the convex hull of perfect-matching incidence vectors of $K_n$, then $r>n^C$. The coordinates of incidence vectors are the pairs $0\le i<j<n$. The cone consists of the symmetric positive semidefinite matrices.

## Depends on

- [Perfect-matching polytope](perfect-matching-polytope.md)
- Affine section and affine image of the real PSD cone.

## Proof depends on

- [Perfect-matching slack PSD-rank obstruction](perfect-matching-slack-psd-rank.md)

## Expansion

Separate the factorization transfer for an arbitrary affine PSD lift: a lift of order r for this polytope gives a real PSD factorization of its actual unshifted slack matrix of order at most r, allowing reduction to the minimal containing cone face. Keep the linked independent slack-rank lower bound.

## Proof outline

Match the canonical edge coordinates and prove the exact lift-to-slack implication for all affine sections. Do not infer an exponential or positively shifted lower bound from this endpoint.

## Sources

- [Comparator statement: `OAI.PerfectMatchingPSD.affine_lift_lower_bound`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatchingAffineLift.lean#L27-L32)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/126.md)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/MatchingPSD/AffineLift.lean)
