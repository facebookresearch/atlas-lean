# PLONK: a universal-setup zkSNARK with constant-size proofs

For PLONK constraint systems with $n$ gates, the PIOP combining the gate equation, the permutation argument and the quotient test, compiled with KZG polynomial commitments over a pairing-friendly group and made non-interactive by Fiat–Shamir, is a preprocessing zkSNARK with a universal and updatable structured reference string of size $O(n)$ group elements. Proofs consist of a constant number of group and field elements, verification uses a constant number of pairings and $O(\ell+\log n)$ field operations for $\ell$ public inputs, and the prover performs $O(n\log n)$ field operations and $O(n)$ group exponentiations. Knowledge soundness holds in the algebraic group model and the random oracle model under the $q$-DLOG assumption.

## Proof sketch

Linear combinations of the gate, permutation and boundary constraints with a random challenge yield one polynomial that must vanish on $H$, proved via the quotient test. The KZG extractor in the algebraic group model recovers the committed polynomials, and the PIOP soundness bounds then apply; Fiat–Shamir is applied to the public-coin protocol.

## Depends on

- [Security of KZG polynomial commitments](../zero-knowledge-and-arguments/security-of-kzg-polynomial-commitments.md)
- [PLONK gate equations with copy constraints](plonk-constraint-system.md)
- [Polynomial interactive oracle proofs](polynomial-iop.md)
- [Succinct arguments and SNARKs](../zero-knowledge-and-arguments/succinct-arguments-and-snarks.md)

## Proof depends on

- [Compiling polynomial IOPs with polynomial commitments into succinct arguments](piop-compilation.md)
- [Grand-product permutation argument with random linear combinations](plonk-permutation-argument.md)
- [Vanishing on a multiplicative subgroup and the quotient test](subgroup-vanishing-quotient.md)
- [Lagrange basis over a multiplicative subgroup](lagrange-basis-subgroup.md)

## Sources

- Ariel Gabizon, Zachary J. Williamson, Oana Ciobotaru, "PLONK: Permutations over Lagrange-bases for Oecumenical Noninteractive arguments of Knowledge", IACR ePrint 2019/953 (2019).
