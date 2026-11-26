# cq: lookup arguments with prover time independent of the table size

For a table of size $N$ committed via KZG over a pairing-friendly group, after an $O(N\log N)$ preprocessing step computing the cached quotient commitments, the cq protocol proves that the $n$ values of a committed polynomial over a subgroup of size $n$ lie in the table with a prover running in $O(n\log n)$ field operations and $O(n)$ group operations, constant-size proofs, and a constant number of pairings for verification. It is knowledge sound in the algebraic group model and random oracle model under a $q$-type discrete-log assumption, supports homomorphic table commitments (hence vector lookups), and its verifier uses no pairings with prover-defined $\mathbb{G}_2$ elements.

## Proof sketch

The prover commits to the multiplicities and to $A$ over the table domain using cached quotients, and to the witness-side logarithmic derivatives over the small domain; sum equality is checked by the identity $\sum_iA_i=\sum_jB_j$ via evaluation at $0$ of the respective polynomials. Soundness combines the logarithmic-derivative lemma with KZG extraction.

## Depends on

- [Cached quotients make table commitments reusable](cached-quotients.md)
- [Security of KZG polynomial commitments](../zero-knowledge-and-arguments/security-of-kzg-polynomial-commitments.md)
- [Lookup relations with multiplicities](lookup-relation.md)

## Proof depends on

- [Soundness of checking the logarithmic-derivative identity at a random point](logup-random-evaluation.md)

## Sources

- Liam Eagen, Dario Fiore, Ariel Gabizon, "cq: Cached Quotients for Fast Lookups", IACR ePrint 2022/1763 (2022).
