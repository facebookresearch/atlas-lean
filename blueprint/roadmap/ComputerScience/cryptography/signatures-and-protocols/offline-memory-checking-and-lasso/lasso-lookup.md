# Lasso: lookup arguments into huge decomposable tables

For $m$ lookups into a $c$-decomposable table of size $N$ with $k$ subtables, using any multilinear polynomial commitment scheme, Lasso's prover commits to $O(c\,m+c\,N^{1/c})$ field elements, all of which are small (in $\{0,\dots,m\}$ or the subtable value range), and proves the lookups by a sum-check over $g$ applied to committed subtable reads combined with offline memory checking for each subtable; for unstructured tables of size $N$ it commits to $m+N$ small field elements. When using a multi-exponentiation-based commitment, the prover's cryptographic cost is $O(c(m+N^{1/c}))$ group operations plus one evaluation proof, and soundness follows from sum-check and memory-checking soundness with error $O((m+N^{1/c})\log N/|\mathbb{F}|)$.

## Proof sketch

Write each lookup index into $c$ chunks; the prover commits to chunk indices and subtable outputs. A sum-check proves that the claimed outputs equal $g$ applied to the subtable outputs, and memory checking (with read counts as committed small values) certifies each subtable output as a correct read; since the subtables have efficiently evaluable multilinear extensions, the verifier needs no commitment to them.

## Depends on

- [Decomposable lookup tables](decomposable-table.md)
- [Offline memory checking with timestamps](offline-memory-checking.md)
- [Polynomial commitment schemes](../zero-knowledge-and-arguments/polynomial-commitment-schemes.md)

## Proof depends on

- [Spark: committing to sparse multilinear polynomials via memory checking](spark-sparse-commitment.md)
- [Multiset equality via randomized product fingerprints](multiset-fingerprint.md)
- [Grand products via a layered binary-tree circuit and GKR](gkr-grand-product.md)

## Sources

- Srinath Setty, Justin Thaler, Riad Wahby, "Unlocking the Lookup Singularity with Lasso", EUROCRYPT (2024), IACR ePrint 2023/1216.
