---
article_id: af_6547cc94235dcdedf22efaa3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Combinatorics.Coding.HammingSpherePacking.hamming_sphere_packing_bound
---

# Hamming Sphere Packing

The Hamming (sphere-packing) bound for `q`-ary block codes: a code of length `n`
with pairwise Hamming distance at least `2 * t + 1` satisfies
`C.card * ∑_{i=0}^t n.choose i * (q - 1)^i ≤ q^n`.

The proof packs disjoint radius-`t` Hamming balls around the codewords into the
ambient space: the distance hypothesis forces the balls apart (any overlap would
give a triangle-inequality contradiction), and each ball has the stated volume
(`Hamming.card_ball`).

This is the `q`-ary generalization of Hamming's binary sphere-packing bound. The
original paper assumes binary words and derives the `2^n` form; the same disjoint-ball
counting argument gives the formula stated here for an arbitrary finite alphabet.

Binary source: R. W. Hamming, "Error Detecting and Error Correcting Codes",
Bell System Technical Journal 29 (1950), 147–160,
DOI 10.1002/j.1538-7305.1950.tb00463.x.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Ball](../../../../InformationTheory/MathlibExt/hamming-ball/ball.md)
- [Card ball](../../../../InformationTheory/MathlibExt/hamming-ball/card-ball.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Coding.HammingSpherePacking](../../../../../sources/v2/MathlibExt.md)
