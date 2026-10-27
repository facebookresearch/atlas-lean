---
article_id: af_dcec305e1acd378273d00b71
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Combinatorics.HarperIsoperimetricWanted.harper_isoperimetric_inequality
---

# Harper Isoperimetric

Harper's Hamming-cube isoperimetric inequality, ball-comparison form (Theorem 9.4.3):
if `B` is a closed Hamming ball and `B.card ≤ A.card`, then every positive
natural-radius closed expansion of `B` has cardinality at most the corresponding
expansion of `A`.

This is weaker than the full simplicial-order (initial-segment) formulation: it
does not assert a ball exists at every cardinality and gives no
equality/uniqueness cases. Positive natural radii `0 < t` are the exact discrete
ATLAS specialization, with closed expansion `A_t = {x : d_H(x, A) ≤ t}`.

The ATLAS theorem body is a direct proof placeholder; the course text cites Harper
without proof, and the report records that source gap as justified. The declaration
below supplies the Lean proof.

Pinned ATLAS source (definitions and theorem, lines 17--51) at commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`:
<https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/HarperIsoperimetric.lean#L17-L51>
Target metadata (lines 749--753):
<https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/ProbabilisticMethodsInCombinatorics/targets.yaml#L749-L753>
Report entry (lines 3800--3826):
<https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/ProbabilisticMethodsInCombinatorics/report.json#L3800-L3826>

## Depends on

- [Is Ball](../../../InformationTheory/MathlibExt/hamming-expansion/is-ball.md)
- [Expansion](../../../InformationTheory/MathlibExt/hamming-expansion/expansion.md)

## Proof depends on

- [Ball](../../../InformationTheory/MathlibExt/hamming-ball/ball.md)
- [Card ball](../../../InformationTheory/MathlibExt/hamming-ball/card-ball.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.HarperIsoperimetric](../../../../sources/v2/MathlibExt.md)
- L. H. Harper, "Optimal numberings and isoperimetric problems on graphs," Journal of Combinatorial Theory 1(3) (1966), 385–393, DOI 10.1016/S0021-9800(66)80059-5.
