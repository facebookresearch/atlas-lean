---
article_id: af_f7a3943d95d7016b37714479
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.meshPatternCount_eq_factorial_mul_rStirlingNumber
---

# Mesh Pattern Count eq factorial mul r Stirling Number

The number of permutations having exactly `j` matches of the extended mesh pattern of
parameter `k` equals `(k - 1)!` times the corresponding `r`-Stirling number.

## Depends on

- [R Stirling First](../../part-07/rstirling-first-alternating-expansion/r-stirling-first.md)

## Proof depends on

- [Match Pred](../mesh-pattern-stirling-recursion/match-pred.md)
- [Zero Pred](../mesh-pattern-stirling-recursion/zero-pred.md)
- [Mesh N](../mesh-pattern-stirling-recursion/mesh-n.md)
- [Mesh Pattern Count eq factorial mul r Stirling Number general](mesh-pattern-count-eq-factorial-mul-r-st.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.MeshPatternRStirling](../../../../../../../sources/v2/MathlibExt.md)
- Matt Davis, "Quadrant Marked Mesh Patterns and the r-Stirling Numbers", Journal of Integer Sequences 18 (2015), Article 15.10.1, Theorem `thm:rstir`, line 201, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Davis/davis3.tex>.
