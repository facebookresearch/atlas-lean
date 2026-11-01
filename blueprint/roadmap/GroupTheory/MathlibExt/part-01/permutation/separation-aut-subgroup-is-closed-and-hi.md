---
article_id: af_cf5e08ac21443a68736a938d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.CameronSeparationGroupWanted.separationAutSubgroup_isClosed_and_highlyHomogeneous
---

# Cameron Separation Group

The separation automorphism group of a countable infinite dense circular order is
closed in the pointwise topology and highly homogeneous (one orbit on `k`-sets for
all `k`).

## Depends on

- [Pointwise Topology](pointwise-topology.md)
- [Is Highly Homogeneous](highly-homogeneous/is-highly-homogeneous.md)
- [Separation Aut Subgroup](separation/separation-aut-subgroup.md)

## Proof depends on

- [Cameron Circular Order Group](circular-order-aut-subgroup-is-closed-an.md)
- [Circular Order](circular-order-aut-subgroup.md)
- [Circular Separates](separation/circular-separates.md)

## Sources

- [MathlibExt, MathlibExt.GroupTheory.Permutation.CameronSeparationGroup](../../../../../sources/v2/MathlibExt.md)
- Daniele A. Gewurz and Francesca Merola, "Sequences realized as Parker vectors of oligomorphic permutation groups," Journal of Integer Sequences 6, `https://cs.uwaterloo.ca/journals/JIS/VOL6/Gewurz/gewurz22.tex`, lines 331–359. The source identifies `D` (also `C*`) as the cyclic-order permutations preserving or reversing the order and calls Cameron's five representatives closed and highly homogeneous, glossed as one orbit on `k`-sets for all `k`. The source cites Peter J. Cameron, "Transitivity of permutation groups on unordered sets," Math. Z. 148 (1976), 127–139. Interpretation boundary: only the `D` representative is asserted, not exhaustive classification, uniqueness, or conjugacy. The explicit countability, infinitude, and circular-density hypotheses select the intended countable dense circular order.
