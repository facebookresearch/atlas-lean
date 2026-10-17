---
article_id: af_df67a00e69ed294f89e29924
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.normalSeq
---

# Normal Seq

Normal second-order number sequence with nonzero integer coefficients:
`u_1 = 1`, `u_2 = a1`, `u_(n+2) = a1 * u_(n+1) + a2 * u_n`.
Concept `jis_sem_341d671b9a22383202776b02`;
source `jis_source_6670e6fe84c03e3ab211c809`.
The Lean totalization sets `u_0 = 0`; source indices `u_1`, `u_2` are unshifted.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NormalNumberSequence](../../../../../sources/v2/MathlibExt.md)
