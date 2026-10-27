---
article_id: af_3c4c4babf7e7da86d3838dcb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Submodule.exists_smith_normal_form_dvd_chain
---

# Exists smith normal form dvd chain

Any submodule `N` of a finite free module `M` over a PID has a Smith normal form: bases
`bM` of `M` and `bN` of `N` with `bN i = a i • bM i`, nonzero coefficients `a i`, and the
invariant-factor divisibility chain `a i ∣ a (i+1)`. This refines
`Submodule.exists_smith_normal_form_of_le`, which gives no divisibility chain.
`MathlibExt.LinearAlgebra.SmithNormalFormWanted.smithNormalForm` is the source-shaped form.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.SmithNormalForm](../../../../sources/v2/MathlibExt.md)
