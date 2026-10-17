---
article_id: af_a78975cfc204d13f16c6b38b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.SmithNormalFormWanted.smithNormalForm
---

# Smith Normal Form

Any submodule of a finite free module over a PID has a Smith normal form with invariant-factor
divisibility chain `a i ∣ a (i+1)`, the refinement beyond the existing Mathlib diagonal-basis
Smith-form API.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exists smith normal form dvd chain](exists-smith-normal-form-dvd-chain.md)

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.SmithNormalForm](../../../../sources/v2/MathlibExt.md)
- H. J. S. Smith, Phil. Trans. R. Soc. Lond. 151 (1861), 293-326, DOI 10.1098/RSTL.1861.0016. It is `Submodule.exists_smith_normal_form_dvd_chain`, kept under the source's name. Proves `Wanted` entry `smithNormalForm`.
