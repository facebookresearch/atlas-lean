---
article_id: af_0b736a8f3c8f88568a9b684e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.sylvester_law_of_inertia
---

# Sylvester Inertia

Sylvester's law of inertia: congruence preserves the inertia triple
of a real symmetric matrix (statement `sylvester-inertia-s1`;
source J. J. Sylvester, *A demonstration of the theorem that every homogeneous quadratic polynomial
is reducible by real orthogonal substitutions to the form of a sum of positive and negative squares*,
Philosophical Magazine Ser. 4, 4(23) (1852), 138-142; Hermitian over `ℝ` is symmetric).

Proof: The spectral theorem from `Mathlib.Analysis.Matrix.Spectrum` identifies each matrix
quadratic form with a weighted sum of squares whose weights are its eigenvalues. Congruence gives
an equivalence of quadratic forms, and signature invariance from
`Mathlib.LinearAlgebra.QuadraticForm.Signature` fixes the positive and negative counts; the zero
count follows by trichotomy.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.SylvesterInertia](../../../../../sources/v2/MathlibExt.md)
