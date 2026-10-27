---
article_id: af_f4069f3b525f6752c12d9ba2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.InnerProductSpace.BoundedSelfAdjointSpectralWanted.boundedSelfAdjoint_spectral_multiplication
---

# Bounded Self Adjoint spectral multiplication

Spectral theorem for bounded self-adjoint operators, multiplication-operator form: a
self-adjoint `T : E →L[ℂ] E` is unitarily equivalent to multiplication by a real-valued
measurable function on some `L²`. Sources: Mathlib
`Mathlib/Analysis/InnerProductSpace/Spectrum.lean` TODO (spectral theory for bounded
self-adjoint operators); W. Rudin, Functional Analysis, 2nd ed., Ch. 12.

Proof: Scalar measures from the continuous functional calculus identify each cyclic subspace with an
`L²` space. A maximal orthogonal family of cyclic subspaces is then assembled over a disjoint-union
measure, where the spectral coordinate acts by multiplication.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exists spectral Measure](exists-spectral-measure.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral](../../../../../../sources/v2/MathlibExt.md)
