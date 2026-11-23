/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.FiniteLiesOver

/-!
# Finite-place completion instances over a base completion

For finite places `v` of `K` and `w` of `L` with `w` lying over `v`,
this file supplies the `Algebra`, `IsScalarTower`, and `ContinuousSMul`
instances for the canonical map between adic completions, mirroring
`NumberField.LiesOver` for infinite places.

## ATLAS source map

ATLAS NumberTheoryI item N265, Theorem 13.5, Section 13.1; primary source:
module `Atlas.NumberTheoryI.GlobalFields`,
file `v1/Atlas/NumberTheoryI/code/GlobalFields.lean`,
declaration `TensorProductDecomposition.theorem_13_5_finite_place_Kv`,
lines 1152--1211:
<https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L1152-L1211>

For every finite place `w` over `v`, the source creates the target scalar
structure `Algebra (v.adicCompletion K) (w.val.adicCompletion L)` from
`(completionEmbedding_finite v w.val w.prop).toAlgebra` at lines 1156--1158
and 1170--1172. This module's scoped `Algebra` instance uses the
source-faithful canonical map `adicCompletionMap v w` from the prerequisite
module, whose source map identifies it with that completion embedding.
The scoped `IsScalarTower` records compatibility with the original `K`-algebra
maps, the scalar compatibility used in the source's `hf_alg` argument at
lines 1181--1198 to upgrade the ring equivalence to an algebra equivalence
over `v.adicCompletion K`. The scoped `ContinuousSMul` records continuity of this
scalar action for downstream topological arguments; it is supporting API and
is not itself a separate clause of Theorem 13.5. This stage supplies only
those reusable instances and does not construct or prove the full
tensor-product equivalence.
-/

@[expose] public section

namespace NumberField.LiesOver

open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
variable {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
variable {w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)}
variable [hvw : w.asIdeal.LiesOver v.asIdeal]

noncomputable scoped instance instAlgebraAdicCompletionRingOfIntegers_mathlibExt :
    Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (adicCompletionMap v w).toAlgebra

scoped instance instIsScalarTowerAdicCompletionRingOfIntegers_mathlibExt :
    IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rw [RingHom.algebraMap_toAlgebra]
  exact (adicCompletionMap_algebraMap v w x).symm

scoped instance instContinuousSMulAdicCompletionRingOfIntegers_mathlibExt :
    ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) where
  continuous_smul :=
    ((continuous_adicCompletionMap v w).comp continuous_fst).mul continuous_snd

end NumberField.LiesOver
