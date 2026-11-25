/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.CanonicalEmbedding.DualIdealLattice

/-! # Consumers for the dual of an ideal lattice -/

namespace NumberFieldMixedEmbeddingDualIdealLatticeTest

open NumberField NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

/-- The exact source statement, with the original binders. -/
public theorem exactSource (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (LinearMap.BilinForm.dualSubmodule (Algebra.traceForm ℝ (mixedSpace K)).flip
        (mixedEmbedding.idealLattice K I) : Set (mixedSpace K))
      = mixedEmbedding K '' (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Set K) :=
  NumberField.mixedEmbedding.coe_dualSubmodule_flip_traceForm_idealLattice K I

/-- Boundary example: for the unit ideal, the dual lattice is the mixed embedding
of the trace dual of `1`, so the statement is not vacuous at `I = 1`. -/
public theorem exactSource_one (K : Type*) [Field K] [NumberField K] :
    (LinearMap.BilinForm.dualSubmodule (Algebra.traceForm ℝ (mixedSpace K)).flip
        (mixedEmbedding.idealLattice K 1) : Set (mixedSpace K))
      = mixedEmbedding K '' (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) : Set K) :=
  NumberField.mixedEmbedding.coe_dualSubmodule_flip_traceForm_idealLattice K 1

end NumberFieldMixedEmbeddingDualIdealLatticeTest
