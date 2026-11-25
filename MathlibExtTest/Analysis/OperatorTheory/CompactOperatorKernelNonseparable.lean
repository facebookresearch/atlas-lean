/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.OperatorTheory.CompactOperatorKernelNonseparable
import MathlibExt.Analysis.InnerProductSpace.SeparableHilbertCountableBasis
import Mathlib.Analysis.Real.Cardinality

/-! # Tests for `MathlibExt.Analysis.OperatorTheory.CompactOperatorKernelNonseparable` -/

namespace MathlibExtTest.Analysis.OperatorTheory.CompactOperatorKernelNonseparable

open TopologicalSpace
open scoped lp
open MathlibExt.Analysis.OperatorTheory.CompactOperatorKernelNonseparableWanted

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- The zero operator is compact and its kernel is the whole space.
example (hH : ¬ SeparableSpace H) : ¬ SeparableSpace (⊤ : Submodule ℂ H) := by
  have h := not_separableSpace_ker_of_isCompactOperator_of_not_separableSpace (0 : H →L[ℂ] H) hH
    isCompactOperator_zero
  rwa [show (0 : H →L[ℂ] H).ker = ⊤ by simp] at h

-- A rank-one operator `x ↦ ⟪u, x⟫ • v` factors through `ℂ`, so it is compact; its kernel is not
-- separable.
example (hH : ¬ SeparableSpace H) (u v : H) :
    ¬ SeparableSpace (ContinuousLinearMap.toSpanSingleton ℂ v ∘L innerSL ℂ u).ker := by
  have hv : IsCompactOperator (ContinuousLinearMap.toSpanSingleton ℂ v) :=
    isCompactOperator_of_locallyCompactSpace_rng _
  exact not_separableSpace_ker_of_isCompactOperator_of_not_separableSpace _ hH
    (hv.comp_clm (innerSL ℂ u))

-- A compact operator on a nonseparable Hilbert space is not injective.
example (A : H →L[ℂ] H) (hH : ¬ SeparableSpace H) (hA : IsCompactOperator A) :
    ¬ Function.Injective A := fun hinj =>
  not_separableSpace_ker_of_isCompactOperator_of_not_separableSpace A hH hA <| by
    rw [show A.ker = ⊥ from LinearMap.ker_eq_bot.2 hinj]
    infer_instance

-- Equivalently, `0` is an eigenvalue: some nonzero vector lies in the kernel.
example (A : H →L[ℂ] H) (hH : ¬ SeparableSpace H) (hA : IsCompactOperator A) :
    ∃ x : H, x ≠ 0 ∧ A x = 0 := by
  have hker : A.ker ≠ ⊥ := fun h =>
    not_separableSpace_ker_of_isCompactOperator_of_not_separableSpace A hH hA (h ▸ inferInstance)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨x, hx0, hx⟩

end General

-- `ℓ²(ℝ, ℂ)` is not separable, since its standard Hilbert basis is an orthonormal family indexed
-- by the uncountable `ℝ`; so every compact operator on it has a nonseparable kernel.
example (A : ℓ²(ℝ, ℂ) →L[ℂ] ℓ²(ℝ, ℂ)) (hA : IsCompactOperator A) :
    ¬ SeparableSpace A.ker := by
  refine not_separableSpace_ker_of_isCompactOperator_of_not_separableSpace A (fun _ => ?_) hA
  exact Cardinal.not_countable_real (Set.countable_univ_iff.2
    (MathlibExt.Analysis.InnerProductSpace.SeparableHilbertCountableBasis.countable_of_orthonormal
      (default : HilbertBasis ℝ ℂ ℓ²(ℝ, ℂ)).orthonormal))

-- The hypothesis that `H` is not separable cannot be dropped: on `ℂ`, the identity is compact
-- and its kernel `⊥` is separable.
example : IsCompactOperator (1 : ℂ →L[ℂ] ℂ) ∧ SeparableSpace (1 : ℂ →L[ℂ] ℂ).ker :=
  ⟨isCompactOperator_of_locallyCompactSpace_rng _, inferInstance⟩

end MathlibExtTest.Analysis.OperatorTheory.CompactOperatorKernelNonseparable
