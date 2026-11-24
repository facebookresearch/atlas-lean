/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.VonNeumannAlgebra.MaximalLocalCutoffProjection
public import MathlibExt.Analysis.VonNeumannAlgebra.MaximalLocalProjectionAnnihilator
public import Mathlib.Analysis.CStarAlgebra.Projection

/-!
# The actual maximal-family finite-cutoff supremum is the original identity

Each original family member is the value of its actual singleton cutoff,
so it lies below the constructed cutoff supremum s. Both are genuine star
projections; therefore s*p=p for every family member p. Its star-projection
complement 1-s annihilates the entire actual family. The proved original
maximal-family annihilator law gives 1-s=0 and hence s=1. No identity limit,
LUB, projection or normality certificate is supplied as an input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight
open scoped BigOperators

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual maximal-family finite positive cutoffs have original identity as their constructed supremum. -/
theorem maximalLocalCutoffSupremum_eq_one (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ),
      ((maximalLocalCutoffSupremum M ψ).val : M) = 1 := by
  classical
  let sourceOrder : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder M := sourceOrder
  let : Preorder M := sourceOrder.toPreorder
  let : LE M := sourceOrder.toLE
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ
  let S := maximalLocalProjectionFamily M ψ
  let P := maximalLocalPositiveFiniteCutoffs M ψ
  let s := maximalLocalCutoffSupremum M ψ
  have hs : IsStarProjection (s.val : M) := maximalLocalCutoffSupremum_isStarProjection M ψ
  have hmember (p : M) (hp : p ∈ S.val) : p ≤ (s.val : M) := by
    let i : S.val := ⟨p, hp⟩
    have hvalue : (P.val {i} : M) = p := by
      rw [(maximalLocalPositiveFiniteCutoffs_value M ψ) {i}]
      change (∑ j ∈ ({i} : Finset S.val), (j.val : M)) = (i.val : M)
      exact Finset.sum_singleton (fun j : S.val => (j.val : M)) i
    have h := (maximalLocalCutoffSupremum_isLUB M ψ).1 (Set.mem_range_self ({i} : Finset S.val))
    rw [hvalue] at h
    exact h
  have hcomplement : (1 : M) - (s.val : M) = 0 := by
    apply maximalLocalProjectionFamily_annihilator_eq_zero M ψ (1 - (s.val : M)) hs.one_sub
    intro p hp
    have hprod : (s.val : M) * p = p :=
      ((S.property.1 p hp).1.le_iff_mul_eq_right hs).mp (hmember p hp)
    rw [sub_mul, one_mul, hprod, sub_self]
  exact (sub_eq_zero.mp hcomplement).symm

end

end VonNeumannAlgebra
