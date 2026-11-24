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

public import MathlibExt.Analysis.VonNeumannAlgebra.MaximalLocalProjectionFamily
public import Mathlib.Analysis.CStarAlgebra.Projection

/-!
# No nonzero star projection annihilates the actual maximal local family

For a nonzero original projection e, the actual local construction supplies
a nonzero locally dominated projection F≤e. If e annihilates every member
of the constructed maximal family, so does F. Selfadjointness supplies the
reverse zero products; inserting F contradicts actual maximality. The
finite-cutoff supremum and its limiting behavior remain separate next data.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An original star projection orthogonal to the actual maximal family must be zero. -/
theorem maximalLocalProjectionFamily_annihilator_eq_zero (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ) (e : M), IsStarProjection e →
      (∀ p ∈ (maximalLocalProjectionFamily M ψ).val, e * p = 0) → e = 0 := by
  classical
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : LE M := (CStarAlgebra.spectralOrder M).toLE
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ e he hannihilator
  by_contra hne
  let S := maximalLocalProjectionFamily M ψ
  let q := localVectorDominatedProjection M ψ e he hne
  let F : M := q.val.1
  have hF : IsStarProjection F := q.property.1
  have hFne : F ≠ 0 := q.property.2.1
  have hFe : F * e = F := (hF.le_iff_mul_eq_left he).mp q.property.2.2.1
  have hFS (p : M) (hp : p ∈ S.val) : F * p = 0 := by
    calc
      F * p = (F * e) * p := by rw [hFe]
      _ = F * (e * p) := mul_assoc F e p
      _ = 0 := by rw [hannihilator p hp, mul_zero]
  have hSF (p : M) (hp : p ∈ S.val) : p * F = 0 := by
    have h := congrArg star (hFS p hp)
    simpa only [star_mul, hF.isSelfAdjoint.star_eq,
      (S.property.1 p hp).1.isSelfAdjoint.star_eq, star_zero] using h
  have hFnot : F ∉ S.val := by
    intro hmem
    have hz := hFS F hmem
    rw [hF.isIdempotentElem.eq] at hz
    exact hFne hz
  have heligible : ∀ p ∈ insert F S.val, IsStarProjection p ∧ p ≠ 0 ∧ ∃ ξ : H,
      ∀ b : PositiveElement M,
        @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) p →
        (ψ.toContinuousLinearMap (b : M)).re ≤ (vectorFunctional M ξ ξ (b : M)).re := by
    intro p hp
    rcases hp with rfl | hp
    · exact ⟨hF, hFne, q.val.2, q.property.2.2.2⟩
    · exact S.property.1 p hp
  have hpairwise : (insert F S.val).Pairwise (fun p t => p * t = 0) := by
    intro p hp t ht hpt
    rcases hp with rfl | hp
    · rcases ht with rfl | ht
      · exact (hpt rfl).elim
      · exact hFS t ht
    · rcases ht with rfl | ht
      · exact hSF p hp
      · exact S.property.2.1 hp ht hpt
  have hinsert : insert F S.val ⊆ S.val :=
    S.property.2.2 (insert F S.val) heligible hpairwise (Set.subset_insert F S.val)
  exact hFnot (hinsert (Set.mem_insert F S.val))

end

end VonNeumannAlgebra
