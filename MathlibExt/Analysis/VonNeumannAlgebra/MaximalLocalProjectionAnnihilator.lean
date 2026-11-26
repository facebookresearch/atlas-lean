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
# No nonzero projection annihilates a maximal local family

Let `S` be the maximal orthogonal family of locally vector-dominated nonzero star projections
for a positive bounded functional `ψ`. If a star projection `e∈M` satisfies `ep=0` for every
`p∈S`, then `e=0`.

A nonzero `e` would contain another nonzero locally dominated projection orthogonal to `S`,
contradicting maximality.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Projection annihilating the maximal local family is zero.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a
positive bounded complex-linear functional for the spectral orders. Let `S` be the
constructed maximal set of pairwise orthogonal nonzero star projections, each admitting a
vector `ξ` with `Re ψ(b)≤Re ⟨ξ,bξ⟩` for `0≤b≤p`. For finite `t ⊆ S`, put `P_t=Σ_p∈t p`. if
a star projection `e∈M` satisfies `ep=0` for every `p∈S`, then `e=0`. -/
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
