/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.AdversaryOutputCondition

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator BigOperators InnerProductSpace
open Cslib.AdversaryOutputCondition

namespace Cslib.AdversaryOutputConditionTests

set_option autoImplicit false

/-- At zero error, the Hadamard product in the output condition vanishes. -/
theorem hadamard_eq_zero_of_eps_zero {X E : Type*}
    [Fintype X] [DecidableEq X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : X → Bool) (ψ : X → E) (u : Bool → X → E)
    (hdecomp : ∀ x, ψ x = u false x + u true x)
    (hortho : ∀ x y, inner ℂ (u false x) (u true y) = 0)
    (hunit : ∀ x, ‖ψ x‖ = 1)
    (herr : ∀ x, ‖u (!f x) x‖ ^ 2 ≤ 0)
    (Γ : Matrix X X ℝ) (hΓ : IsAdversaryMatrix f Γ) :
    Γ.map (fun r : ℝ => (r : ℂ)) ⊙ gramMatrix ψ = 0 := by
  have hzero : ∀ z, u (!f z) z = 0 := by
    intro z
    have h2 : ‖u (!f z) z‖ ^ 2 = 0 :=
      le_antisymm (herr z) (sq_nonneg _)
    have h0 : ‖u (!f z) z‖ = 0 := sq_eq_zero_iff.mp h2
    simpa using h0
  have hhad : ∀ (A B : Matrix X X ℂ) (a b : X),
      (A ⊙ B) a b = A a b * B a b := fun A B a b => rfl
  have hmap : ∀ (a b : X),
      (Γ.map (fun r : ℝ => (r : ℂ))) a b = ((Γ a b : ℝ) : ℂ) :=
    fun a b => rfl
  have hgram : ∀ (a b : X),
      (gramMatrix ψ) a b = inner ℂ (ψ a) (ψ b) := fun a b => rfl
  have hzeroM : ∀ (a b : X), (0 : Matrix X X ℂ) a b = 0 :=
    fun a b => rfl
  ext a b
  rw [hhad, hmap, hgram, hzeroM]
  by_cases hxy : f a = f b
  · rw [hΓ.2 a b hxy]
    simp
  · have hT := inner_eq_cross_terms f ψ u hdecomp hortho hxy
    have hfx : f a = !f b := by
      cases h1 : f a <;> cases h2 : f b <;> simp_all
    have hfy : f b = !f a := by
      cases h1 : f a <;> cases h2 : f b <;> simp_all
    have e1 : inner ℂ (u (f a) a) (u (f a) b) = 0 := by
      have hz : u (f a) b = 0 := by
        rw [hfx]
        exact hzero b
      simp [hz]
    have e2 : inner ℂ (u (f b) a) (u (f b) b) = 0 := by
      have hz : u (f b) a = 0 := by
        rw [hfy]
        exact hzero a
      simp [hz]
    have hG : inner ℂ (ψ a) (ψ b) = 0 := by
      rw [hT, e1, e2, add_zero]
    rw [hG, mul_zero]

/-- The two-by-two swap matrix is an adversary matrix for the identity
Boolean function on `Fin 2`. -/
theorem swap_isAdversaryMatrix :
    IsAdversaryMatrix (fun x : Fin 2 => x = 1)
      !![0, 1; 1, 0] := by
  refine ⟨?_, ?_⟩
  · unfold Matrix.IsSymm
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  · intro x y h
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    fin_cases x <;> fin_cases y <;> simp_all

/-- The Gram matrix of the standard orthonormal basis is the identity. -/
theorem gramMatrix_single :
    gramMatrix (fun i : Fin 2 => EuclideanSpace.single i (1 : ℂ)) = 1 := by
  ext x y
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  fin_cases x <;> fin_cases y <;> simp_all [gramMatrix, EuclideanSpace.inner_single_left]

#print axioms inner_eq_cross_terms
#print axioms norm_inner_le_of_ne
#print axioms norm_hadamard_gram_factor_le
#print axioms adversary_quadForm_le
#print axioms norm_hadamard_gramMatrix_le

end Cslib.AdversaryOutputConditionTests
