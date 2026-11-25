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
    Γ.map (fun r : ℝ => (r : ℂ)) ⊙ Matrix.gram ℂ ψ = 0 := by
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
      (Matrix.gram ℂ ψ) a b = inner ℂ (ψ a) (ψ b) := fun a b => rfl
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
    Matrix.gram ℂ (fun i : Fin 2 => EuclideanSpace.single i (1 : ℂ)) = 1 := by
  ext x y
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  fin_cases x <;> fin_cases y <;> simp_all [EuclideanSpace.inner_single_left]

/-- Two-point label function: `false` at `0`, `true` at `1`. -/
def fEx : Fin 2 → Bool := fun x => x = 1

/-- Two-point swap matrix. -/
def ΓEx : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- Two-point state family: the standard orthonormal basis. -/
noncomputable def ψEx : Fin 2 → EuclideanSpace ℂ (Fin 2) :=
  fun i => EuclideanSpace.single i (1 : ℂ)

/-- Output-component decomposition: the correct component holds the state. -/
noncomputable def uEx : Bool → Fin 2 → EuclideanSpace ℂ (Fin 2) :=
  fun b x => if b = fEx x then ψEx x else 0

/-- Unit coefficient vector supported at `0`. -/
def αEx : Fin 2 → ℂ := ![1, 0]

/-- Decomposition of the two-point states into output components. -/
theorem hdecompEx : ∀ x, ψEx x = uEx false x + uEx true x := by
  intro x
  cases hfx : fEx x <;> simp [uEx, hfx]

/-- Orthogonality of opposite output components on the example. -/
theorem horthoEx : ∀ x y, inner ℂ (uEx false x) (uEx true y) = 0 := by
  have hf0 : fEx 0 = false := by decide
  have hf1 : fEx 1 = true := by decide
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  intro x y
  fin_cases x <;> fin_cases y <;>
    simp_all [uEx, ψEx, EuclideanSpace.inner_single_left]

/-- The two-point states are unit vectors. -/
theorem hunitEx : ∀ x, ‖ψEx x‖ = 1 := by
  intro x
  simp [ψEx]

/-- The two-point example has zero error. -/
theorem herrEx : ∀ x, ‖uEx (!fEx x) x‖ ^ 2 ≤ 0 := by
  intro x
  have hz : uEx (!fEx x) x = 0 := by
    cases hfx : fEx x <;> simp [uEx, hfx]
  rw [hz, norm_zero]
  norm_num

/-- The swap matrix is an adversary matrix for the example labels. -/
theorem hΓEx : IsAdversaryMatrix fEx ΓEx := swap_isAdversaryMatrix

/-- The example coefficient vector is normalized. -/
theorem hαEx : ∑ x, ‖αEx x‖ ^ 2 = 1 := by
  rw [Fin.sum_univ_two]
  simp [αEx]

/-- The example labels differ across the two points. -/
theorem hxyEx : fEx 0 ≠ fEx 1 := by decide

/-- Smoke test: the pairwise bound on the two-point example. -/
theorem smoke_norm_inner_two_point :
    ‖inner ℂ (ψEx 0) (ψEx 1)‖ ≤ 2 * Real.sqrt (0 * (1 - 0)) :=
  norm_inner_le_of_ne fEx ψEx uEx hdecompEx horthoEx hunitEx (le_refl 0)
    (by norm_num) herrEx hxyEx

/-- Smoke test: the quadratic-form bound on the two-point example. -/
theorem smoke_quadForm_two_point :
    ‖∑ x, ∑ y, ((ΓEx x y : ℝ) : ℂ) * star (αEx x) * αEx y *
      inner ℂ (ψEx x) (ψEx y)‖ ≤
        2 * Real.sqrt (0 * (1 - 0)) *
          ‖ΓEx.map (fun r : ℝ => (r : ℂ))‖ :=
  adversary_quadForm_le fEx ψEx uEx hdecompEx horthoEx hunitEx (le_refl 0)
    (by norm_num) herrEx ΓEx hΓEx αEx hαEx

/-- Smoke test: the operator-norm bound on the two-point example. -/
theorem smoke_hadamard_two_point :
    ‖ΓEx.map (fun r : ℝ => (r : ℂ)) ⊙ Matrix.gram ℂ ψEx‖ ≤
      2 * Real.sqrt (0 * (1 - 0)) *
        ‖ΓEx.map (fun r : ℝ => (r : ℂ))‖ :=
  norm_hadamard_gramMatrix_le fEx ψEx uEx hdecompEx horthoEx hunitEx
    (le_refl 0) (by norm_num) herrEx ΓEx hΓEx

#print axioms inner_eq_cross_terms
#print axioms norm_inner_le_of_ne
#print axioms adversary_quadForm_le
#print axioms norm_hadamard_gramMatrix_le

end Cslib.AdversaryOutputConditionTests
