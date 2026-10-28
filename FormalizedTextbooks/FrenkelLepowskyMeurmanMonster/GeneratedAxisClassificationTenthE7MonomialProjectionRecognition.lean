/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderMonomial

/-! Entire genuine monomial E7 projectors recognize the actual octad, normal pair, and signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The complete actual standard projector diagonal, including every outside zero. -/
def generatedTenthE7ProjectionDiagonal (i : Fin 24) : ℝ :=
  (if i.val < 8 then 2 else 0) - (if i = 4 ∨ i = 5 then 1 else 0)

/-- Every diagonal entry is exactly its whole original coordinate expression. -/
theorem generatedTenth_e7_projection_diagonal_actual (i : Fin 24) :
    generatedTenthE7XiProjection.map (Int.castRingHom ℝ) i i =
      generatedTenthE7ProjectionDiagonal i := by
  fin_cases i <;> norm_num [generatedTenthE7XiProjection, generatedTenthE7ProjectionDiagonal]

/-- The complete diagonal recognizes membership in the original enclosing octad. -/
theorem generatedTenth_e7_projection_diagonal_octad (i : Fin 24) :
    generatedTenthE7ProjectionDiagonal i ≠ 0 ↔ i.val < 8 := by
  fin_cases i <;> norm_num [generatedTenthE7ProjectionDiagonal]

/-- The complete diagonal recognizes both original normal coordinates exactly. -/
theorem generatedTenth_e7_projection_diagonal_normal (i : Fin 24) :
    generatedTenthE7ProjectionDiagonal i = 1 ↔ i = 4 ∨ i = 5 := by
  fin_cases i <;> norm_num [generatedTenthE7ProjectionDiagonal]

private theorem monomial_single (c : golayCode) (p : golayAutomorphismSubgroup) (j : Fin 24) :
    (golayMonomialPair (c, p)).val (Pi.single j 1) =
      qSign (c.val (p.val j)) • Pi.single (p.val j) 1 := by
  funext i
  rw [golayMonomialPair_apply]
  by_cases hi : i = p.val j
  · subst i
    simp [p.val.symm_apply_apply]
  · have hpre : p.val.symm i ≠ j := by
      intro h
      exact hi ((p.val.symm_apply_eq).mp h)
    simp [hi, hpre]

/-- Full projector commutation binds every original signed matrix entry. -/
theorem generatedTenth_e7_monomial_projection_entry (c : golayCode)
    (p : golayAutomorphismSubgroup)
    (he : ∀ x : Fin 24 → ℝ,
      (golayMonomialPair (c, p)).val (generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ x) =
        generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ
          (golayMonomialPair (c, p)).val x) (i j : Fin 24) :
    qSign (c.val (p.val i)) * generatedTenthE7XiProjection.map (Int.castRingHom ℝ) i j =
      generatedTenthE7XiProjection.map (Int.castRingHom ℝ) (p.val i) (p.val j) *
        qSign (c.val (p.val j)) := by
  have h := congrFun (he (Pi.single j 1)) (p.val i)
  rw [golayMonomialPair_apply, p.val.symm_apply_apply, Matrix.mulVec_single_one,
    monomial_single, Matrix.mulVec_smul, Matrix.mulVec_single_one] at h
  simpa only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply, mul_comm] using h

/-- Every actual monomial projector fixer preserves the entire actual diagonal. -/
theorem generatedTenth_e7_monomial_projection_diagonal (c : golayCode)
    (p : golayAutomorphismSubgroup)
    (he : ∀ x : Fin 24 → ℝ,
      (golayMonomialPair (c, p)).val (generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ x) =
        generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ
          (golayMonomialPair (c, p)).val x) (i : Fin 24) :
    generatedTenthE7ProjectionDiagonal i = generatedTenthE7ProjectionDiagonal (p.val i) := by
  have h := generatedTenth_e7_monomial_projection_entry c p he i i
  rw [generatedTenth_e7_projection_diagonal_actual,
    generatedTenth_e7_projection_diagonal_actual] at h
  have hn : qSign (c.val (p.val i)) ≠ 0 := by
    intro hz
    have hs := qSign_sq (c.val (p.val i))
    rw [hz, zero_mul] at hs
    norm_num at hs
  apply mul_left_cancel₀ hn
  simpa only [mul_comm] using h

/-- Full actual projector fixation preserves every octad and normal-pair membership. -/
theorem generatedTenth_e7_monomial_projection_support (c : golayCode)
    (p : golayAutomorphismSubgroup)
    (he : ∀ x : Fin 24 → ℝ,
      (golayMonomialPair (c, p)).val (generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ x) =
        generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ
          (golayMonomialPair (c, p)).val x) (i : Fin 24) :
    ((p.val i).val < 8 ↔ i.val < 8) ∧
      (p.val i = 4 ∨ p.val i = 5 ↔ i = 4 ∨ i = 5) := by
  have h := generatedTenth_e7_monomial_projection_diagonal c p he i
  constructor
  · rw [← generatedTenth_e7_projection_diagonal_octad,
      ← generatedTenth_e7_projection_diagonal_octad, ← h]
  · rw [← generatedTenth_e7_projection_diagonal_normal,
      ← generatedTenth_e7_projection_diagonal_normal, ← h]

private theorem original_q_sign_injective : Function.Injective qSign := by
  intro a b h
  have hs : qSign (a + b) = 1 := by
    rw [qSign_add, h, qSign_sq]
  have hz := (qSign_eq_one_iff _).mp hs
  have he := eq_neg_of_add_eq_zero_left hz
  simpa only [ZMod.neg_eq_self_mod_two] using he

/-- Entire original off-diagonal fixation forces the actual two normal signs to agree. -/
theorem generatedTenth_e7_monomial_projection_signs (c : golayCode)
    (p : golayAutomorphismSubgroup)
    (he : ∀ x : Fin 24 → ℝ,
      (golayMonomialPair (c, p)).val (generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ x) =
        generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ
          (golayMonomialPair (c, p)).val x) : c.val 4 = c.val 5 := by
  have h4 := (generatedTenth_e7_monomial_projection_support c p he 4).2.mpr
    (Or.inl rfl)
  have h5 := (generatedTenth_e7_monomial_projection_support c p he 5).2.mpr
    (Or.inr rfl)
  have h := generatedTenth_e7_monomial_projection_entry c p he 4 5
  rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5
  · exact False.elim ((by decide : (4 : Fin 24) ≠ 5)
      (p.val.injective (h4.trans h5.symm)))
  · rw [h4, h5] at h
    norm_num [generatedTenthE7XiProjection] at h
    apply original_q_sign_injective
    linarith
  · rw [h4, h5] at h
    norm_num [generatedTenthE7XiProjection] at h
    apply original_q_sign_injective
    linarith
  · exact False.elim ((by decide : (4 : Fin 24) ≠ 5)
      (p.val.injective (h4.trans h5.symm)))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
