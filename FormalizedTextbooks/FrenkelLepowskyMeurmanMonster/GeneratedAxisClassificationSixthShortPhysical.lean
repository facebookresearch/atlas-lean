/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialShortPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitMonomialActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralizerGeometryShortLines

/-! Actual physical short-vector transport determines the genuine preferred-label permutation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A physical equality up to sign identifies the actual permuted short label. -/
theorem generatedSixth_short_permutation_of_vector (e : leechIsomSubgroup)
    (r s : GriessShortIndex)
    (h : e.val (griessShortVector r) = griessShortVector s ∨
      e.val (griessShortVector r) = -griessShortVector s) :
    griessShortPermutation e r = s := by
  apply centralizer_shortVector_sign_unique
  rcases griessShortPermutation_vector e r with h₁ | h₁ <;> rcases h with h₂ | h₂
  · exact Or.inl (h₁.symm.trans h₂)
  · exact Or.inr (h₁.symm.trans h₂)
  · right
    funext i
    have ha := congrFun h₁ i
    have hb := congrFun h₂ i
    simp only [Pi.neg_apply] at ha hb ⊢
    linarith
  · left
    funext i
    have ha := congrFun h₁ i
    have hb := congrFun h₂ i
    simp only [Pi.neg_apply] at ha hb ⊢
    linarith

/-- The four original monomial spatial words use exactly the frozen coordinate input arrays. -/
theorem generatedSixth_monomial_physical_apply (k : Fin 4) (x : Fin 24 → ℝ) (i : Fin 24) :
    (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2.val x i =
      x (sixthFrameOrbitSpatialInput (Fin.natAdd 10 (Fin.castAdd 2 k)) i) := by
  have h := sixthFrameOrbit_permutation_apply (Fin.castAdd 2 k) x i
  have he : sixthFrameOrbitMonomialIsometry (Fin.natAdd 10 (Fin.castAdd 2 k)) =
      (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2 := by
    fin_cases k <;> rfl
  rw [he] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
