/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpinEnvelope

/-! The genuine inverse spin-label permutation proves zero outside a complete sparse monomial support envelope. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Original twelve-bit labels and their physical spin coefficients are explicitly inverse bijections. -/
def generatedAxisGlobalOddSpinLabelEquiv : Fin 4096 ≃ SpinIndex where
  toFun := golayLabelCoefficients
  invFun := generatedAxisGlobalSpinLabel
  left_inv := generatedAxisGlobalSpinLabel_coeff
  right_inv := generatedAxisGlobalSpinLabel_decode

/-- Each original monomial pullback letter is the actual code equivalence in its stated direction. -/
def generatedAxisGlobalOddMonomialPullLetterEquiv (l : Fin 2 × Bool) : SpinIndex ≃ SpinIndex :=
  if l.2 then (monsterSourcePermutationCode l.1).toEquiv else
    (monsterSourcePermutationCode l.1).symm.toEquiv

/-- Literal composition of all genuine original monomial label pullbacks. -/
def generatedAxisGlobalOddMonomialPullEquiv : List (Fin 2 × Bool) → SpinIndex ≃ SpinIndex
  | [] => Equiv.refl _
  | l :: w => (generatedAxisGlobalOddMonomialPullLetterEquiv l).trans
      (generatedAxisGlobalOddMonomialPullEquiv w)

/-- Every source-word pullback label is the actual image under the composed genuine equivalence. -/
theorem generatedAxisGlobalOddMonomialPullEquiv_actual (w : List (Fin 2 × Bool)) (t : SpinIndex) :
    generatedAxisGlobalOddMonomialPullEquiv w t = (generatedFourthMonomialWordPull w t).2 := by
  induction w generalizing t with
  | nil => rfl
  | cons l w ih =>
    change generatedAxisGlobalOddMonomialPullEquiv w
      (generatedAxisGlobalOddMonomialPullLetterEquiv l t) = _
    rw [ih]
    have hl : generatedAxisGlobalOddMonomialPullLetterEquiv l t =
        generatedFourthMonomialPullLetter l t := by
      rcases l with ⟨k, b⟩
      cases b <;> rfl
    rw [hl]
    rfl

/-- The exact original pullback is also a genuine permutation of all 4096 physical binary labels. -/
def generatedAxisGlobalOddMonomialLabelEquiv (w : List (Fin 2 × Bool)) : Fin 4096 ≃ Fin 4096 :=
  generatedAxisGlobalOddSpinLabelEquiv.trans
    ((generatedAxisGlobalOddMonomialPullEquiv w).trans generatedAxisGlobalOddSpinLabelEquiv.symm)

/-- The finite-label equivalence retains the complete genuine source-word label pullback. -/
theorem generatedAxisGlobalOddMonomialLabelEquiv_actual (w : List (Fin 2 × Bool)) (k : Fin 4096) :
    generatedAxisGlobalOddMonomialLabelEquiv w k =
      generatedAxisGlobalSpinLabel (generatedFourthMonomialWordPull w (golayLabelCoefficients k)).2 := by
  change generatedAxisGlobalSpinLabel
    (generatedAxisGlobalOddMonomialPullEquiv w (golayLabelCoefficients k)) = _
  rw [generatedAxisGlobalOddMonomialPullEquiv_actual]

/-- Every omitted output label has zero genuine input coefficient under the complete source pullback. -/
theorem generatedAxisGlobalOddMonomialSpin_zero_outside
    (w : List (Fin 2 × Bool)) (u : Fin 4096 → ℤ) (E : Fin 4096 → Bool)
    (hc : ∀ m : Fin 4096, u m ≠ 0 → E ((generatedAxisGlobalOddMonomialLabelEquiv w).symm m) = true)
    (k : Fin 4096) (hk : E k = false) :
    generatedAxisGlobalOddMonomialSpinInteger w u k = 0 := by
  have hz : u (generatedAxisGlobalOddMonomialLabelEquiv w k) = 0 := by
    by_contra hh
    have he := hc _ hh
    rw [Equiv.symm_apply_apply, hk] at he
    contradiction
  unfold generatedAxisGlobalOddMonomialSpinInteger
  dsimp only
  rw [← generatedAxisGlobalOddMonomialLabelEquiv_actual, hz, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
