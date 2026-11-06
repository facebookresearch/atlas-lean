/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddMonomialEnvelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSignEnvelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonTensorFactors

/-! Exact original signed translations carry complete finite support envelopes bijectively. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The original Q pullback is the actual translation of original spin labels. -/
def generatedAxisGlobalOddQSpinLabelEquiv (q : Q) : Fin 4096 ≃ Fin 4096 :=
  generatedAxisGlobalOddSpinLabelEquiv.trans
    ((Equiv.addRight (spinTranslation q)).trans generatedAxisGlobalOddSpinLabelEquiv.symm)

/-- The exact original coefficient label is the genuine bijective pullback. -/
theorem generatedAxisGlobalOddQSpinLabelEquiv_actual (q : Q) (k : Fin 4096) :
    generatedAxisGlobalOddQSpinLabelEquiv q k =
      generatedAxisGlobalSpinLabel (golayLabelCoefficients k + spinTranslation q) := rfl

/-- A translated original source sign output vanishes at every omitted physical coefficient. -/
theorem generatedAxisGlobalOddQSignSpin_zero_outside
    (q : Q) (a : Fin 2048) (u : Fin 4096 → ℤ) (S E : Fin 4096 → Bool)
    (hs : ∀ m, S m = false → generatedAxisGlobalOddSignSpinInteger a u m = 0)
    (hc : ∀ m, S m = true → E ((generatedAxisGlobalOddQSpinLabelEquiv q).symm m) = true)
    (k : Fin 4096) (hk : E k = false) :
    generatedAxisGlobalOddQSpinInteger q (generatedAxisGlobalOddSignSpinInteger a u) k = 0 := by
  have hm : S (generatedAxisGlobalOddQSpinLabelEquiv q k) = false := by
    cases h : S (generatedAxisGlobalOddQSpinLabelEquiv q k) with
    | false => rfl
    | true =>
      have he := hc _ h
      rw [Equiv.symm_apply_apply, hk] at he
      contradiction
  unfold generatedAxisGlobalOddQSpinInteger
  rw [← generatedAxisGlobalOddQSpinLabelEquiv_actual, hs _ hm, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
