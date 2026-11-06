/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQMiddleFull
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedForwardQLocal

/-! Full middle Pauli fixers yield genuine forward local lifts after even-modulation correction. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- An actual fixing odd modulation corrects parity without changing the translation. -/
def generatedEighthEvenPauli (q : Q) : Q :=
  if spinModulation q 11 = 0 then q else q * cocodeQ (golayLabelCoefficients 3079)

/-- The corrected original element has even actual modulation. -/
theorem generatedEighth_even_pauli_modulation (q : Q) :
    spinModulation (generatedEighthEvenPauli q) 11 = 0 := by
  unfold generatedEighthEvenPauli
  split_ifs with h
  · exact h
  · rw [spinModulation_mul, Pi.add_apply, cocodeQ_modulation]
    have hm : golayLabelCoefficients 3079 (11 : Fin 12) = 1 := by decide +kernel
    rw [hm]
    have he : spinModulation q 11 = 1 := by
      have hv := ZMod.val_lt (spinModulation q 11)
      have hn : (spinModulation q 11).val ≠ 0 := by
        intro hz
        apply h
        exact (ZMod.val_eq_zero _).mp hz
      have hval : (spinModulation q 11).val = 1 := by omega
      apply ZMod.val_injective 2
      change (spinModulation q 11).val = 1
      exact hval
    rw [he]
    decide +kernel

/-- Parity correction retains the complete actual translation. -/
theorem generatedEighth_even_pauli_translation (q : Q) :
    spinTranslation (generatedEighthEvenPauli q) = spinTranslation q := by
  unfold generatedEighthEvenPauli
  split_ifs
  · rfl
  · rw [spinTranslation_mul, cocodeQ_translation, add_zero]

/-- Correcting a full middle fixer by the fixing modulation still fixes the full middle axis. -/
theorem generatedEighth_even_pauli_full_fixed (q : Q)
    (hq : rhoLocal (inclQ q) generatedEighthMiddleAxis = generatedEighthMiddleAxis) :
    rhoLocal (inclQ (generatedEighthEvenPauli q)) generatedEighthMiddleAxis =
      generatedEighthMiddleAxis := by
  unfold generatedEighthEvenPauli
  split_ifs
  · exact hq
  · simp only [map_mul, LinearEquiv.mul_apply,
      generatedEighth_middle_odd_modulation_full_fixed, hq]

/-- The chosen forward-triality local element associated with an actual middle fixer. -/
def generatedEighthPauliLocalLift (q : Q) : H :=
  generatedForwardQLocal (generatedEighthEvenPauli q) (generatedEighth_even_pauli_modulation q)

/-- Forward triality transport gives a genuine complete Eighth-axis fixer. -/
theorem generatedEighth_pauli_local_lift_full_fixed (q : Q)
    (hq : rhoLocal (inclQ q) generatedEighthMiddleAxis = generatedEighthMiddleAxis) :
    rhoLocal (generatedEighthPauliLocalLift q) generatedEighthAxis = generatedEighthAxis := by
  rw [generatedEighthPauliLocalLift, generatedForwardQLocal_action,
    generatedEighthAxis_local_expression]
  change (sExtra * rhoLocal (inclQ (generatedEighthEvenPauli q)) * sExtra⁻¹)
    (sExtra generatedEighthMiddleAxis) = sExtra generatedEighthMiddleAxis
  simp only [LinearEquiv.mul_apply]
  change sExtra (rhoLocal (inclQ (generatedEighthEvenPauli q))
    (sExtra.symm (sExtra generatedEighthMiddleAxis))) = _
  rw [LinearEquiv.symm_apply_apply, generatedEighth_even_pauli_full_fixed q hq]

/-- Its actual Conway projection is the original translation-code sign isometry. -/
theorem generatedEighth_pauli_local_lift_projection (q : Q) (d : Fin 4096)
    (hd : spinTranslation q = golayLabelCoefficients d) :
    projH (generatedEighthPauliLocalLift q) =
      (QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode d)) : Co1) := by
  apply generatedForwardQLocal_projection
  rw [generatedEighth_even_pauli_translation]
  exact hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
