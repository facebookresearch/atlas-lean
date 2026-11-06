/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthTensorSupportDetector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedSpinSupportPhases

/-! A unique squared coordinate and the genuine affine detecting support exclude Pauli fixers.
The actual Ninth tensor's finite coordinate bindings are separate prerequisites. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem fixed_square (q : Q) (f : SpinSpace)
    (hf : spinRepresentation q f = f) (t : SpinIndex) :
    (f (t + spinTranslation q)) ^ 2 = (f t) ^ 2 := by
  have h := (generatedSpinSupport_fixed_iff q f).mp hf t
  have hs := congrArg (fun z : ℝ => z ^ 2) h
  rw [mul_pow] at hs
  have hsign : (qSign (spinPhase q t)) ^ 2 = 1 := by rw [pow_two, qSign_sq]
  rw [hsign, one_mul] at hs
  exact hs

/-- Any genuine spin vector with a unique squared coordinate and the thirteen nonzero
original detecting labels has trivial full extraspecial stabilizer. -/
theorem generatedNinth_tensor_support_fixed_trivial (q : Q) (f : SpinSpace)
    (hf : spinRepresentation q f = f)
    (hunique : ∃ t : SpinIndex, ∀ u : SpinIndex, (f u) ^ 2 = (f t) ^ 2 → u = t)
    (hsupport : ∀ i : Fin 13,
      f (golayLabelCoefficients (generatedNinthTensorSupportLabels i)) ≠ 0) : q = 1 := by
  obtain ⟨t, ht⟩ := hunique
  have htranslate := ht (t + spinTranslation q) (fixed_square q f hf t)
  have ha : spinTranslation q = 0 :=
    add_left_cancel (htranslate.trans (add_zero t).symm)
  have hp : ∀ u : SpinIndex, f (u + spinTranslation q) = qSign (0 : ZMod 2) * f u := by
    intro u
    simp only [ha, add_zero, qSign_zero, one_mul]
  have hphase : ∀ i : Fin 13, toAdd q.coeff +
      spinDot (spinModulation q) (golayLabelCoefficients
        (generatedNinthTensorSupportLabels i)) = 0 := by
    intro i
    have h := generatedSpinSupport_fixed_phase q f 0 hf hp
      (golayLabelCoefficients (generatedNinthTensorSupportLabels i)) (hsupport i)
    simpa only [spinPhase, add_zero] using h
  obtain ⟨hb, hc⟩ := generatedNinth_tensor_support_detect (spinModulation q)
    (toAdd q.coeff) hphase
  apply spinRepresentation_injective
  rw [map_one]
  apply LinearEquiv.ext
  intro w
  funext u
  change qSign (spinPhase q u) * w (u + spinTranslation q) = w u
  simp only [spinPhase, ha, hb, hc, spinDot_zero_left,
    qSign_zero, add_zero, one_mul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
