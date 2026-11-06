/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact extraspecial conjugation by the one-coordinate source Fourier operator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationSpinHadamard

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Swapping the last translation and modulation coordinates includes their central correction. -/
def monsterSpinHadamardImage (q : Q) : Q :=
  let a := spinTranslation q
  let b := spinModulation q
  let δ := a 11 + b 11
  ⟨ofAdd (Fin.append (a + δ • monsterSpinOmegaVector)
    (b + δ • monsterSpinOmegaVector)), ofAdd (toAdd q.coeff + a 11 * b 11)⟩

/-- The exact translation of the actual Fourier-conjugated Q element. -/
theorem monsterSpinHadamardImage_translation (q : Q) :
    spinTranslation (monsterSpinHadamardImage q) = spinTranslation q +
      (spinTranslation q 11 + spinModulation q 11) • monsterSpinOmegaVector := by
  ext i
  exact Fin.append_left _ _ i

/-- Its exact modulation swaps the same last pair. -/
theorem monsterSpinHadamardImage_modulation (q : Q) :
    spinModulation (monsterSpinHadamardImage q) = spinModulation q +
      (spinTranslation q 11 + spinModulation q 11) • monsterSpinOmegaVector := by
  ext i
  exact Fin.append_right _ _ i

/-- The last-coordinate unit character is actual coordinate evaluation. -/
theorem monsterSpinOmegaVector_dot (t : SpinIndex) :
    spinDot monsterSpinOmegaVector t = t 11 := by
  simp [spinDot, monsterSpinOmegaVector, Pi.single_apply]

/-- The corresponding right character is the same coordinate evaluation. -/
theorem monsterSpinOmegaVector_dot_right (t : SpinIndex) :
    spinDot t monsterSpinOmegaVector = t 11 := by
  simp [spinDot, monsterSpinOmegaVector, Pi.single_apply]

/-- The last translation becomes the old last modulation. -/
theorem monsterSpinHadamardImage_translation_last (q : Q) :
    spinTranslation (monsterSpinHadamardImage q) 11 = spinModulation q 11 := by
  rw [monsterSpinHadamardImage_translation]
  change spinTranslation q 11 + (spinTranslation q 11 + spinModulation q 11) * 1 = _
  rw [mul_one, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- The image phase retains the exact central correction and the swapped coordinate character. -/
theorem monsterSpinHadamardImage_phase (q : Q) (t : SpinIndex) :
    spinPhase (monsterSpinHadamardImage q) t = spinPhase q t +
      spinTranslation q 11 * spinModulation q 11 +
        (spinTranslation q 11 + spinModulation q 11) * t 11 := by
  have hc : toAdd (monsterSpinHadamardImage q).coeff =
      toAdd q.coeff + spinTranslation q 11 * spinModulation q 11 := rfl
  rw [spinPhase, hc, monsterSpinHadamardImage_modulation, spinDot_add_left,
    xiSpinDot_smul_left, monsterSpinOmegaVector_dot]
  unfold spinPhase
  abel

/-- Flipping the last label adds exactly the last modulation to the source phase. -/
theorem monsterSpinHadamard_phase_flip (q : Q) (t : SpinIndex) :
    spinPhase q (monsterSpinOmegaFlip t) = spinPhase q t + spinModulation q 11 := by
  rw [spinPhase, monsterSpinOmegaFlip, spinDot_add_right, monsterSpinOmegaVector_dot_right]
  exact (add_assoc _ _ _).symm

/-- The sixteen binary sign cases governing the actual two-term Fourier intertwiner. -/
theorem monsterSpinHadamard_sign_identity (a b t p : ZMod 2) (x y : ℝ) :
    qSign t * qSign p * x + qSign (p + b) * y =
      qSign (p + a * b + (a + b) * t) *
        (qSign (t + b) * (if a + b = 0 then x else y) +
          (if a + b = 0 then y else x)) := by
  have hc : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
  have h11 : (1 : ZMod 2) + 1 = 0 := CharTwo.add_self_eq_zero _
  obtain rfl | rfl := hc a <;> obtain rfl | rfl := hc b <;>
    obtain rfl | rfl := hc t <;> obtain rfl | rfl := hc p <;>
      simp only [zero_add, add_zero, mul_zero, mul_one, one_mul,
        h11, qSign_zero, qSign_one, ite_true, ite_eq_right one_ne_zero] <;> ring

/-- The flip commutes with every genuine additive translation of labels. -/
theorem monsterSpinOmegaFlip_add (t a : SpinIndex) :
    monsterSpinOmegaFlip t + a = monsterSpinOmegaFlip (t + a) := by
  ext i
  change (t i + monsterSpinOmegaVector i) + a i = (t i + a i) + monsterSpinOmegaVector i
  abel

/-- The Fourier image either retains or flips the old shifted label. -/
theorem monsterSpinHadamardImage_shift (q : Q) (t : SpinIndex) :
    t + spinTranslation (monsterSpinHadamardImage q) =
      if spinTranslation q 11 + spinModulation q 11 = 0 then t + spinTranslation q
      else monsterSpinOmegaFlip (t + spinTranslation q) := by
  rw [monsterSpinHadamardImage_translation]
  have hc : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
  obtain h | h := hc (spinTranslation q 11 + spinModulation q 11)
  · rw [h, zero_smul, add_zero, ite_eq_left rfl]
  · rw [h, one_smul, ite_eq_right one_ne_zero]
    exact (add_assoc _ _ _).symm

/-- Applying the flip to that image exchanges the same two old labels. -/
theorem monsterSpinHadamardImage_shift_flip (q : Q) (t : SpinIndex) :
    monsterSpinOmegaFlip (t + spinTranslation (monsterSpinHadamardImage q)) =
      if spinTranslation q 11 + spinModulation q 11 = 0 then
        monsterSpinOmegaFlip (t + spinTranslation q) else t + spinTranslation q := by
  rw [monsterSpinHadamardImage_shift]
  split_ifs <;> first | rfl | exact monsterSpinOmegaFlip_double _

/-- The explicit two-term Fourier sum intertwines every actual extraspecial operator. -/
theorem monsterSpinHadamard_intertwines (q : Q) (f : SpinSpace) (t : SpinIndex) :
    monsterSpinHadamard (spinRepresentation q f) t =
      spinRepresentation (monsterSpinHadamardImage q) (monsterSpinHadamard f) t := by
  rw [monsterSpinHadamard_apply, monsterMonomialSpinRepresentation_apply,
    monsterMonomialSpinRepresentation_apply, monsterMonomialSpinRepresentation_apply,
    monsterSpinHadamard_apply, monsterSpinHadamard_phase_flip,
    monsterSpinOmegaFlip_add, monsterSpinHadamardImage_phase]
  have hl : (t + spinTranslation (monsterSpinHadamardImage q)) 11 =
      t 11 + spinModulation q 11 := by
    rw [Pi.add_apply, monsterSpinHadamardImage_translation_last]
  rw [hl, monsterSpinHadamardImage_shift_flip, monsterSpinHadamardImage_shift]
  simp only [apply_ite]
  have h := monsterSpinHadamard_sign_identity (spinTranslation q 11) (spinModulation q 11)
    (t 11) (spinPhase q t) (f (t + spinTranslation q))
      (f (monsterSpinOmegaFlip (t + spinTranslation q)))
  by_cases hd : spinTranslation q 11 + spinModulation q 11 = 0 <;>
    simp only [hd, ite_true, ite_false] at h ⊢ <;>
      linear_combination (1 / Real.sqrt 2) * h

/-- Conjugation by the actual Fourier equivalence has the full central-corrected Q image. -/
theorem monsterSpinHadamard_conjugation (q : Q) :
    monsterSpinHadamardEquiv * spinRepresentation q * monsterSpinHadamardEquiv =
      spinRepresentation (monsterSpinHadamardImage q) := by
  apply LinearEquiv.ext
  intro f
  ext t
  change monsterSpinHadamard (spinRepresentation q (monsterSpinHadamard f)) t = _
  rw [monsterSpinHadamard_intertwines, monsterSpinHadamard_involutive f]

/-- The actual Fourier linear equivalence has square one. -/
theorem monsterSpinHadamardEquiv_square :
    monsterSpinHadamardEquiv * monsterSpinHadamardEquiv = 1 := by
  apply LinearEquiv.ext
  exact monsterSpinHadamard_involutive

/-- The explicit source plus/minus change is an actual orthogonal normalizer of Q. -/
noncomputable def monsterSpinHadamardHolomorph : SpinHolomorph :=
  ⟨monsterSpinHadamardEquiv,
    xiSpinImage_normalizer_of_involution _ monsterSpinHadamardEquiv_square
      monsterSpinHadamardImage monsterSpinHadamard_conjugation,
    monsterSpinHadamard_pairing⟩

/-- The proved coordinate image is the actual conjugation automorphism of the normalizer. -/
theorem monsterSpinHadamardHolomorph_conjugation (q : Q) :
    spinConjugation monsterSpinHadamardHolomorph q = monsterSpinHadamardImage q := by
  apply spinRepresentation_injective
  rw [spinConjugation_representation]
  have hi : monsterSpinHadamardEquiv⁻¹ = monsterSpinHadamardEquiv :=
    inv_eq_of_mul_eq_one_right monsterSpinHadamardEquiv_square
  change monsterSpinHadamardEquiv * spinRepresentation q * monsterSpinHadamardEquiv⁻¹ =
    spinRepresentation (monsterSpinHadamardImage q)
  rw [hi]
  exact monsterSpinHadamard_conjugation q

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
