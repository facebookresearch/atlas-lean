/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinSupportData

/-! The actual rank-nine support and norm determine every nonzero coefficient magnitude. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every nonzero original middle spin coefficient satisfies the three genuine Pauli equations. -/
theorem generatedSixth_spin_support_equations (t : SpinIndex)
    (ht : generatedSixthSpinState t ≠ 0) :
    generatedSixthSpinSupportMatrix *ᵥ t = 0 := by
  funext j
  have h := generatedSpinSupport_fixed_phase
    (cocodeQ (golayLabelCoefficients (generatedSixthSpinSupportModulation j)))
    generatedSixthSpinState 0 (generatedSixth_spin_support_modulation_fixed j)
    (fun u => by simp only [cocodeQ_translation, add_zero, qSign_zero, one_mul]) t ht
  simpa only [spinPhase, cocodeQ_coeff, cocodeQ_modulation, zero_add, add_zero,
    generatedSixthSpinSupportMatrix, Matrix.mulVec, dotProduct, spinDot, Pi.zero_apply] using h

/-- The genuine rank-nine translation projection is the identity on the support-equation kernel. -/
theorem generatedSixth_spin_support_projection (t : SpinIndex)
    (ht : generatedSixthSpinSupportMatrix *ᵥ t = 0) :
    generatedSixthSpinPauliTranslationMatrix *ᵥ (generatedSixthSpinPauliLeftInverse *ᵥ t) = t := by
  have h := congrArg (fun M : Matrix (Fin 12) (Fin 12) (ZMod 2) => M *ᵥ t)
    generatedSixth_spin_support_projection_certificate
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ht, Matrix.mulVec_zero, add_zero, Matrix.one_mulVec] at h
  exact h

/-- Every nonzero spin coordinate lies in the original 512-point translation orbit of zero. -/
theorem generatedSixth_spin_support_orbit (t : SpinIndex)
    (ht : generatedSixthSpinState t ≠ 0) :
    ∃ a : Fin 9 → ZMod 2, generatedSixthSpinCoordinateOrbit 0 a = t := by
  refine ⟨generatedSixthSpinPauliLeftInverse *ᵥ t, ?_⟩
  change 0 + spinTranslation (generatedSixthSpinPauliProduct _) = t
  rw [zero_add, generatedSixth_spin_pauli_product_translation]
  exact generatedSixth_spin_support_projection t (generatedSixth_spin_support_equations t ht)

/-- The original norm is exactly 512 times the square of its zero coordinate. -/
theorem generatedSixth_spin_state_norm_exact :
    spinPairing generatedSixthSpinState generatedSixthSpinState =
      (512 : ℝ) * (generatedSixthSpinState 0) ^ 2 := by
  classical
  have hs : (∑ t ∈ Finset.univ.image (generatedSixthSpinCoordinateOrbit 0),
      (generatedSixthSpinState t) ^ 2) =
      (512 : ℝ) * (generatedSixthSpinState 0) ^ 2 := by
    rw [Finset.sum_image]
    · simp only [generatedSixth_spin_coordinate_orbit_square, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      norm_num [Fintype.card_fun, ZMod.card]
    · intro a _ b _ h
      exact (generatedSixthSpinCoordinateOrbit 0).injective h
  have he : (∑ t ∈ Finset.univ.image (generatedSixthSpinCoordinateOrbit 0),
      (generatedSixthSpinState t) ^ 2) = ∑ t, (generatedSixthSpinState t) ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro t _ ht
    have hz : generatedSixthSpinState t = 0 := by
      by_contra hz
      obtain ⟨a, ha⟩ := generatedSixth_spin_support_orbit t hz
      exact ht (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩)
    rw [hz, zero_pow (by decide : (2 : Nat) ≠ 0)]
  have hz : spinPairing generatedSixthSpinState generatedSixthSpinState =
      ∑ t, (generatedSixthSpinState t) ^ 2 := by simp only [spinPairing, pow_two]
  rw [hz, ← he, hs]

/-- Every original translation-orbit coefficient has square exactly one two-hundred-fifty-sixth. -/
theorem generatedSixth_spin_orbit_square_exact (a : Fin 9 → ZMod 2) :
    (generatedSixthSpinState (generatedSixthSpinCoordinateOrbit 0 a)) ^ 2 =
      (1 / 256 : ℝ) := by
  rw [generatedSixth_spin_coordinate_orbit_square]
  have h := generatedSixth_spin_state_norm_exact
  rw [generatedSixth_spin_state_pairing] at h
  linarith

/-- Each coordinate satisfying the original Pauli equations has the exact nonzero square. -/
theorem generatedSixth_spin_kernel_square_exact (t : SpinIndex)
    (ht : generatedSixthSpinSupportMatrix *ᵥ t = 0) :
    (generatedSixthSpinState t) ^ 2 = (1 / 256 : ℝ) := by
  have h := generatedSixth_spin_orbit_square_exact (generatedSixthSpinPauliLeftInverse *ᵥ t)
  have he : generatedSixthSpinCoordinateOrbit 0 (generatedSixthSpinPauliLeftInverse *ᵥ t) = t := by
    change 0 + spinTranslation (generatedSixthSpinPauliProduct _) = t
    rw [zero_add, generatedSixth_spin_pauli_product_translation]
    exact generatedSixth_spin_support_projection t ht
  rw [he] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
