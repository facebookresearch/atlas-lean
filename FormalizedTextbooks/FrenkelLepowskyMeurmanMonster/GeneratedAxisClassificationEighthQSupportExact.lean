/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQSupportData

/-! The actual rank-eleven support and norm determine every nonzero coefficient magnitude. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every nonzero original middle spin coefficient satisfies the one genuine Pauli equation. -/
theorem generatedEighth_spin_support_equations (t : SpinIndex)
    (ht : generatedEighthSpinState t ≠ 0) :
    generatedEighthSpinSupportMatrix *ᵥ t = 0 := by
  funext j
  have h := generatedSpinSupport_fixed_phase
    (cocodeQ (golayLabelCoefficients (generatedEighthSpinSupportModulation j)))
    generatedEighthSpinState 0 (generatedEighth_spin_support_modulation_fixed j)
    (fun u => by simp only [cocodeQ_translation, add_zero, qSign_zero, one_mul]) t ht
  simpa only [spinPhase, cocodeQ_coeff, cocodeQ_modulation, zero_add, add_zero,
    generatedEighthSpinSupportMatrix, Matrix.mulVec, dotProduct, spinDot, Pi.zero_apply] using h

/-- The original translation projection is the identity on the support-equation kernel. -/
theorem generatedEighth_spin_support_projection (t : SpinIndex)
    (ht : generatedEighthSpinSupportMatrix *ᵥ t = 0) :
    generatedEighthSpinPauliTranslationMatrix *ᵥ
      (generatedEighthSpinPauliLeftInverse *ᵥ t) = t := by
  have h := congrArg (fun M : Matrix (Fin 12) (Fin 12) (ZMod 2) => M *ᵥ t)
    generatedEighth_spin_support_projection_certificate
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ht, Matrix.mulVec_zero, add_zero, Matrix.one_mulVec] at h
  exact h

/-- Every nonzero spin coordinate lies in the original 2048-point translation orbit of zero. -/
theorem generatedEighth_spin_support_orbit (t : SpinIndex)
    (ht : generatedEighthSpinState t ≠ 0) :
    ∃ a : Fin 11 → ZMod 2, generatedEighthSpinCoordinateOrbit 0 a = t := by
  refine ⟨generatedEighthSpinPauliLeftInverse *ᵥ t, ?_⟩
  change 0 + spinTranslation (generatedEighthSpinPauliProduct _) = t
  rw [zero_add, generatedEighth_spin_pauli_product_translation]
  exact generatedEighth_spin_support_projection t (generatedEighth_spin_support_equations t ht)

/-- The original norm is exactly 2048 times the square of its zero coordinate. -/
theorem generatedEighth_spin_state_norm_exact :
    spinPairing generatedEighthSpinState generatedEighthSpinState =
      (2048 : ℝ) * (generatedEighthSpinState 0) ^ 2 := by
  classical
  have hs : (∑ t ∈ Finset.univ.image (generatedEighthSpinCoordinateOrbit 0),
      (generatedEighthSpinState t) ^ 2) =
      (2048 : ℝ) * (generatedEighthSpinState 0) ^ 2 := by
    rw [Finset.sum_image]
    · simp only [generatedEighth_spin_coordinate_orbit_square, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      norm_num [Fintype.card_fun, ZMod.card]
    · intro a _ b _ h
      exact (generatedEighthSpinCoordinateOrbit 0).injective h
  have he : (∑ t ∈ Finset.univ.image (generatedEighthSpinCoordinateOrbit 0),
      (generatedEighthSpinState t) ^ 2) = ∑ t, (generatedEighthSpinState t) ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro t _ ht
    have hz : generatedEighthSpinState t = 0 := by
      by_contra hz
      obtain ⟨a, ha⟩ := generatedEighth_spin_support_orbit t hz
      exact ht (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩)
    rw [hz, zero_pow (by decide : (2 : Nat) ≠ 0)]
  have hz : spinPairing generatedEighthSpinState generatedEighthSpinState =
      ∑ t, (generatedEighthSpinState t) ^ 2 := by simp only [spinPairing, pow_two]
  rw [hz, ← he, hs]

/-- Every original translation-orbit coefficient has square exactly one two-hundred-fifty-eighth. -/
theorem generatedEighth_spin_orbit_square_exact (a : Fin 11 → ZMod 2) :
    (generatedEighthSpinState (generatedEighthSpinCoordinateOrbit 0 a)) ^ 2 =
      (1 / 1024 : ℝ) := by
  rw [generatedEighth_spin_coordinate_orbit_square]
  have h := generatedEighth_spin_state_norm_exact
  rw [generatedEighth_spin_state_pairing] at h
  linarith

/-- Each coordinate satisfying the original Pauli equations has the exact nonzero square. -/
theorem generatedEighth_spin_kernel_square_exact (t : SpinIndex)
    (ht : generatedEighthSpinSupportMatrix *ᵥ t = 0) :
    (generatedEighthSpinState t) ^ 2 = (1 / 1024 : ℝ) := by
  have h := generatedEighth_spin_orbit_square_exact (generatedEighthSpinPauliLeftInverse *ᵥ t)
  have he : generatedEighthSpinCoordinateOrbit 0
      (generatedEighthSpinPauliLeftInverse *ᵥ t) = t := by
    change 0 + spinTranslation (generatedEighthSpinPauliProduct _) = t
    rw [zero_add, generatedEighth_spin_pauli_product_translation]
    exact generatedEighth_spin_support_projection t ht
  rw [he] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
