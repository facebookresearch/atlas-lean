/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPauliTransportData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddStatePairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddSpinStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedSpinSupportPhases

/-! Actual Pauli fixation and norm of the genuine sixth middle spin state. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual spin image in the middle of the original triality/local/triality word. -/
def generatedSixthSpinState : SpinSpace :=
  generatedSixthLocalFiber.val.1.val (generatedOddSpinState 0 1 0)

/-- The genuine middle spin state has squared Euclidean norm two. -/
theorem generatedSixth_spin_state_pairing :
    spinPairing generatedSixthSpinState generatedSixthSpinState = 2 := by
  have h := generatedSixthLocalFiber.val.1.property.2
    (generatedOddSpinState 0 1 0) (generatedOddSpinState 0 1 0)
  exact h.trans (generatedOddSpinState_pairing 0 1)

private theorem cache_image (j : Fin 12) :
    generatedSixthQImage (generatedSixthSpinPauliCache j 0) =
      generatedSixthSpinPauliCache j 8 := by
  rcases generatedSixth_spin_pauli_cache_certificate j with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  unfold generatedSixthQImage generatedSixthQWord
  simp only [List.foldl_cons, List.foldl_nil]
  rw [← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7, ← h8]

/-- The full original word transports each initial Pauli generator to its certified final value. -/
theorem generatedSixth_spin_pauli_transport (j : Fin 12) :
    spinConjugation generatedSixthLocalFiber.val.1 (generatedSixthSpinPauliInitial j) =
      generatedSixthSpinPauliCache j 8 := by
  rw [generatedSixthSpinPauliInitial, generatedSixth_spin_conjugation, cache_image]

private theorem transported_fixed (s : SpinHolomorph) (q : Q) (f : SpinSpace)
    (hf : spinRepresentation q f = f) :
    spinRepresentation (spinConjugation s q) (s.val f) = s.val f := by
  rw [spinConjugation_representation]
  simp only [LinearEquiv.mul_apply]
  change s.val (spinRepresentation q (s.val.symm (s.val f))) = _
  rw [LinearEquiv.symm_apply_apply, hf]

/-- All twelve actual transported Pauli operators fix the actual middle spin state. -/
theorem generatedSixth_spin_pauli_final_fixed (j : Fin 12) :
    spinRepresentation (generatedSixthSpinPauliCache j 8) generatedSixthSpinState =
      generatedSixthSpinState := by
  rw [← generatedSixth_spin_pauli_transport]
  exact transported_fixed generatedSixthLocalFiber.val.1 (generatedSixthSpinPauliInitial j)
    (generatedOddSpinState 0 1 0) (generatedSixth_spin_pauli_initial_fixed j)

/-- A genuine fixing pure modulation distinguishes the two coordinates of each Ω pair. -/
theorem generatedSixth_spin_state_odd_modulation_fixed :
    spinRepresentation (cocodeQ (golayLabelCoefficients 3079)) generatedSixthSpinState =
      generatedSixthSpinState := by
  rw [← generatedSixth_spin_pauli_odd_modulation, map_mul]
  simp only [LinearEquiv.mul_apply, generatedSixth_spin_pauli_final_fixed]

/-- The two members of every Ω pair cannot both lie in the support of the actual middle state. -/
theorem generatedSixth_spin_state_omega_product_zero (t : SpinIndex) :
    generatedSixthSpinState t *
      generatedSixthSpinState (t + Pi.single (11 : Fin 12) 1) = 0 := by
  by_cases ht : generatedSixthSpinState t = 0
  · rw [ht, zero_mul]
  · have hu : generatedSixthSpinState (t + Pi.single (11 : Fin 12) 1) = 0 := by
      by_contra hu
      have he := generatedSpinSupport_fixed_modulation_difference
        (cocodeQ (golayLabelCoefficients 3079)) generatedSixthSpinState 0
        generatedSixth_spin_state_odd_modulation_fixed
        (fun u => by simp only [cocodeQ_translation, add_zero, qSign_zero, one_mul])
        t (t + Pi.single (11 : Fin 12) 1) ht hu
      rw [cocodeQ_modulation, ← add_assoc, ZModModule.add_self, zero_add] at he
      have ho : spinDot (golayLabelCoefficients 3079) (Pi.single (11 : Fin 12) 1) = 1 := by
        decide +kernel
      rw [ho] at he
      exact one_ne_zero he
    rw [hu, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
