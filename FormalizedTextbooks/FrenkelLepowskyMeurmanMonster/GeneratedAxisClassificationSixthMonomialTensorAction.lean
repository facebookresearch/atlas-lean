/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorData

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalTensorPacked
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitSpatialActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftCorrectedTensor

/-! Genuine full tensor action of the four Q-corrected sixth monomial generators. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The four raw spatial coordinates are the original unsigned permutation pullbacks. -/
theorem generatedSixth_monomial_physical (k : Fin 4) (f : Fin 24 → ℝ) (i : Fin 24) :
    (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2.val f i =
      f (generatedSixthMonomialPhysicalInput k i) := by
  have he : (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2 =
      sixthFrameOrbitMonomialIsometry ⟨10 + k.val, by omega⟩ := by
    fin_cases k <;> rfl
  rw [he, sixthFrameOrbit_monomial_apply]
  have hs : sixthFrameOrbitSpatialSign ⟨10 + k.val, by omega⟩ i = 1 := by
    exact (show ∀ k : Fin 4, ∀ i : Fin 24,
      sixthFrameOrbitSpatialSign ⟨10 + k.val, by omega⟩ i = 1 from by decide +kernel) k i
  rw [hs, Int.cast_one, one_mul]
  rfl

/-- Both factors of the genuine raw tensor action retain their exact source orientation. -/
theorem generatedSixth_monomial_raw_tensor (k : Fin 4)
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (generatedSixthRawGenerator (Fin.castAdd 1 k)) T t i =
      qSign (monsterMonomialQuadratic (generatedSixthMonomialSpinModel k).phase t) *
        T ((generatedSixthMonomialSpinModel k).coordinate *ᵥ t)
          (generatedSixthMonomialPhysicalInput k i) := by
  rw [generatedFourth_local_tensor_columns]
  have hc (j : Fin 24) :
      (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2.val (Pi.single j 1) i *
        (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.1.val (fun u => T u j) t =
      (Pi.single j 1 : Fin 24 → ℝ) (generatedSixthMonomialPhysicalInput k i) *
        (qSign (monsterMonomialQuadratic (generatedSixthMonomialSpinModel k).phase t) *
          T ((generatedSixthMonomialSpinModel k).coordinate *ᵥ t) j) := by
    exact congrArg₂ (fun a b : ℝ => a * b)
      (generatedSixth_monomial_physical k (Pi.single j 1) i)
      (generatedSixth_monomial_raw_spin k (fun u => T u j) t)
  calc
    _ = ∑ j : Fin 24, (Pi.single j 1 : Fin 24 → ℝ)
        (generatedSixthMonomialPhysicalInput k i) *
        (qSign (monsterMonomialQuadratic (generatedSixthMonomialSpinModel k).phase t) *
          T ((generatedSixthMonomialSpinModel k).coordinate *ᵥ t) j) :=
      Finset.sum_congr rfl (fun j _ => hc j)
    _ = _ := by
      simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]

/-- The integer expression is the full genuine corrected tensor coordinate. -/
theorem generatedSixth_monomial_corrected_tensor (k : Fin 4)
    (n : Fin 4096) (i : Fin 24) :
    localTensorRepresentation (generatedSixthCorrectedGenerator (Fin.castAdd 1 k))
      (griessConwayEncode generatedSixthAxis).2.2 (golayLabelCoefficients n) i =
        (generatedSixthMonomialTensorNumerator k n i : ℝ) / (32 * Real.sqrt 2) := by
  rw [generatedSixthCorrectedGenerator, map_mul, LinearEquiv.mul_apply]
  rw [generatedFourth_lift_q_tensor, generatedSixth_monomial_raw_tensor]
  have hc (t : SpinIndex) (j : Fin 24) :
      (griessConwayEncode generatedSixthAxis).2.2 t j =
        (generatedSixthFinalTensorPackedNumerator (nortonUIntegerLabel t) j : ℝ) /
          (32 * Real.sqrt 2) := by
    simpa only [nortonUIntegerLabel_inverse] using
      generatedSixth_final_tensor_packed (nortonUIntegerLabel t) j
  rw [hc]
  simp only [generatedSixthMonomialTensorNumerator, Int.cast_mul,
    nortonUIntegerSign_real, qSign_add]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
