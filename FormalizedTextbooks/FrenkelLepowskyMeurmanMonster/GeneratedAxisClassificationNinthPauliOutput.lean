/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliReconstruction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliTransport

/-! The literal original spin word retains all eight reconstructed source columns and phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem integer_sum (g : SpinHolomorph)
    (f : NortonUIntegerVector → NortonUIntegerVector)
    (hg : ∀ v, g.val (nortonUIntegerEmbed v) =
      (1 / 4096 : ℝ) • nortonUIntegerEmbed (f v))
    (d : ℤ) (u : NortonUIntegerVector) (w : Fin 128 → ℤ)
    (v : Fin 128 → NortonUIntegerVector)
    (hu : (d : ℝ) • nortonUIntegerEmbed u =
      ∑ q : Fin 128, (w q : ℝ) • nortonUIntegerEmbed (v q)) (n : Fin 4096) :
    d * f u n = ∑ q : Fin 128, w q * f (v q) n := by
  have h := congrArg (fun z : SpinSpace => g.val z (golayLabelCoefficients n)) hu
  simp only [map_sum, map_smul, hg, smul_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, nortonUIntegerEmbed, nortonUIntegerLabel_coeff] at h
  have hr : (∑ q : Fin 128, (w q : ℝ) * (1 / 4096) * (f (v q) n : ℝ)) =
      (1 / 4096 : ℝ) * ∑ q : Fin 128, (w q : ℝ) * (f (v q) n : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hr] at h
  have he : ((d * f u n : ℤ) : ℝ) =
      ((∑ q : Fin 128, w q * f (v q) n : ℤ) : ℝ) := by
    simp only [Int.cast_sum, Int.cast_mul]
    linarith only [h]
  exact_mod_cast he

/-- The exact original integer output numerator in its transported Q coordinates. -/
def generatedNinthPauliOutputInteger (b : Fin 8) (n : Fin 4096) : ℤ :=
  ∑ q : Fin 128, generatedNinthPauliInputCoefficients b q *
    nortonUIntegerQ (generatedNinthQImage (generatedNinthPauliWitness q))
      (generatedNinthColumnSpinData 9) n

/-- The actual nine-factor integer word retains every reconstructed input column. -/
theorem generatedNinth_pauli_output_integer (b : Fin 8) (n : Fin 4096) :
    generatedNinthPauliInputDenominator b *
      generatedNinthIntegerSpin (generatedNinthColumnInputInteger
        (generatedNinthInputBasisColumn b)) n =
          1024 * generatedNinthPauliOutputInteger b n := by
  have hu : (generatedNinthPauliInputDenominator b : ℝ) •
      nortonUIntegerEmbed (generatedNinthColumnInputInteger (generatedNinthInputBasisColumn b)) =
        ∑ q : Fin 128, (generatedNinthPauliInputCoefficients b q : ℝ) •
          nortonUIntegerEmbed (nortonUIntegerQ (generatedNinthPauliWitness q)
            (generatedNinthColumnInputInteger 1)) := by
    ext t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed]
    exact_mod_cast generatedNinth_pauli_input_reconstruction b (nortonUIntegerLabel t)
  have h := integer_sum generatedNinthLocalFiber.val.1 generatedNinthIntegerSpin
    generatedNinth_integer_spin_embed (generatedNinthPauliInputDenominator b)
    (generatedNinthColumnInputInteger (generatedNinthInputBasisColumn b))
    (generatedNinthPauliInputCoefficients b)
    (fun q => nortonUIntegerQ (generatedNinthPauliWitness q) (generatedNinthColumnInputInteger 1))
    hu n
  rw [h]
  simp only [generatedNinth_pauli_column_integer, generatedNinthPauliOutputInteger,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
