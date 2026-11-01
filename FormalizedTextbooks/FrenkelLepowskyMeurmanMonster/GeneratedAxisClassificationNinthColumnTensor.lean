/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMiddleTensor

/-! One column of the actual ninth middle tensor is one original spin circuit.
Linearity moves the physical matrix coefficients to the sparse input vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The physical row is applied first to the exact signed input tensor columns. -/
def generatedNinthColumnInputInteger (i : Fin 24) : NortonUIntegerVector := fun n =>
  ∑ j : Fin 24, generatedNinthFrameVectorData 9 j i * generatedNinthInputTensorInteger j n

/-- The column input embeds as the genuine physical linear combination. -/
theorem generatedNinth_column_input_embed (i : Fin 24) :
    nortonUIntegerEmbed (generatedNinthColumnInputInteger i) =
      ∑ j : Fin 24, (generatedNinthFrameVectorData 9 j i : ℝ) •
        nortonUIntegerEmbed (generatedNinthInputTensorInteger j) := by
  ext t
  simp only [nortonUIntegerEmbed, generatedNinthColumnInputInteger, Int.cast_sum,
    Int.cast_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

private theorem generatedNinth_integer_spin_sum
    (g : SpinHolomorph) (f : NortonUIntegerVector → NortonUIntegerVector)
    (hg : ∀ v, g.val (nortonUIntegerEmbed v) = (1 / 4096 : ℝ) • nortonUIntegerEmbed (f v))
    (w : Fin 24 → ℤ) (v : Fin 24 → NortonUIntegerVector) (n : Fin 4096) :
    f (fun m => ∑ j : Fin 24, w j * v j m) n = ∑ j : Fin 24, w j * f (v j) n := by
  have hv : nortonUIntegerEmbed (fun m => ∑ j : Fin 24, w j * v j m) =
      ∑ j : Fin 24, (w j : ℝ) • nortonUIntegerEmbed (v j) := by
    ext t
    simp only [nortonUIntegerEmbed, Int.cast_sum, Int.cast_mul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h := congrArg (fun z : SpinSpace => g.val z (golayLabelCoefficients n)) hv
  rw [hg] at h
  simp only [map_sum, map_smul, hg, smul_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, nortonUIntegerEmbed, nortonUIntegerLabel_coeff] at h
  have hr : (∑ j : Fin 24, (w j : ℝ) * (1 / 4096) * (f (v j) n : ℝ)) =
      (1 / 4096 : ℝ) * ∑ j : Fin 24, (w j : ℝ) * (f (v j) n : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hr] at h
  have hz : (f (fun m => ∑ j : Fin 24, w j * v j m) n : ℝ) =
      ((∑ j : Fin 24, w j * f (v j) n : ℤ) : ℝ) := by
    simp only [Int.cast_sum, Int.cast_mul]
    linarith [h]
  exact_mod_cast hz

/-- Linearity identifies the whole middle numerator with one spin-circuit evaluation. -/
theorem generatedNinth_column_integer_eq (n : Fin 4096) (i : Fin 24) :
    generatedNinthMiddleTensorInteger n i =
      generatedNinthIntegerSpin (generatedNinthColumnInputInteger i) n :=
  (generatedNinth_integer_spin_sum generatedNinthLocalFiber.val.1
    generatedNinthIntegerSpin generatedNinth_integer_spin_embed
    (fun j => generatedNinthFrameVectorData 9 j i) generatedNinthInputTensorInteger n).symm

/-- The true middle column is the sparse input's original spin word divided by its denominator. -/
theorem generatedNinth_middle_column_integer (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.2 t i =
        (generatedNinthIntegerSpin (generatedNinthColumnInputInteger i)
          (nortonUIntegerLabel t) : ℝ) / (32768 * Real.sqrt 2) := by
  rw [generatedNinth_middle_tensor_integer, generatedNinth_column_integer_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
