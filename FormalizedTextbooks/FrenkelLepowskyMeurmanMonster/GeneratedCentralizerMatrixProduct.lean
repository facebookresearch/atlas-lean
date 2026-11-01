/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual matrix constituent has twice the ordinary symmetric Jordan product. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerConstituentCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalProductInvariance

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Conway multiplication of pure matrix coordinates is twice their Jordan product. -/
theorem generatedCentral_raw_matrix_product (A B : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayRawProduct (A, (0, 0)) (B, (0, 0)) =
      ((2 : ℝ) • (A * B + B * A), (0, 0)) := by
  apply Prod.ext
  · funext i j
    simp only [conwayRawProduct, Pi.zero_apply, zero_mul, mul_zero, add_zero,
      ite_self, Finset.sum_const_zero, zero_div, Matrix.smul_apply,
      Matrix.add_apply, Matrix.mul_apply, smul_eq_mul, Finset.sum_add_distrib]
  · apply Prod.ext
    · funext r
      simp only [conwayRawProduct, Pi.zero_apply, zero_mul, mul_zero, add_zero,
        ite_self, Finset.sum_const_zero, zero_div]
    · funext t i
      simp only [conwayRawProduct, Pi.zero_apply, zero_mul, mul_zero, add_zero,
        ite_self, Finset.sum_const_zero, zero_div,
        show (fun _ : SpinIndex => (0 : ℝ)) = 0 from rfl, map_zero]

/-- The pure actual matrix vectors multiply as the original symmetric Jordan algebra. -/
theorem generatedCentral_matrix_product (A B : Sym24) :
    griessProd (generatedCentralPlusEmbed A 0).val (generatedCentralPlusEmbed B 0).val =
      (generatedCentralPlusEmbed ((2 : ℝ) • sym24Jordan A B) 0).val := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [griessProd_encode, generatedCentralPlusEmbed_encode,
    generatedCentralPlusEmbed_encode, generatedCentral_raw_matrix_product,
    generatedCentralPlusEmbed_encode]
  rfl

private theorem realZeroDot {ι : Type*} [Fintype ι] :
    (∑ r : ι, (0 : ι → ℝ) r * (0 : ι → ℝ) r) = 0 := by
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- On actual pure symmetric matrices, the original form is the ordinary trace product. -/
theorem generatedCentral_matrix_form (A B : Sym24) :
    griessForm (generatedCentralPlusEmbed A 0).val (generatedCentralPlusEmbed B 0).val =
      (A.val * B.val).trace := by
  rw [generatedCentralPlusEmbed_griessForm, realZeroDot, add_zero]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hB : B.val i j = B.val j i :=
    congrArg (fun M : Matrix (Fin 24) (Fin 24) ℝ => M j i) B.property
  rw [hB]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
