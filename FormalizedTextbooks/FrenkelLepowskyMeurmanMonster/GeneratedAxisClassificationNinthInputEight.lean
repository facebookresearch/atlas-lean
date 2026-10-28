/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthInputEightEmbed

/-! The literal original integer spin word preserves the exact eight-state source reduction. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem integer_eight (g : SpinHolomorph)
    (f : NortonUIntegerVector → NortonUIntegerVector)
    (hg : ∀ v, g.val (nortonUIntegerEmbed v) =
      (1 / 4096 : ℝ) • nortonUIntegerEmbed (f v))
    (w : Fin 8 → ℤ) (v : Fin 8 → NortonUIntegerVector) (u : NortonUIntegerVector)
    (hu : nortonUIntegerEmbed u =
      ∑ b : Fin 8, (w b : ℝ) • nortonUIntegerEmbed (v b)) (n : Fin 4096) :
    f u n = ∑ b : Fin 8, w b * f (v b) n := by
  have h := congrArg (fun z : SpinSpace => g.val z (golayLabelCoefficients n)) hu
  rw [hg] at h
  simp only [map_sum, map_smul, hg, smul_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, nortonUIntegerEmbed, nortonUIntegerLabel_coeff] at h
  have hr : (∑ b : Fin 8, (w b : ℝ) * (1 / 4096) * (f (v b) n : ℝ)) =
      (1 / 4096 : ℝ) * ∑ b : Fin 8, (w b : ℝ) * (f (v b) n : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hr] at h
  have he : (f u n : ℝ) = ((∑ b : Fin 8, w b * f (v b) n : ℤ) : ℝ) := by
    simp only [Int.cast_sum, Int.cast_mul]
    linarith only [h]
  exact_mod_cast he

/-- The actual original integer spin output retains its exact eight-column source reduction. -/
theorem generatedNinth_column_integer_eight (i : Fin 24) (n : Fin 4096) :
    generatedNinthIntegerSpin (generatedNinthColumnInputInteger i) n =
      ∑ b : Fin 8, generatedNinthInputBasisCoefficients i b *
        generatedNinthIntegerSpin (generatedNinthColumnInputInteger
          (generatedNinthInputBasisColumn b)) n :=
  integer_eight generatedNinthLocalFiber.val.1 generatedNinthIntegerSpin
    generatedNinth_integer_spin_embed (generatedNinthInputBasisCoefficients i)
    (fun b => generatedNinthColumnInputInteger (generatedNinthInputBasisColumn b))
    (generatedNinthColumnInputInteger i) (generatedNinth_column_input_eight_embed i) n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
