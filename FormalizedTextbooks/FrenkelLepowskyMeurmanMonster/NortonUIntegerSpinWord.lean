/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual Norton spin word has a computable integral numerator with denominator 128. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinXi

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Integer primitive sequence in the exact order of the complete actual Norton spin word. -/
def nortonUIntegerU (v : NortonUIntegerVector) : NortonUIntegerVector :=
  nortonUIntegerHadamard (nortonUIntegerY82PlusMinus (nortonUIntegerHadamard
    (nortonUIntegerQ (sourceQCode 2049 1)
      (nortonUIntegerQ (sourceQCocode (golayLabelCoefficients 1807))
        (nortonUIntegerPermutationInverse 0 (nortonUIntegerXi
          (nortonUIntegerPermutationInverse 1 (nortonUIntegerXi v))))))))

set_option maxHeartbeats 2000000 in
-- Normalize the ten nested linear factors while retaining their concrete integer numerators.
/-- Its exact normalization gives the actual complete spin fiber component. -/
theorem nortonUIntegerU_embed (v : NortonUIntegerVector) :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed v) =
      (1 / 128 : ℝ) • nortonUIntegerEmbed (nortonUIntegerU v) := by
  rw [monsterNortonUFiber_spin]
  change monsterSpinHadamard (monsterSourceY82PlusMinus.val (monsterSpinHadamard
    (spinRepresentation (sourceQCode 2049 1)
      (spinRepresentation (sourceQCocode (golayLabelCoefficients 1807))
        ((monsterSourcePermutationSpin 0)⁻¹.val (xiSpinHolomorph.val
          ((monsterSourcePermutationSpin 1)⁻¹.val
            (xiSpinHolomorph.val (nortonUIntegerEmbed v))))))))) = _
  simp only [nortonUIntegerXi_embed, nortonUIntegerPermutationInverse_embed,
    nortonUIntegerQ_embed, nortonUIntegerHadamard_embed, nortonUIntegerY82PlusMinus_embed,
    map_smul, smul_smul]
  apply congrArg (fun c : ℝ => c • nortonUIntegerEmbed (nortonUIntegerU v))
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hs]
  rw [hsq]
  norm_num

/-- Spin holomorph multiplication composes the actual operators in their given order. -/
theorem nortonUIntegerSpin_mul_apply (g h : SpinHolomorph) (f : SpinSpace) :
    (g * h).val f = g.val (h.val f) := rfl

set_option maxHeartbeats 400000 in
-- Rewrite abstract operator multiplication before specializing the large concrete word.
/-- The actual spin power is the corresponding integer iteration with every denominator retained. -/
theorem nortonUIntegerU_power_embed (n : ℕ) (v : NortonUIntegerVector) :
    (monsterNortonUFiber.val.1 ^ n).val (nortonUIntegerEmbed v) =
      ((1 / 128 : ℝ) ^ n) • nortonUIntegerEmbed ((nortonUIntegerU^[n]) v) := by
  induction n with
  | zero =>
    change nortonUIntegerEmbed v = (1 : ℝ) • nortonUIntegerEmbed v
    rw [one_smul]
  | succ n ih =>
    rw [pow_succ', nortonUIntegerSpin_mul_apply]
    rw [ih, map_smul, nortonUIntegerU_embed, smul_smul, Function.iterate_succ_apply']
    rw [pow_succ', mul_comm]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
