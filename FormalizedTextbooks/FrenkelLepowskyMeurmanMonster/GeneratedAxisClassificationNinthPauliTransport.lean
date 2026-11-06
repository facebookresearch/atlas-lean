/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnFullSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthQImage

/-! The actual original spin word transports every Q translate of its certified input column. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem intertwine (s : SpinHolomorph) (q : Q) (f : SpinSpace) :
    s.val (spinRepresentation q f) =
      spinRepresentation (spinConjugation s q) (s.val f) := by
  rw [spinConjugation_representation]
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

/-- Every actual Q translate of column one has its exact transported spin state. -/
theorem generatedNinth_pauli_column_spin (q : Q) :
    generatedNinthLocalFiber.val.1.val
      (nortonUIntegerEmbed (nortonUIntegerQ q (generatedNinthColumnInputInteger 1))) =
        (1 / 4 : ℝ) • nortonUIntegerEmbed
          (nortonUIntegerQ (generatedNinthQImage q) (generatedNinthColumnSpinData 9)) := by
  rw [← nortonUIntegerQ_embed, intertwine, generatedNinthQImage_eq,
    generatedNinth_column_full_spin, map_smul, nortonUIntegerQ_embed]

/-- The literal original integer word retains the transported Q phase with factor1024. -/
theorem generatedNinth_pauli_column_integer (q : Q) (n : Fin 4096) :
    generatedNinthIntegerSpin
      (nortonUIntegerQ q (generatedNinthColumnInputInteger 1)) n =
        1024 * nortonUIntegerQ (generatedNinthQImage q) (generatedNinthColumnSpinData 9) n := by
  have h := generatedNinth_pauli_column_spin q
  rw [generatedNinth_integer_spin_embed] at h
  have hn := congrArg (fun f : SpinSpace => f (golayLabelCoefficients n)) h
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed,
    nortonUIntegerLabel_coeff] at hn
  have he : (generatedNinthIntegerSpin
      (nortonUIntegerQ q (generatedNinthColumnInputInteger 1)) n : ℝ) =
      (1024 : ℝ) *
        (nortonUIntegerQ (generatedNinthQImage q) (generatedNinthColumnSpinData 9) n : ℝ) := by
    linarith only [hn]
  exact_mod_cast he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
