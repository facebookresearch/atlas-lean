/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedBlock00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedBlock01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedBlock02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedBlock03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedBlock04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedBlock05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedBlock06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedBlock07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedBlock08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedBlock09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedBlock10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedBlock11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedBlock12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedBlock13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedBlock14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedBlock15

/-! All bounded original signed spin blocks assemble into the genuine complete phase vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Both support and signs equal the actual original spin phase at every coordinate. -/
theorem generatedSixth_packed_spin_phase (n : Fin 4096) :
    generatedSixthPackedSpinPhase n = generatedSixthPartialPhaseInteger 8 n := by
  rw [generatedSixth_packed_phase_formula]
  have hall (b : Fin 16) (j : Fin 256) :
      generatedSixthPackedSpinPhase ⟨256 * b.val + j.val, by omega⟩ =
        generatedSixthPackedPhaseFormula ⟨256 * b.val + j.val, by omega⟩ := by
    fin_cases b
    · exact generatedSixth_packed_spin_phase_block00 j
    · exact generatedSixth_packed_spin_phase_block01 j
    · exact generatedSixth_packed_spin_phase_block02 j
    · exact generatedSixth_packed_spin_phase_block03 j
    · exact generatedSixth_packed_spin_phase_block04 j
    · exact generatedSixth_packed_spin_phase_block05 j
    · exact generatedSixth_packed_spin_phase_block06 j
    · exact generatedSixth_packed_spin_phase_block07 j
    · exact generatedSixth_packed_spin_phase_block08 j
    · exact generatedSixth_packed_spin_phase_block09 j
    · exact generatedSixth_packed_spin_phase_block10 j
    · exact generatedSixth_packed_spin_phase_block11 j
    · exact generatedSixth_packed_spin_phase_block12 j
    · exact generatedSixth_packed_spin_phase_block13 j
    · exact generatedSixth_packed_spin_phase_block14 j
    · exact generatedSixth_packed_spin_phase_block15 j
  let b : Fin 16 := ⟨n.val / 256, by omega⟩
  let j : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have hn : n = ⟨256 * b.val + j.val, by omega⟩ := by
    apply Fin.ext
    dsimp [b, j]
    omega
  rw [hn]
  exact hall b j

/-- The compact signed spin vector retains the actual positive one-sixteenth normalization. -/
theorem generatedSixth_packed_spin_state (n : Fin 4096) :
    generatedSixthSpinState (golayLabelCoefficients n) =
      (generatedSixthPackedSpinPhase n : ℝ) / 16 := by
  have h := congrArg (fun f : SpinSpace => f (golayLabelCoefficients n))
    (generatedSixth_partial_phase_embed 8)
  rw [generatedSixth_partial_state_final] at h
  have ha := generatedSixth_partial_anchor_values 8
  change generatedSixthPartialSpinAnchor 8 = (1 / 16 : ℝ) at ha
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed,
    nortonUIntegerLabel_coeff, ha] at h
  rw [← generatedSixth_packed_spin_phase] at h
  exact h.trans (by ring)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
