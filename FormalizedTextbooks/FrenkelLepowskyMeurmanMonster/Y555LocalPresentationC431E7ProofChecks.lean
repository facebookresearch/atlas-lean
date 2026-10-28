/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Soundness of the completely checked original-source C431 E7 equation program. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431E7ProofRowChecks

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- Every equation of the acyclic C431 proof program has a checked original-source derivation. -/
theorem y431E7ProofProgram_checked (i : Fin 356) :
    (y431E7ProofProgram i).Checked y431CoxeterEquation
      (fun a => (y431E7ProofProgram (y322ProgramPrior i a)).equation) := by
  by_cases hi : i.val < 171
  · exact y431E7ProofProgram_seed_checked i hi
  · let row : Fin 185 := ⟨i.val - 171, by omega⟩
    have h := y431E7ProofRow_checked row
    have he : (⟨171 + row.val, by omega⟩ : Fin 356) = i := by
      apply Fin.ext
      dsimp only [row]
      omega
    unfold y431E7ProofRowChecked at h
    rw [he] at h
    exact h

set_option maxRecDepth 100000 in
/-- Every checked C431 elementary equation holds in its original independently presented group. -/
theorem y431E7ProofProgram_valid (i : Fin 356) :
    (y431E7ProofProgram i).equation.Valid
      (fun v => (PresentedGroup.of v : Y431RPresentation)) :=
  y322EquationProgram_valid _ _ y431CoxeterEquation_valid _ y431E7ProofProgram_checked i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
