/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhQRootFixed

/-! Four distinct genuine extraspecial elements fix the complete seventh axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The identity and three genuine rooted-plane cocode modulations. -/
def generatedSeventhRootQModulation : Fin 4 → SpinIndex :=
  fun j => golayLabelCoefficients (![0, 1504, 1648, 912] j)

/-- The four literal cocode modulations are distinct in the actual binary module. -/
theorem generatedSeventh_root_Q_modulation_injective :
    Function.Injective generatedSeventhRootQModulation := by
  decide +kernel

/-- Each of the four actual cocodes fixes every original coordinate of the seventh axis. -/
theorem generatedSeventh_root_Q_mem (j : Fin 4) :
    cocodeQ (generatedSeventhRootQModulation j) ∈ generatedSeventhAxisQStabilizer := by
  change rhoLocal (inclQ (cocodeQ (generatedSeventhRootQModulation j)))
    generatedSeventhAxis = generatedSeventhAxis
  fin_cases j <;> dsimp only
  · change rhoLocal (inclQ (cocodeQ (generatedSeventhRootQModulation 0)))
      generatedSeventhAxis = generatedSeventhAxis
    have hc : cocodeQ (generatedSeventhRootQModulation 0) = 1 := by
      apply NormalizedCocycleExtension.Extension.ext <;> decide +kernel
    rw [hc, map_one, map_one]
    rfl
  · have h := generatedSeventh_target_pair_Q_fixed 0
    rw [generatedSeventh_target_pair_Q_cocode] at h
    exact h
  · have h := generatedSeventh_target_pair_Q_fixed 1
    rw [generatedSeventh_target_pair_Q_cocode] at h
    exact h
  · have h := generatedSeventh_target_pair_Q_fixed 2
    rw [generatedSeventh_target_pair_Q_cocode] at h
    exact h

/-- The actual full-axis extraspecial stabilizer contains at least four elements. -/
theorem generatedSeventhAxisQStabilizer_card_lower :
    4 ≤ Nat.card generatedSeventhAxisQStabilizer := by
  let f : Fin 4 → generatedSeventhAxisQStabilizer :=
    fun j => ⟨cocodeQ (generatedSeventhRootQModulation j), generatedSeventh_root_Q_mem j⟩
  have hi : Function.Injective f := by
    intro a b h
    apply generatedSeventh_root_Q_modulation_injective
    have hc := congrArg (fun q : generatedSeventhAxisQStabilizer => spinModulation q.val) h
    simpa only [f, cocodeQ_modulation] using hc
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
    Nat.card_le_card_of_injective f hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
