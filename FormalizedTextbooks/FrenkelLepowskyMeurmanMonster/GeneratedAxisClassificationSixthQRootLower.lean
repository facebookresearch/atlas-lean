/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQRootFixed

/-! Four distinct genuine extraspecial elements fix the complete sixth axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual extraspecial intersection with the sixth-axis local stabilizer. -/
def generatedSixthAxisQStabilizer : Subgroup Q :=
  generatedSixthLocalAxisStabilizer.comap inclQ

/-- The identity and three genuine rooted-plane cocode modulations. -/
def generatedSixthRootQModulation : Fin 4 → SpinIndex :=
  fun j => golayLabelCoefficients (![0, 1504, 1648, 912] j)

/-- The four literal cocode modulations are distinct in the actual binary module. -/
theorem generatedSixth_root_Q_modulation_injective :
    Function.Injective generatedSixthRootQModulation := by
  decide +kernel

/-- Each of the four actual cocodes fixes every original coordinate of the sixth axis. -/
theorem generatedSixth_root_Q_mem (j : Fin 4) :
    cocodeQ (generatedSixthRootQModulation j) ∈ generatedSixthAxisQStabilizer := by
  change rhoLocal (inclQ (cocodeQ (generatedSixthRootQModulation j)))
    generatedSixthAxis = generatedSixthAxis
  fin_cases j <;> dsimp only
  · change rhoLocal (inclQ (cocodeQ (generatedSixthRootQModulation 0)))
      generatedSixthAxis = generatedSixthAxis
    have hc : cocodeQ (generatedSixthRootQModulation 0) = 1 := by
      apply NormalizedCocycleExtension.Extension.ext <;> decide +kernel
    rw [hc, map_one, map_one]
    rfl
  · have h := generatedSixth_target_pair_Q_fixed 0
    rw [generatedSixth_target_pair_Q_cocode] at h
    exact h
  · have h := generatedSixth_target_pair_Q_fixed 1
    rw [generatedSixth_target_pair_Q_cocode] at h
    exact h
  · have h := generatedSixth_target_pair_Q_fixed 2
    rw [generatedSixth_target_pair_Q_cocode] at h
    exact h

/-- The actual full-axis extraspecial stabilizer contains at least four elements. -/
theorem generatedSixthAxisQStabilizer_card_lower :
    4 ≤ Nat.card generatedSixthAxisQStabilizer := by
  let f : Fin 4 → generatedSixthAxisQStabilizer :=
    fun j => ⟨cocodeQ (generatedSixthRootQModulation j), generatedSixth_root_Q_mem j⟩
  have hi : Function.Injective f := by
    intro a b h
    apply generatedSixth_root_Q_modulation_injective
    have hc := congrArg (fun q : generatedSixthAxisQStabilizer => spinModulation q.val) h
    simpa only [f, cocodeQ_modulation] using hc
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
    Nat.card_le_card_of_injective f hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
