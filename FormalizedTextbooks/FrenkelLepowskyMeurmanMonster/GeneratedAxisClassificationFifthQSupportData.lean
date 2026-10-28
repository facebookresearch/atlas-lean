/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthTensor

/-! Bounded actual dictionary support and modulation certificates for the fifth tensor. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual binary spin coordinates of a low preferred dictionary label. -/
def generatedFifthSpinLow (d : Fin 2048) : SpinIndex :=
  golayLabelCoefficients ⟨d.val, by omega⟩

/-- The eight actual low dictionary labels occurring in spatial column 19. -/
def generatedFifthColumnLabels : Fin 8 → Fin 2048 :=
  ![1721, 1713, 1971, 1969, 1412, 1077, 1082, 1413]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check the bounded actual binary dictionary and phase certificate.
/-- The displayed eight entries are exactly the genuine column-19 dictionary support. -/
theorem generatedFifth_column_labels_certificate : ∀ d : Fin 2048,
    (∃ j : Fin 64, generatedFifthOddRootOutputData j = (d, 19)) ↔
      ∃ k : Fin 8, generatedFifthColumnLabels k = d := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check the bounded actual binary dictionary and phase certificate.
/-- No nontrivial low translation preserves the eight actual dictionary labels. -/
theorem generatedFifth_column_period_certificate : ∀ k : Fin 8,
    (∀ j : Fin 8, ∃ l : Fin 8,
      generatedFifthSpinLow (generatedFifthColumnLabels l) =
        generatedFifthSpinLow (generatedFifthColumnLabels j) +
          generatedFifthSpinLow (generatedFifthColumnLabels k) +
            generatedFifthSpinLow (generatedFifthColumnLabels 0)) → k = 0 := by
  decide +kernel

/-- The 16 actual binary modulation labels annihilating all dictionary differences. -/
def generatedFifthModulationLabels : Fin 16 → Fin 4096 :=
  ![0, 48, 64, 112, 656, 672, 720, 736,
    1024, 1072, 1088, 1136, 1680, 1696, 1744, 1760]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
-- Check the bounded actual binary dictionary and phase certificate.
/-- The displayed 16 modulations exactly solve all 64 actual support-difference equations. -/
theorem generatedFifth_modulation_certificate : ∀ m : Fin 4096,
    ((golayLabelCoefficients m) 11 = 0 ∧ ∀ j : Fin 64,
      spinDot (golayLabelCoefficients m)
        (generatedFifthSpinLow (generatedFifthOddRootOutputData j).1 +
          generatedFifthSpinLow (generatedFifthColumnLabels 0)) = 0) ↔
      ∃ k : Fin 16, generatedFifthModulationLabels k = m := by
  decide +kernel

/-- The displayed modulations are distinct actual binary labels. -/
theorem generatedFifth_modulation_labels_injective :
    Function.Injective generatedFifthModulationLabels := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
