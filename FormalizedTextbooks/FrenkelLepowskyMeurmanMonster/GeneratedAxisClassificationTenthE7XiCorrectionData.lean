/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7XiCorrectionPermutation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE8AffineData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderXi

/-! Complete integer data for a genuine correcting Xi move of the Tenth flag. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option maxRecDepth 100000

/-- Complete original integral coordinates in the standard octad. -/
def generatedTenthE7XiLine : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 4, 0, -4, 0, 0, 4, -4, 0, 0, 0, 0, 0, 0, 0, 4, 4]

/-- Complete original integral coordinates in the standard octad. -/
def generatedTenthE7XiNormal : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Complete original integral coordinates in the standard octad. -/
def generatedTenthE7XiRoot : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Complete original integral coordinates in the standard octad. -/
def generatedTenthE7XiNextRoot : Fin 24 → ℤ :=
  ![0, 0, -4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The actual original Golay codeword used for phase correction. -/
def generatedTenthE7XiCode : golayCode :=
  ⟨golayEncoder (golayLabelCoefficients 20), ⟨golayLabelCoefficients 20, rfl⟩⟩

/-- Twice the entire physical corrected matrix, retaining the original code signs. -/
def generatedTenthE7XiCorrectedNumerator : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  (if generatedTenthE7XiCode.val i = 0 then 1 else -1) *
    co1XiNumerator (generatedTenthE7XiInverse i) j

/-- All three original integer vectors have exactly the displayed complete images. -/
theorem generatedTenth_e7_xi_corrected_vectors :
    generatedTenthE7XiCorrectedNumerator *ᵥ generatedTenthE7XiLine =
        (2 : ℤ) • generatedTenthE7XiLine ∧
      generatedTenthE7XiCorrectedNumerator *ᵥ generatedTenthE7XiNormal =
        (2 : ℤ) • generatedTenthE7XiNormal ∧
      generatedTenthE7XiCorrectedNumerator *ᵥ generatedTenthE7XiRoot =
        (2 : ℤ) • generatedTenthE7XiNextRoot := by
  decide +kernel

/-- The corrected numerator has no cross terms between the standard octad
and its complement. -/
theorem generatedTenth_e7_xi_corrected_block : ∀ i j : Fin 24,
    (if i.val < 8 then generatedTenthE7XiCorrectedNumerator i j else 0) =
      (if j.val < 8 then generatedTenthE7XiCorrectedNumerator i j else 0) := by
  decide +kernel

/-- The root image is distinct from both original orientations. -/
theorem generatedTenth_e7_xi_root_moves : generatedTenthE7XiNextRoot ≠ generatedTenthE7XiRoot ∧
    generatedTenthE7XiNextRoot ≠ -generatedTenthE7XiRoot := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
