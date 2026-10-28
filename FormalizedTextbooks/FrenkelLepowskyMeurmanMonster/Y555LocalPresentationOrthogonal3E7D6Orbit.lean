/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact kernel checks and actual source-word bindings for the E7D6 inverse column orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3E7D6OrbitData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
open scoped Matrix

set_option maxHeartbeats 16000000 in
-- These checks verify the exact finite source words and coordinates in the kernel.
/-- All literal E7D6 words have their checked inverse orbit recurrence. -/
theorem y322Orthogonal3E7D6Orbit_checked (i : Fin 126) :
    y322InverseWordOrbitChecked y322E7D6RepresentativeWord
      y322Orthogonal3E7D6Parent y322Orthogonal3E7D6Generator
      y322Orthogonal3E7D6Point y322Orthogonal3E7D6Orbit i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 16000000 in
-- These checks verify the exact finite source words and coordinates in the kernel.
/-- The exact E7D6 column code agrees with its sorted witness. -/
theorem y322Orthogonal3E7D6Code_checked (i : Fin 126) :
    y322Orthogonal3E7D6Code i =
      y322Orthogonal3E7D6SortedCode (y322Orthogonal3E7D6SortPosition i) := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 16000000 in
-- These checks verify the exact finite source words and coordinates in the kernel.
/-- The literal E7D6 column encodings are strictly sorted. -/
theorem y322Orthogonal3E7D6SortedCode_mono : StrictMono y322Orthogonal3E7D6SortedCode := by
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel

set_option maxHeartbeats 16000000 in
-- These checks verify the exact finite source words and coordinates in the kernel.
/-- The E7D6 sorting position has its exact literal inverse. -/
theorem y322Orthogonal3E7D6SortPosition_inverse (i : Fin 126) :
    y322Orthogonal3E7D6InverseSortPosition (y322Orthogonal3E7D6SortPosition i) = i := by
  fin_cases i <;> decide +kernel

/-- The exact original E7D6 source words have their certified actual inverse image columns. -/
theorem y322Orthogonal3E7D6Orbit_source (i : Fin 126) :
    (y322Orthogonal3Hom (y322PositiveWord (y322E7D6RepresentativeWord i)))⁻¹.val *ᵥ
      y322Orthogonal3E7D6Point = y322Orthogonal3E7D6Orbit i :=
  y322InverseWordOrbit_checked_image _ _ _ _ _ y322Orthogonal3E7D6Orbit_checked i

/-- The exact inverse column images of the actual original E7D6 source words are distinct. -/
theorem y322Orthogonal3E7D6Orbit_injective : Function.Injective y322Orthogonal3E7D6Orbit := by
  intro i j hij
  apply y322SortedFiniteCode_injective _ _ _ y322Orthogonal3E7D6SortedCode_mono
    y322Orthogonal3E7D6SortPosition_inverse
  change y322Orthogonal3E7D6SortedCode (y322Orthogonal3E7D6SortPosition i) =
    y322Orthogonal3E7D6SortedCode (y322Orthogonal3E7D6SortPosition j)
  rw [← y322Orthogonal3E7D6Code_checked, ← y322Orthogonal3E7D6Code_checked]
  simp only [y322Orthogonal3E7D6Code, hij]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
