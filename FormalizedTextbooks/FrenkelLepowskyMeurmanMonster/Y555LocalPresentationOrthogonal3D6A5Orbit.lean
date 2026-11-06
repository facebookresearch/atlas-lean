/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact kernel checks and actual source-word bindings for the D6A5 inverse column orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3D6A5OrbitData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
open scoped Matrix

set_option maxHeartbeats 16000000 in
-- These checks verify the exact finite source words and coordinates in the kernel.
/-- All literal D6A5 words have their checked inverse orbit recurrence. -/
theorem y322Orthogonal3D6A5Orbit_checked (i : Fin 32) :
    y322InverseWordOrbitChecked y322D6A5RepresentativeWord
      y322Orthogonal3D6A5Parent y322Orthogonal3D6A5Generator
      y322Orthogonal3D6A5Point y322Orthogonal3D6A5Orbit i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 16000000 in
-- These checks verify the exact finite source words and coordinates in the kernel.
/-- The exact D6A5 column code agrees with its sorted witness. -/
theorem y322Orthogonal3D6A5Code_checked (i : Fin 32) :
    y322Orthogonal3D6A5Code i =
      y322Orthogonal3D6A5SortedCode (y322Orthogonal3D6A5SortPosition i) := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 16000000 in
-- These checks verify the exact finite source words and coordinates in the kernel.
/-- The literal D6A5 column encodings are strictly sorted. -/
theorem y322Orthogonal3D6A5SortedCode_mono : StrictMono y322Orthogonal3D6A5SortedCode := by
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel

set_option maxHeartbeats 16000000 in
-- These checks verify the exact finite source words and coordinates in the kernel.
/-- The D6A5 sorting position has its exact literal inverse. -/
theorem y322Orthogonal3D6A5SortPosition_inverse (i : Fin 32) :
    y322Orthogonal3D6A5InverseSortPosition (y322Orthogonal3D6A5SortPosition i) = i := by
  fin_cases i <;> decide +kernel

/-- The exact original D6A5 source words have their certified actual inverse image columns. -/
theorem y322Orthogonal3D6A5Orbit_source (i : Fin 32) :
    (y322Orthogonal3Hom (y322PositiveWord (y322D6A5RepresentativeWord i)))⁻¹.val *ᵥ
      y322Orthogonal3D6A5Point = y322Orthogonal3D6A5Orbit i :=
  y322InverseWordOrbit_checked_image _ _ _ _ _ y322Orthogonal3D6A5Orbit_checked i

/-- The exact inverse column images of the actual original D6A5 source words are distinct. -/
theorem y322Orthogonal3D6A5Orbit_injective : Function.Injective y322Orthogonal3D6A5Orbit := by
  intro i j hij
  apply y322SortedFiniteCode_injective _ _ _ y322Orthogonal3D6A5SortedCode_mono
    y322Orthogonal3D6A5SortPosition_inverse
  change y322Orthogonal3D6A5SortedCode (y322Orthogonal3D6A5SortPosition i) =
    y322Orthogonal3D6A5SortedCode (y322Orthogonal3D6A5SortPosition j)
  rw [← y322Orthogonal3D6A5Code_checked, ← y322Orthogonal3D6A5Code_checked]
  simp only [y322Orthogonal3D6A5Code, hij]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
