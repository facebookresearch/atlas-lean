/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadIntegralSpanData

/-! Exact integer reconstruction in the eight-root basis of a coordinate octad section. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000 in
-- Expand only the eight local root coordinates and their exact divisibility equations.
/-- The genuine coordinate-octad congruences imply integer membership in the root basis. -/
theorem generatedFifthFrame_root_coordinates (v : Fin 8 → ℤ)
    (h2 : 2 ∣ v 7) (h4 : ∀ i, 4 ∣ v 7 - v i) (h8 : 8 ∣ ∑ i, v i) :
    generatedOctadIntegerRootMatrix *ᵥ generatedOctadIntegerRootCoordinates v = v := by
  have hp (i : Fin 8) : 4 * ((v 7 - v i) / 4) = v 7 - v i :=
    Int.mul_ediv_cancel' (h4 i)
  have hlast : 2 * (v 7 / 2) = v 7 := Int.mul_ediv_cancel' h2
  have hb : 8 * (((∑ i, v i) - 8 * v 7) / 8) = (∑ i, v i) - 8 * v 7 :=
    Int.mul_ediv_cancel' (dvd_sub h8 (dvd_mul_right 8 (v 7)))
  have h1 := hp 1
  have htwo := hp 2
  have h3 := hp 3
  have hfour := hp 4
  have h5 := hp 5
  have h6 := hp 6
  simp [Fin.sum_univ_succ] at hb
  ext i
  fin_cases i <;>
    simp [generatedOctadIntegerRootMatrix, generatedOctadIntegerRootCoordinates,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
