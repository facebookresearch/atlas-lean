/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTriality

/-! Actual triality matrix coordinates depend only on the complete original matrix and short source constituents. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Complete actual matrix and short constituents suffice to determine every original forward matrix entry. -/
theorem generatedAxisGlobalRationalMatrixShort_actual (x : GriessSpace)
    (a : GeneratedAxisGlobalRationalPacket)
    (hA : (griessConwayEncode x).1 = a.1.map (Rat.castHom ℝ))
    (hC : ∀ r, (griessConwayEncode x).2.1 r = (a.2.1 r : ℝ)) :
    (griessConwayEncode (sExtra x)).1 =
      (generatedAxisGlobalRationalTriality a).1.map (Rat.castHom ℝ) := by
  rw [generatedAxisGlobalRawTrialityFormula_actual]
  ext i j
  simp only [generatedAxisGlobalRawTrialityFormula, generatedAxisGlobalRawTrialityMatrix,
    generatedAxisGlobalRationalTriality, generatedAxisGlobalTrialityMatrixQ, Matrix.map_apply]
  split_ifs with h
  · exact congrArg (fun A : Matrix (Fin 24) (Fin 24) ℝ => A i i) hA
  · rw [generatedAxisGlobalFinitePairIndex_actual i j h, hC, hC]
    simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
