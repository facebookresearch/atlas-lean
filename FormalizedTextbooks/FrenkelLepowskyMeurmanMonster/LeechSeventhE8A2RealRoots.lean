/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2RootCatalog

/-! The finite E8 roots in their original normalized physical real coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original physical root vector, normalized by the existing Leech embedding. -/
def leechSeventhE8RealRoot (r : Fin 120) : Fin 24 → ℝ :=
  leechCoordinateEmbedding (leechSeventhE8Root r).val

/-- Each genuine finite physical root has squared norm four. -/
theorem leechSeventhE8RealRoot_norm (r : Fin 120) :
    stdPairingFun (leechSeventhE8RealRoot r) (leechSeventhE8RealRoot r) = 4 := by
  rw [leechSeventhE8RealRoot, leechEmbedding_pairing, leechSeventhE8Root_norm]
  norm_num

/-- Every signed finite image is the actual original real spatial action. -/
theorem leechSeventhE8RealRoot_action (g : Fin 18) (r : Fin 120) :
    (generatedFifthSectionGenerator g).val (leechSeventhE8RealRoot r) =
      (leechSeventhE8RootImageSign g r : ℝ) •
        leechSeventhE8RealRoot (leechSeventhE8RootImage g r) := by
  rw [leechSeventhE8RealRoot, ← leechIntegralAction_embedding,
    leechSeventhE8Root_action]
  ext i
  simp [leechCoordinateEmbedding, leechSeventhE8RealRoot, smul_eq_mul]
  ring

/-- The original finite catalogue differs from its preferred short vector only by orientation. -/
theorem leechSeventhE8RealRoot_label_sign (r : Fin 120) :
    leechSeventhE8RealRoot r = griessShortVector (leechSeventhE8RootLabel r) ∨
      leechSeventhE8RealRoot r = -griessShortVector (leechSeventhE8RootLabel r) := by
  rcases leechSeventhE8Root_label_sign r with h | h
  · left
    rw [leechSeventhE8RealRoot, h]
    rfl
  · right
    rw [leechSeventhE8RealRoot, h]
    rw [Submodule.coe_neg, map_neg]
    rfl

private theorem insert_pairing (v w : Fin 8 → ℤ) :
    stdPairingFun (leechCoordinateEmbedding (generatedFifthFrameInsert v))
      (leechCoordinateEmbedding (generatedFifthFrameInsert w)) =
        (∑ i, (v i : ℝ) * (w i : ℝ)) / 8 := by
  have h : (Real.sqrt 8) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 8 ≠ 0 := by positivity
  simp [stdPairingFun, leechCoordinateEmbedding, generatedFifthFrameInsert,
    Fin.sum_univ_succ]
  field_simp
  rw [h]
  ring

/-- Actual physical root pairings are the finite integral pairings divided by eight. -/
theorem leechSeventhE8RealRoot_pairing (r s : Fin 120) :
    stdPairingFun (leechSeventhE8RealRoot r) (leechSeventhE8RealRoot s) =
      (∑ i, leechSeventhE8RootLocal r i * leechSeventhE8RootLocal s i : ℤ) / (8 : ℝ) := by
  rw [leechSeventhE8RealRoot, leechSeventhE8RealRoot,
    leechSeventhE8Root_physical, leechSeventhE8Root_physical, insert_pairing]
  simp only [Int.cast_sum, Int.cast_mul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
