/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGeneratorData

/-! The checked physical matrices are bound to the original genuine actions on every E8 root. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original real coordinate insertion on the physical octad 2052. -/
def generatedTwelfthSectionInsertReal : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 24 → ℝ) where
  toFun a := ![a 0, a 1, a 2, a 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    a 4, a 5, a 6, a 7, 0, 0, 0, 0]
  map_add' a b := by ext i; fin_cases i <;> simp
  map_smul' c a := by ext i; fin_cases i <;> simp

/-- The actual original physical root is its integral local row scaled by the Leech embedding. -/
theorem generatedTwelfthSection_root_insert (r : Fin 120) :
    generatedTwelfthSectionInsertReal (fun i => (leechSeventhE8RootLocal r i : ℝ)) =
      (Real.sqrt 8 : ℝ) • leechSeventhE8RealRoot r := by
  have hn : Real.sqrt 8 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  ext i
  rw [leechSeventhE8RealRoot, leechSeventhE8Root_physical]
  simp only [leechCoordinateEmbedding, Pi.smul_apply, smul_eq_mul]
  unfold generatedFifthFrameInsert generatedTwelfthSectionInsertReal
  fin_cases i <;> simp
  all_goals field_simp

/-- Every original generator acts by the checked half-integral physical matrix on all E8 roots. -/
theorem generatedTwelfthSectionGenerator_real_root (g : Fin 18) (r : Fin 120) :
    (generatedFifthSectionGenerator g).val
        (generatedTwelfthSectionInsertReal (fun i => (leechSeventhE8RootLocal r i : ℝ))) =
      generatedTwelfthSectionInsertReal
        ((1 / 2 : ℝ) •
          (generatedTwelfthSectionGeneratorTwice g).map (Int.castRingHom ℝ) *ᵥ
            (fun i => (leechSeventhE8RootLocal r i : ℝ))) := by
  have hv : (1 / 2 : ℝ) •
      (generatedTwelfthSectionGeneratorTwice g).map (Int.castRingHom ℝ) *ᵥ
        (fun i => (leechSeventhE8RootLocal r i : ℝ)) =
      (leechSeventhE8RootImageSign g r : ℝ) •
        (fun i => (leechSeventhE8RootLocal (leechSeventhE8RootImage g r) i : ℝ)) := by
    ext i
    have h := congrArg (fun v : Fin 8 → ℤ => (v i : ℝ))
      (generatedTwelfthSectionGenerator_root_source g r)
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      Int.cast_sum, Int.cast_mul, Int.cast_ofNat] at h
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      Matrix.map_apply]
    change (1 / 2 : ℝ) *
      (∑ j, (generatedTwelfthSectionGeneratorTwice g i j : ℝ) *
        (leechSeventhE8RootLocal r j : ℝ)) =
      (leechSeventhE8RootImageSign g r : ℝ) * _
    change ∑ j, (generatedTwelfthSectionGeneratorTwice g i j : ℝ) *
      (leechSeventhE8RootLocal r j : ℝ) = _ at h
    linarith
  rw [hv, map_smul, generatedTwelfthSection_root_insert,
    generatedTwelfthSection_root_insert, map_smul, leechSeventhE8RealRoot_action]
  simp only [smul_smul]
  congr 1
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
