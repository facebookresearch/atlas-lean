/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGeneratorAction

/-! Eight original physical roots span the entire actual E8 coordinate section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Original finite root addresses forming a physical section basis. -/
def generatedTwelfthSectionBasisRoots : Fin 8 → Fin 120 := ![0, 1, 2, 3, 4, 5, 6, 28]

/-- Eight times the exact inverse of the original physical root-column matrix. -/
def generatedTwelfthSectionBasisInverse : Matrix (Fin 8) (Fin 8) ℤ := ![
  ![1, -1, 1, 1, 1, 1, 1, 1],
  ![0, 0, -2, 0, 0, 0, 0, 0],
  ![0, 0, 0, -2, 0, 0, 0, 0],
  ![0, 0, 0, 0, -2, 0, 0, 0],
  ![0, 0, 0, 0, 0, -2, 0, 0],
  ![0, 0, 0, 0, 0, 0, -2, 0],
  ![0, 0, 0, 0, 0, 0, 0, -2],
  ![1, 1, 1, 1, 1, 1, 1, 1]
]

set_option maxRecDepth 10000 in
-- Check the exact finite inverse against the original physical catalogue coordinates.
/-- The original inverse reconstructs every physical coordinate unit vector. -/
theorem generatedTwelfthSection_basis_integer : ∀ j : Fin 8,
    ∑ a, generatedTwelfthSectionBasisInverse a j •
      leechSeventhE8RootLocal (generatedTwelfthSectionBasisRoots a) =
        (8 : ℤ) • (Pi.single j 1 : Fin 8 → ℤ) := by
  decide +kernel

/-- The actual root catalogue spans every real physical coordinate in the section. -/
theorem generatedTwelfthSection_basis_real (j : Fin 8) :
    (Pi.single j 1 : Fin 8 → ℝ) =
      ∑ a, ((generatedTwelfthSectionBasisInverse a j : ℝ) / 8) •
        (fun i => (leechSeventhE8RootLocal (generatedTwelfthSectionBasisRoots a) i : ℝ)) := by
  ext i
  have h := congrArg (fun v : Fin 8 → ℤ => (v i : ℝ))
    (generatedTwelfthSection_basis_integer j)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum,
    Int.cast_mul, Int.cast_ofNat, Pi.single_apply] at h
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    div_mul_eq_mul_div, ← Finset.sum_div]
  split_ifs at h ⊢ <;> norm_num at h ⊢ <;> linarith

/-- The checked matrix is the entire genuine action on every real section vector. -/
theorem generatedTwelfthSectionGenerator_real_action (g : Fin 18) (v : Fin 8 → ℝ) :
    (generatedFifthSectionGenerator g).val (generatedTwelfthSectionInsertReal v) =
      generatedTwelfthSectionInsertReal
        ((1 / 2 : ℝ) • (generatedTwelfthSectionGeneratorTwice g).map (Int.castRingHom ℝ) *ᵥ v) := by
  have h : (generatedFifthSectionGenerator g).val.toLinearMap.comp
      generatedTwelfthSectionInsertReal =
      generatedTwelfthSectionInsertReal.comp
        (((1 / 2 : ℝ) • (generatedTwelfthSectionGeneratorTwice g).map
          (Int.castRingHom ℝ)).mulVecLin) := by
    apply (Pi.basisFun ℝ (Fin 8)).ext
    intro j
    simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      Matrix.mulVecLin_apply, Matrix.smul_mulVec]
    rw [generatedTwelfthSection_basis_real]
    simp only [map_sum, map_smul, Matrix.mulVec_sum, Matrix.mulVec_smul,
      generatedTwelfthSectionGenerator_real_root]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [smul_smul, smul_smul, mul_comm]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Matrix.mulVecLin_apply, Matrix.smul_mulVec] using LinearMap.congr_fun h v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
