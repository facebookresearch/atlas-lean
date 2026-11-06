/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2RootCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlags

/-! The finite coordinates and signs are actual lattice roots and actual section actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The genuine integral combination of the existing eight lattice roots. -/
def leechSeventhE8RootSum : (Fin 8 → ℤ) →ₗ[ℤ] leechIntegral where
  toFun a := ∑ j, a j • generatedFifthFrameRoot j
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a b := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.smul_sum, smul_smul]

/-- Each finite root representative is an actual vector in the Leech lattice. -/
def leechSeventhE8Root (r : Fin 120) : leechIntegral :=
  leechSeventhE8RootSum (leechSeventhE8RootCoefficients r)

/-- The actual root combination has its checked original physical coordinates. -/
theorem leechSeventhE8Root_physical (r : Fin 120) :
    (leechSeventhE8Root r).val = generatedFifthFrameInsert (leechSeventhE8RootLocal r) := by
  have h := generatedFifthFrame_insert_root_sum (leechSeventhE8RootCoefficients r)
  rw [leechSeventhE8Root_local_certificate] at h
  exact h.symm

private theorem insert_norm (v : Fin 8 → ℤ) :
    leechSquareSum (generatedFifthFrameInsert v) = ∑ j, (v j) ^ 2 := by
  simp [leechSquareSum, generatedFifthFrameInsert, Fin.sum_univ_succ]

/-- Every finite representative is an actual norm-four physical short vector. -/
theorem leechSeventhE8Root_norm (r : Fin 120) :
    leechSquareSum (leechSeventhE8Root r).val = 32 := by
  rw [leechSeventhE8Root_physical, insert_norm, leechSeventhE8Root_norm_certificate]

private theorem sum_single (j : Fin 8) :
    leechSeventhE8RootSum (Pi.single j 1) = generatedFifthFrameRoot j := by
  simp [leechSeventhE8RootSum, Pi.single_apply, ite_smul]

/-- The genuine original action on every root combination is its verified integral matrix. -/
theorem leechSeventhE8RootSum_action (g : Fin 18) (a : Fin 8 → ℤ) :
    leechIntegralAction (generatedFifthSectionGenerator g) (leechSeventhE8RootSum a) =
      leechSeventhE8RootSum (generatedFifthSectionGeneratorInteger g *ᵥ a) := by
  have h : (leechIntegralAction (generatedFifthSectionGenerator g)).toLinearMap.comp
      leechSeventhE8RootSum = leechSeventhE8RootSum.comp
        (generatedFifthSectionGeneratorInteger g).mulVecLin := by
    apply (Pi.basisFun ℤ (Fin 8)).ext
    intro j
    simp only [LinearMap.comp_apply, Pi.basisFun_apply, sum_single,
      LinearEquiv.coe_toLinearMap, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
    exact generatedFifthSectionGenerator_root_image g j
  exact LinearMap.congr_fun h a

/-- Every finite signed root image is the genuine original section-generator action. -/
theorem leechSeventhE8Root_action (g : Fin 18) (r : Fin 120) :
    leechIntegralAction (generatedFifthSectionGenerator g) (leechSeventhE8Root r) =
      leechSeventhE8RootImageSign g r • leechSeventhE8Root (leechSeventhE8RootImage g r) := by
  rw [leechSeventhE8Root, leechSeventhE8RootSum_action,
    leechSeventhE8Root_image_certificate, map_smul]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
