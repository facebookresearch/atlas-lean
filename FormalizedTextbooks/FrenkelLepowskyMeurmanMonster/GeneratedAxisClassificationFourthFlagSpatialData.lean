/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthFlagSpinData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagMonomialPermutation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

/-! The literal correction's actual integral-basis action and compatible spin lift. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Integral basis coordinates of the genuine correction permutation. -/
def generatedFourthFlagLiftBasis : Matrix (Fin 24) (Fin 24) ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 3, 3, 4, 0, 4, 3, 3, 4, -11, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0, -1, -1, -1, -1, 2, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 2, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1, 2, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, -1, 3, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, -1, -1, -1, 2, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, 0, -1, -1, -1, 0, -1, -1, -1, -1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, -1, -1, -1, 0, -1, -1, -1, -1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, -1, 0, 0, 0, 0, -1, -1, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, -1, -1, -1, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1, 1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1]]

/-- The correction acts on the actual lattice basis by this checked integer matrix. -/
theorem generatedFourth_flag_lift_basis_certificate :
    (fun i j => leechBasisMatrix (generatedFourthFlagCorrectionCoordinates i) j) =
      leechBasisMatrix * generatedFourthFlagLiftBasis := by
  decide +kernel

/-- The checked basis certificate extends to every actual integral vector. -/
theorem generatedFourth_flag_lift_embedding (z : Fin 24 → ℤ) :
    generatedFourthFlagCorrectionLeech.val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ (generatedFourthFlagLiftBasis *ᵥ z)) := by
  have hc : (fun i => (leechBasisMatrix *ᵥ z)
      (generatedFourthFlagCorrectionCoordinates i)) =
      leechBasisMatrix *ᵥ (generatedFourthFlagLiftBasis *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, ← generatedFourth_flag_lift_basis_certificate]
    rfl
  funext i
  change ((leechBasisMatrix *ᵥ z) (generatedFourthFlagCorrectionCoordinates i) : ℝ) /
      Real.sqrt 8 = ((leechBasisMatrix *ᵥ (generatedFourthFlagLiftBasis *ᵥ z)) i : ℝ) /
      Real.sqrt 8
  rw [congrFun hc i]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Every binary entry is checked from the actual full spin image and actual integral basis.
/-- The spin lift has exactly the correction's genuine binary quotient action. -/
theorem generatedFourth_flag_lift_binary_certificate :
    generatedFourthFlagLiftBinaryMatrix = leechHyperbolicInverse *
      generatedFourthFlagLiftBasis.map (Int.castRingHom (ZMod 2)) * leechHyperbolicMatrix := by
  decide +kernel

/-- The actual paired operators agree on the genuine quotient Q/Z(Q)=Λ/2Λ. -/
theorem generatedFourth_flag_lift_compatibility :
    spinBinaryAction generatedFourthFlagLiftSpin =
      leechBinaryAction generatedFourthFlagCorrectionLeech := by
  apply LinearEquiv.toLinearMap_injective
  rw [generatedFourth_flag_lift_binary_linear, generatedFourth_flag_lift_binary_certificate]
  apply LinearMap.ext
  intro v
  exact (leechBinaryAction_of_basis_certificate _ _
    generatedFourth_flag_lift_embedding v).symm

/-- The genuine correction permutation paired with its fully checked actual spin lift. -/
noncomputable def generatedFourthFlagCorrectionFiber : localFiberSubgroup :=
  ⟨(generatedFourthFlagLiftSpin, generatedFourthFlagCorrectionLeech),
    generatedFourth_flag_lift_compatibility⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
