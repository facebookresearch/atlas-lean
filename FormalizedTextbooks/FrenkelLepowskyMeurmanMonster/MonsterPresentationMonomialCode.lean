/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact binary code actions and zero-basis Parker phases of two source permutations.
Seysen, arXiv:2002.10921v3, §4.2: the standard representative has zero sign
on each chosen code basis vector; its quadratic polarization is (4.0.1).
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitPermutations
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ParkerCyclicPhase

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Forward and inverse code matrices, from the actual checked generator images. -/
def monsterSourcePermutationCodeMatrix (k : Fin 4) :
    Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  fun i j => golayLabelCoefficients (omegaOrbitPermCodeImages k j) i

set_option maxHeartbeats 2000000 in
-- Check both products of the two explicit 12 by 12 matrix pairs.
/-- The finite forward and inverse matrices really are inverses. -/
theorem monsterSourcePermutationCode_inverse : ∀ k : Fin 2,
    monsterSourcePermutationCodeMatrix (Fin.natAdd 2 k) *
      monsterSourcePermutationCodeMatrix (Fin.castAdd 2 k) = 1 ∧
    monsterSourcePermutationCodeMatrix (Fin.castAdd 2 k) *
      monsterSourcePermutationCodeMatrix (Fin.natAdd 2 k) = 1 := by
  decide +kernel

/-- The actual linear equivalence induced on the source code coefficients. -/
def monsterSourcePermutationCode (k : Fin 2) : SpinIndex ≃ₗ[ZMod 2] SpinIndex where
  toFun a := monsterSourcePermutationCodeMatrix (Fin.castAdd 2 k) *ᵥ a
  invFun a := monsterSourcePermutationCodeMatrix (Fin.natAdd 2 k) *ᵥ a
  left_inv a := by
    change monsterSourcePermutationCodeMatrix (Fin.natAdd 2 k) *ᵥ
      (monsterSourcePermutationCodeMatrix (Fin.castAdd 2 k) *ᵥ a) = a
    rw [Matrix.mulVec_mulVec, (monsterSourcePermutationCode_inverse k).1]
    exact Matrix.one_mulVec a
  right_inv a := by
    change monsterSourcePermutationCodeMatrix (Fin.castAdd 2 k) *ᵥ
      (monsterSourcePermutationCodeMatrix (Fin.natAdd 2 k) *ᵥ a) = a
    rw [Matrix.mulVec_mulVec, (monsterSourcePermutationCode_inverse k).2]
    exact Matrix.one_mulVec a
  map_add' _ _ := Matrix.mulVec_add _ _ _
  map_smul' _ _ := Matrix.mulVec_smul _ _ _

/-- Basis vectors are mapped to the checked source code labels. -/
theorem monsterSourcePermutationCode_single (k : Fin 2) (j : Fin 12) :
    monsterSourcePermutationCode k (Pi.single j 1) =
      golayLabelCoefficients (omegaOrbitPermCodeImages (Fin.castAdd 2 k) j) := by
  ext i
  change (∑ l : Fin 12, _ * (Pi.single j 1 : SpinIndex) l) = _
  simp [Pi.single_apply, monsterSourcePermutationCodeMatrix]

/-- The code linear equivalence matches the genuine physical coordinate permutation. -/
theorem monsterSourcePermutationCode_encoder (k : Fin 2) (a : SpinIndex) :
    golayEncoder (monsterSourcePermutationCode k a) =
      golayPermute (omegaOrbitPermutation k) (golayEncoder a) := by
  let L : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
    { toFun := golayPermute (omegaOrbitPermutation k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h : golayEncoder.comp (monsterSourcePermutationCode k).toLinearMap =
      L.comp golayEncoder := by
    apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
    intro j
    simp only [LinearMap.comp_apply, Pi.basisFun_apply, LinearEquiv.coe_coe]
    rw [monsterSourcePermutationCode_single]
    exact (omegaOrbitPermutation_code_certificate k j).1.symm
  exact LinearMap.congr_fun h a

/-- The upper-triangular coefficients of the standard Parker lift's quadratic sign. -/
def monsterSourcePermutationPhaseMatrix (k : Fin 2) :
    Matrix (Fin 12) (Fin 12) (ZMod 2) := fun i j =>
  if i < j then
    spinDot (sourceCodeThetaPolynomial (monsterSourcePermutationCode k (Pi.single i 1)))
      (monsterSourcePermutationCode k (Pi.single j 1)) +
        spinDot (sourceCodeTheta i) (Pi.single j 1)
  else 0

/-- The exact zero-basis quadratic phase, with no chosen lift or sign assumption. -/
def monsterSourcePermutationPhase (k : Fin 2) (a : SpinIndex) : ZMod 2 :=
  ∑ i, ∑ j, a i * a j * monsterSourcePermutationPhaseMatrix k i j

/-- The standard representative has the required zero phases on all code basis vectors. -/
theorem monsterSourcePermutationPhase_single (k : Fin 2) (i : Fin 12) :
    monsterSourcePermutationPhase k (Pi.single i 1) = 0 := by
  unfold monsterSourcePermutationPhase
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro l _
  by_cases hj : j = i <;> by_cases hl : l = i <;>
    simp [hj, hl, monsterSourcePermutationPhaseMatrix]

/-- Compact row encodings discovered from the public AutPL runtime's two standard lifts. -/
def monsterSourcePermutationPhaseRows : Fin 2 → Fin 12 → ℕ :=
  ![![546, 12, 728, 624, 0, 512, 0, 512, 512, 1024, 0, 0],
    ![828, 252, 8, 0, 512, 256, 512, 256, 0, 0, 0, 0]]

set_option maxHeartbeats 4000000 in
-- Check the discovery rows against the actual theta formula and checked code images.
/-- The row data are certificates for the actual Parker quadratic phase coefficients. -/
theorem monsterSourcePermutationPhase_certificate : ∀ k i j,
    monsterSourcePermutationPhaseMatrix k i j =
      golayBooleanCast ((monsterSourcePermutationPhaseRows k i).testBit j.val) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
