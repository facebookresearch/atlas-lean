/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact binary code actions and zero-basis Parker phases of the source permutation p43549632.
Seysen, arXiv:2002.10921v3, §4.2: the standard representative has zero sign
on each chosen code basis vector; its quadratic polarization is (4.0.1).
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerPermutation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ParkerCyclicPhase

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Forward and inverse code matrices, from the actual checked generator images. -/
def monsterNortonSingerCodeMatrix (k : Fin 2) :
    Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  fun i j => golayLabelCoefficients (monsterNortonSingerPermCodeImages k j) i

set_option maxHeartbeats 2000000 in
-- Check both products of the explicit 12 by 12 matrix pair.
/-- The finite forward and inverse matrices really are inverses. -/
theorem monsterNortonSingerCode_inverse : ∀ k : Fin 1,
    monsterNortonSingerCodeMatrix (Fin.natAdd 1 k) *
      monsterNortonSingerCodeMatrix (Fin.castAdd 1 k) = 1 ∧
    monsterNortonSingerCodeMatrix (Fin.castAdd 1 k) *
      monsterNortonSingerCodeMatrix (Fin.natAdd 1 k) = 1 := by
  decide +kernel

/-- The actual linear equivalence induced on the source code coefficients. -/
def monsterNortonSingerCode (k : Fin 1) : SpinIndex ≃ₗ[ZMod 2] SpinIndex where
  toFun a := monsterNortonSingerCodeMatrix (Fin.castAdd 1 k) *ᵥ a
  invFun a := monsterNortonSingerCodeMatrix (Fin.natAdd 1 k) *ᵥ a
  left_inv a := by
    change monsterNortonSingerCodeMatrix (Fin.natAdd 1 k) *ᵥ
      (monsterNortonSingerCodeMatrix (Fin.castAdd 1 k) *ᵥ a) = a
    rw [Matrix.mulVec_mulVec, (monsterNortonSingerCode_inverse k).1]
    exact Matrix.one_mulVec a
  right_inv a := by
    change monsterNortonSingerCodeMatrix (Fin.castAdd 1 k) *ᵥ
      (monsterNortonSingerCodeMatrix (Fin.natAdd 1 k) *ᵥ a) = a
    rw [Matrix.mulVec_mulVec, (monsterNortonSingerCode_inverse k).2]
    exact Matrix.one_mulVec a
  map_add' _ _ := Matrix.mulVec_add _ _ _
  map_smul' _ _ := Matrix.mulVec_smul _ _ _

/-- Basis vectors are mapped to the checked source code labels. -/
theorem monsterNortonSingerCode_single (k : Fin 1) (j : Fin 12) :
    monsterNortonSingerCode k (Pi.single j 1) =
      golayLabelCoefficients (monsterNortonSingerPermCodeImages (Fin.castAdd 1 k) j) := by
  ext i
  change (∑ l : Fin 12, _ * (Pi.single j 1 : SpinIndex) l) = _
  simp [Pi.single_apply, monsterNortonSingerCodeMatrix]

/-- The code linear equivalence matches the genuine physical coordinate permutation. -/
theorem monsterNortonSingerCode_encoder (k : Fin 1) (a : SpinIndex) :
    golayEncoder (monsterNortonSingerCode k a) =
      golayPermute (monsterNortonSingerPermutation k) (golayEncoder a) := by
  let L : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
    { toFun := golayPermute (monsterNortonSingerPermutation k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h : golayEncoder.comp (monsterNortonSingerCode k).toLinearMap =
      L.comp golayEncoder := by
    apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
    intro j
    simp only [LinearMap.comp_apply, Pi.basisFun_apply, LinearEquiv.coe_coe]
    rw [monsterNortonSingerCode_single]
    exact (monsterNortonSingerPermutation_code_certificate k j).1.symm
  exact LinearMap.congr_fun h a

/-- The upper-triangular coefficients of the standard Parker lift's quadratic sign. -/
def monsterNortonSingerPhaseMatrix (k : Fin 1) :
    Matrix (Fin 12) (Fin 12) (ZMod 2) := fun i j =>
  if i < j then
    spinDot (sourceCodeThetaPolynomial (monsterNortonSingerCode k (Pi.single i 1)))
      (monsterNortonSingerCode k (Pi.single j 1)) +
        spinDot (sourceCodeTheta i) (Pi.single j 1)
  else 0

/-- The exact zero-basis quadratic phase, with no chosen lift or sign assumption. -/
def monsterNortonSingerPhase (k : Fin 1) (a : SpinIndex) : ZMod 2 :=
  ∑ i, ∑ j, a i * a j * monsterNortonSingerPhaseMatrix k i j

/-- The standard representative has the required zero phases on all code basis vectors. -/
theorem monsterNortonSingerPhase_single (k : Fin 1) (i : Fin 12) :
    monsterNortonSingerPhase k (Pi.single i 1) = 0 := by
  unfold monsterNortonSingerPhase
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro l _
  by_cases hj : j = i <;> by_cases hl : l = i <;>
    simp [hj, hl, monsterNortonSingerPhaseMatrix]

/-- Compact row encoding of the source permutation’s standard lift. -/
def monsterNortonSingerPhaseRows : Fin 1 → Fin 12 → ℕ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 4000000 in
-- Check the discovery rows against the actual theta formula and checked code images.
/-- The row data are certificates for the actual Parker quadratic phase coefficients. -/
theorem monsterNortonSingerPhase_certificate : ∀ k i j,
    monsterNortonSingerPhaseMatrix k i j =
      golayBooleanCast ((monsterNortonSingerPhaseRows k i).testBit j.val) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
