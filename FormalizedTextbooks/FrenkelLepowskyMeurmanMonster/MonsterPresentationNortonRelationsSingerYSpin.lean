/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual preferred Y-spin covariance under the source Singer permutation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerYQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerYCoefficient
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerSpinCoefficient
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQCoordinateEvaluation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Relabeling by the actual linear Singer permutation preserves the zero spin coordinate. -/
theorem monsterNortonSingerSpin_apply_zero (x : SpinSpace) :
    monsterNortonSingerSpin.val x 0 = x 0 := by
  change x ((monsterNortonSingerCode 0).symm 0) = x 0
  rw [map_zero]

private theorem relabeling_single_zero {ι : Type*} [DecidableEq ι] [Zero ι]
    (P : Equiv.Perm ι) (hP : P 0 = 0) :
    (fun t => (Pi.single (0 : ι) (1 : ℝ) : ι → ℝ) (P.symm t)) =
      (Pi.single 0 1 : ι → ℝ) := by
  funext t
  have he : P.symm t = 0 ↔ t = 0 := by
    constructor
    · intro h
      have hp := congrArg P h
      simpa only [Equiv.apply_symm_apply, hP] using hp
    · intro h
      subst t
      apply P.injective
      rw [Equiv.apply_symm_apply, hP]
  simp only [Pi.single_apply, he]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Specialize the abstract relabeling proof without expanding the 4096-point enumeration.
/-- The genuine spin permutation fixes the delta vector at zero. -/
theorem monsterNortonSingerSpin_delta_zero :
    monsterNortonSingerSpin.val (Pi.single (0 : SpinIndex) 1) = Pi.single 0 1 := by
  have hp : (monsterNortonSingerCode 0).toEquiv 0 = 0 :=
    (monsterNortonSingerCode 0).map_zero
  change (fun t => (Pi.single (0 : SpinIndex) (1 : ℝ) : SpinSpace)
    ((monsterNortonSingerCode 0).symm t)) = _
  exact relabeling_single_zero (monsterNortonSingerCode 0).toEquiv hp

set_option maxRecDepth 10000 in
/-- The actual conjugation maps of the preferred spin products agree on all of Q. -/
theorem monsterNortonSingerY_basis_conjugation (a : Fin 11) :
    spinConjugation (monsterNortonSingerSpin *
      monsterNortonYSpin (monsterNortonSingerYBasisSource a)) =
      spinConjugation (monsterNortonYSpin (monsterNortonSingerYBasisTarget a) *
        monsterNortonSingerSpin) := by
  have hi (i : Fin 24) :
      spinConjugation (monsterNortonSingerSpin *
        monsterNortonYSpin (monsterNortonSingerYBasisSource a)) (qCoordinateGenerator i) =
      spinConjugation (monsterNortonYSpin (monsterNortonSingerYBasisTarget a) *
        monsterNortonSingerSpin) (qCoordinateGenerator i) := by
    simp only [map_mul]
    change spinConjugation monsterNortonSingerSpin
      (spinConjugation (monsterNortonYSpin (monsterNortonSingerYBasisSource a))
        (qCoordinateGenerator i)) =
      spinConjugation (monsterNortonYSpin (monsterNortonSingerYBasisTarget a))
        (spinConjugation monsterNortonSingerSpin (qCoordinateGenerator i))
    rw [monsterNortonSingerSpin_conjugation, monsterNortonYSpin_conjugation,
      monsterNortonYSpin_conjugation, monsterNortonSingerSpin_conjugation]
    exact monsterNortonSingerY_basis_coordinate_certificate a i
  let images : Fin 24 → Q := fun i =>
    spinConjugation (monsterNortonSingerSpin *
      monsterNortonYSpin (monsterNortonSingerYBasisSource a)) (qCoordinateGenerator i)
  apply DFunLike.ext
  intro q
  rw [monsterNortonCoordinateEvaluation_eq _ images (fun _ => rfl),
    monsterNortonCoordinateEvaluation_eq _ images (fun i => (hi i).symm)]

/-- The preferred actual Y-spin operators satisfy full Singer covariance with positive scalar. -/
theorem monsterNortonSingerY_basis_spin (a : Fin 11) :
    monsterNortonSingerSpin * monsterNortonYSpin (monsterNortonSingerYBasisSource a) =
      monsterNortonYSpin (monsterNortonSingerYBasisTarget a) * monsterNortonSingerSpin := by
  have hs : ∀ a, monsterNortonSingerYBasisSource a ≠ 0 := by decide +kernel
  have ht : ∀ a, monsterNortonSingerYBasisTarget a ≠ 0 := by decide +kernel
  have hb : (monsterNortonYSpin (monsterNortonSingerYBasisTarget a) *
      monsterNortonSingerSpin).val (Pi.single (0 : SpinIndex) 1) 0 = (1 / 2 : ℝ) := by
    change (monsterNortonYSpin (monsterNortonSingerYBasisTarget a)).val
      (monsterNortonSingerSpin.val (Pi.single (0 : SpinIndex) 1)) 0 = _
    rw [monsterNortonSingerSpin_delta_zero, monsterNortonYSpin_zero_coefficient _ (ht a)]
  apply monsterNortonSpin_eq_of_conjugation_eq_of_coefficient _ _
    (monsterNortonSingerY_basis_conjugation a) (Pi.single (0 : SpinIndex) 1) 0
  · change monsterNortonSingerSpin.val
      ((monsterNortonYSpin (monsterNortonSingerYBasisSource a)).val
        (Pi.single (0 : SpinIndex) 1)) 0 = _
    rw [monsterNortonSingerSpin_apply_zero, monsterNortonYSpin_zero_coefficient _ (hs a), hb]
  · rw [hb]
    norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
