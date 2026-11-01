/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual norm-eight action and its coordinate-frame stabilizer. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCountTypes
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechConcreteGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Finiteness
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual lattice action restricts to the norm-eight vectors. -/
noncomputable instance : MulAction leechIsomSubgroup LeechNormEight where
  smul e u := ⟨leechIntegralAction e u.val, by
    rw [leechIntegralAction_squareSum, u.property]⟩
  one_smul u := by
    apply Subtype.ext
    change leechIntegralAction 1 u.val = u.val
    rw [map_one]
    rfl
  mul_smul e f u := by
    apply Subtype.ext
    exact congrArg (fun a => a u.val) (leechIntegralAction.map_mul e f)

/-- The distinguished positive coordinate-frame vector in the norm-eight set. -/
def leechNormEightAxis : LeechNormEight :=
  ⟨leechCoordinateFrameLattice 0, leechCoordinateFrameVector_square 0⟩

/-- The actual norm-eight action is transitive, by the concrete reduction theorem. -/
theorem leechNormEight_orbit_eq_univ :
    MulAction.orbit leechIsomSubgroup leechNormEightAxis = Set.univ := by
  apply Set.eq_univ_of_forall
  intro u
  obtain ⟨e, _, he⟩ := leechNormEight_concrete_transitive u.val u.property
  have hh : e • u = leechNormEightAxis := by
    apply Subtype.ext
    apply Subtype.ext
    exact he
  refine ⟨e⁻¹, ?_⟩
  change e⁻¹ • leechNormEightAxis = u
  rw [← hh, inv_smul_smul]

/-- The full stabilizer of the positive frame vector is contained in the
actual monomial subgroup. -/
theorem leechNormEight_stabilizer_le_monomial :
    MulAction.stabilizer leechIsomSubgroup leechNormEightAxis ≤ golayMonomialSubgroup := by
  intro e he
  apply leech_fix_frame_mem_monomial e
  exact congrArg Subtype.val he

/-- Actual orbit-stabilizer counting expressed with the finite norm-eight vector set. -/
theorem leechNormEight_card_mul_stabilizer :
    Nat.card LeechNormEight *
      Nat.card (MulAction.stabilizer leechIsomSubgroup leechNormEightAxis) =
      Nat.card leechIsomSubgroup := by
  have : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let _ := Fintype.ofFinite LeechNormEight
  let _ := Fintype.ofFinite leechIsomSubgroup
  let _ := Fintype.ofFinite (MulAction.orbit leechIsomSubgroup leechNormEightAxis)
  let _ := Fintype.ofFinite (MulAction.stabilizer leechIsomSubgroup leechNormEightAxis)
  have horbit : Nat.card (MulAction.orbit leechIsomSubgroup leechNormEightAxis) =
      Nat.card LeechNormEight := by
    rw [leechNormEight_orbit_eq_univ]
    exact Nat.card_congr (Equiv.Set.univ LeechNormEight)
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    leechIsomSubgroup leechNormEightAxis
  simpa only [← Nat.card_eq_fintype_card, horbit] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
