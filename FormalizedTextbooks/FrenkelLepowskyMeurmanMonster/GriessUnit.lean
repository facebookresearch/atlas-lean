/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortGeometry
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneralAxialVector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalProductInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GriessCommutativity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedForm
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
/-! The concrete identity element and its invariant orthogonal complement.

The dictionary diagonal with entries 1/4 is the identity for the actual
Griess product. Local generators and triality fix it, so the generated group
fixes the identity line and preserves its 196883 dimensional complement.
These conclusions use the concrete generator formulas, with no milestone
proofs or simplicity assumptions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

noncomputable def griessUnit : GriessSpace := trialityDiagonalVector (fun _ => 1 / 4)

lemma griessUnit_encode : griessConwayEncode griessUnit =
    (Matrix.diagonal (fun _ => (1 / 4 : ℝ)), (0, 0)) := griessConwayEncode_diagonal _

lemma griessUnit_raw_product (x : ConwayRawSpace) :
    conwayRawProduct (Matrix.diagonal (fun _ => (1 / 4 : ℝ)), (0, 0)) x = x := by
  rw [conwayRawProduct_diagonal]
  apply Prod.ext
  · ext i j
    norm_num
  · apply Prod.ext
    · funext r
      have h : conwayShortPairing (Matrix.diagonal (fun _ => (1 / 4 : ℝ))) r = 1 := by
        rw [conwayShortPairing_diagonal]
        simp only [← Finset.mul_sum, sq]
        rw [griessShortVector_norm_sq]
        norm_num
      simp only [h, one_mul]
    · funext t i
      norm_num

theorem griessUnit_mul (x : GriessSpace) : griessProd griessUnit x = x := by
  rw [griessProd_eq_conwayRawProduct, griessUnit_encode, griessUnit_raw_product,
    griessConwayDecode_encode]

theorem griessUnit_mul_right (x : GriessSpace) : griessProd x griessUnit = x := by
  rw [griessProd_comm, griessUnit_mul]

theorem griessUnit_form : griessForm griessUnit griessUnit = 3 / 2 := by
  rw [griessForm_eq_trialityBlockForm]
  simp only [griessUnit, trialityDiagonalVector, LinearEquiv.apply_symm_apply,
    trialityBlockForm]
  norm_num

theorem griessUnit_ne_zero : griessUnit ≠ 0 := by
  intro h
  have hf := griessUnit_form
  rw [h] at hf
  norm_num at hf

theorem griessUnit_fixed_of_product (e : GriessSpace ≃ₗ[ℝ] GriessSpace)
    (he : ∀ x y, e (griessProd x y) = griessProd (e x) (e y)) : e griessUnit = griessUnit := by
  have h := he griessUnit (e.symm griessUnit)
  rw [griessUnit_mul, LinearEquiv.apply_symm_apply, griessUnit_mul_right] at h
  exact h.symm

theorem rhoLocal_griessUnit (h : H) : rhoLocal h griessUnit = griessUnit :=
  griessUnit_fixed_of_product (rhoLocal h) (rhoLocal_product h)

theorem sExtra_griessUnit : sExtra griessUnit = griessUnit := sExtra_diagonal _

noncomputable def griessUnitStabilizer : Subgroup (GriessSpace ≃ₗ[ℝ] GriessSpace) where
  carrier := {e | e griessUnit = griessUnit}
  one_mem' := rfl
  mul_mem' := by
    intro e f he hf
    change e (f griessUnit) = griessUnit
    rw [hf, he]
  inv_mem' := by
    intro e he
    apply e.injective
    change e (e.symm griessUnit) = e griessUnit
    rw [LinearEquiv.apply_symm_apply, he]

theorem G_le_griessUnitStabilizer : G ≤ griessUnitStabilizer := by
  apply (Subgroup.closure_le _).mpr
  rintro e (⟨h, rfl⟩ | he)
  · exact rhoLocal_griessUnit h
  · obtain rfl := Set.mem_singleton_iff.mp he
    exact sExtra_griessUnit

theorem generated_group_griessUnit (g : G) : g.val griessUnit = griessUnit :=
  G_le_griessUnitStabilizer g.property

noncomputable def griessUnitOrthogonal : Submodule ℝ GriessSpace :=
  (griessForm griessUnit).ker

theorem generated_group_unit_pairing (g : G) (x : GriessSpace) :
    griessForm griessUnit (g.val x) = griessForm griessUnit x := by
  have h := generated_group_preserves_griessForm g griessUnit x
  rwa [generated_group_griessUnit] at h

theorem generated_group_preserves_griessUnitOrthogonal (g : G) (x : GriessSpace) :
    g.val x ∈ griessUnitOrthogonal ↔ x ∈ griessUnitOrthogonal := by
  change griessForm griessUnit (g.val x) = 0 ↔ griessForm griessUnit x = 0
  rw [generated_group_unit_pairing]

theorem griessUnitFunctional_surjective : Function.Surjective (griessForm griessUnit) := by
  intro y
  refine ⟨(2 * y / 3 : ℝ) • griessUnit, ?_⟩
  rw [map_smul, griessUnit_form]
  change (2 * y / 3) * (3 / 2) = y
  ring

theorem griessUnitOrthogonal_finrank : Module.finrank ℝ griessUnitOrthogonal = 196883 := by
  have h := (griessForm griessUnit).finrank_range_add_finrank_ker
  rw [(LinearMap.range_eq_top.mpr griessUnitFunctional_surjective),
    finrank_top, Module.finrank_self] at h
  have hd : Module.finrank ℝ GriessSpace = 196884 := by
    simp [GriessSpace]
  change 1 + Module.finrank ℝ griessUnitOrthogonal = Module.finrank ℝ GriessSpace at h
  rw [hd] at h
  omega
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
