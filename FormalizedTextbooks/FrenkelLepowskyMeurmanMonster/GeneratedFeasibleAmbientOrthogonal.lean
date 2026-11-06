/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedForm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOrbitStabilizers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisEnumerationLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ConwayAxisTranspositionCoordinates

/-! The feasible orbit of Höhn–Seysen, arXiv:2508.01037, §4, is the orbit of
the opposite signed axis under the full actual stabilizer of the first axis.
Every element of the actual generated group preserves the actual Griess form,
and the two opposite signed axes are orthogonal. Hence the whole feasible orbit
lies among the actual global-orbit vectors orthogonal to the first axis.
No orbit size, stabilizer generation, or source table value is used. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual weighted Griess form is symmetric. -/
theorem generatedFeasibleAmbient_form_symm (x y : GriessSpace) :
    griessForm x y = griessForm y x := by
  rw [griessForm_apply, griessForm_apply]
  unfold griessFormFun
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The pairing of an actual signed-short axis with any vector, in Conway coordinates. -/
theorem generatedFeasibleAmbient_axis_form (r : GriessShortIndex) (c : ZMod 2)
    (x : GriessSpace) :
    griessForm (conwayShortAxis r c) x =
      2 * axisMatrixContraction (griessShortVector r) (griessConwayEncode x).1 -
        8 * qSign c * (griessConwayEncode x).2.1 r := by
  rw [griessForm_eq_conwayRawForm, conwayShortAxis_encode, conwayShortAxisRaw_form]

/-- The matrix part of a signed-short axis contracts against its own vector to 32. -/
theorem generatedFeasibleAmbient_axis_self_contraction (r : GriessShortIndex) (c : ZMod 2) :
    axisMatrixContraction (griessShortVector r) (conwayShortAxisRaw r c).1 = 32 := by
  simp only [conwayShortAxisRaw, axisMatrixContraction, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  have he (i j : Fin 24) :
      griessShortVector r i * (2 * (griessShortVector r i * griessShortVector r j)) *
        griessShortVector r j =
      2 * (griessShortVector r i * griessShortVector r i) *
        (griessShortVector r j * griessShortVector r j) := by ring
  simp_rw [he, ← Finset.mul_sum, griessShortVector_norm_sq]
  rw [← Finset.sum_mul, ← Finset.mul_sum, griessShortVector_norm_sq]
  norm_num

/-- The two opposite signed axes over one short label are orthogonal. -/
theorem generatedFeasibleAmbient_opposite_form (r : GriessShortIndex) :
    griessForm (conwayShortAxis r 0) (conwayShortAxis r 1) = 0 := by
  rw [generatedFeasibleAmbient_axis_form, conwayShortAxis_encode,
    generatedFeasibleAmbient_axis_self_contraction]
  have hs : (conwayShortAxisRaw r 1).2.1 r = 8 := by
    simp [conwayShortAxisRaw]
  rw [hs, qSign_zero]
  norm_num

/-- The actual global-orbit vectors orthogonal to the given vector. -/
def generatedFeasibleAmbientOrthogonalAxes (a : GriessSpace) : Set GriessSpace :=
  {x | x ∈ generatedVectorOrbit a ∧ griessForm a x = 0}

/-- An orthogonal partner in the global orbit has its entire actual stabilizer orbit
orthogonal; only form invariance of the actual generated group is used. -/
theorem generatedFeasibleVectorOrbit_subset_orthogonalAxes (a b : GriessSpace)
    (hb : b ∈ generatedVectorOrbit a) (hab : griessForm a b = 0) :
    generatedFeasibleVectorOrbit a b ⊆ generatedFeasibleAmbientOrthogonalAxes a := by
  rintro x ⟨g, rfl⟩
  obtain ⟨k, hk⟩ := hb
  have hfix : g.val.val a = a := g.property
  refine ⟨⟨g.val * k, ?_⟩, ?_⟩
  · change g.val.val (k.val a) = g.val.val b
    rw [hk]
  · change griessForm a (g.val.val b) = 0
    calc griessForm a (g.val.val b) = griessForm (g.val.val a) (g.val.val b) := by
          rw [hfix]
      _ = griessForm a b := generated_group_preserves_griessForm g.val a b
      _ = 0 := hab

/-- The actual feasible orbit lies among the actual orthogonal partners of the first axis. -/
theorem generatedFeasibleVectorOrbit_subset_opposite_orthogonalAxes (r : GriessShortIndex) :
    generatedFeasibleVectorOrbit (conwayShortAxis r 0) (conwayShortAxis r 1) ⊆
      generatedFeasibleAmbientOrthogonalAxes (conwayShortAxis r 0) :=
  generatedFeasibleVectorOrbit_subset_orthogonalAxes _ _
    (generatedSignedShortAxes_subset_orbit r 0 ⟨(r, 1), rfl⟩)
    (generatedFeasibleAmbient_opposite_form r)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
