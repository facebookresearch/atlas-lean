/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2PlaneCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2PlaneGram
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2RealRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2Linear

/-! The finite A2 candidates are actual root spans in the physical E8 section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The three genuine physical short roots associated with a finite A2 candidate. -/
def leechSeventhE8A2PlaneRoots (p : Fin 1120) (j : Fin 3) : Fin 24 → ℝ :=
  leechSeventhE8RealRoot (leechSeventhE8A2Indices p j)

/-- The actual real span of the three verified roots of a finite A2 candidate. -/
def leechSeventhE8A2Plane (p : Fin 1120) : Submodule ℝ (Fin 24 → ℝ) :=
  Submodule.span ℝ (Set.range (leechSeventhE8A2PlaneRoots p))

/-- Every named original root belongs to its actual candidate plane. -/
theorem leechSeventhE8A2Plane_root_mem (p : Fin 1120) (j : Fin 3) :
    leechSeventhE8A2PlaneRoots p j ∈ leechSeventhE8A2Plane p :=
  Submodule.subset_span ⟨j, rfl⟩

/-- The checked integral Gram operator gives eigenvalue six on every physical generating root. -/
theorem leechSeventhE8A2Plane_gram (p : Fin 1120) (k : Fin 3) :
    leechSeventhRootOuterSum (leechSeventhE8A2PlaneRoots p)
      (leechSeventhE8A2PlaneRoots p k) = (6 : ℝ) • leechSeventhE8A2PlaneRoots p k := by
  let d : Fin 3 → ℤ := fun j => ∑ i : Fin 8,
    leechSeventhE8RootLocal (leechSeventhE8A2Indices p j) i *
      leechSeventhE8RootLocal (leechSeventhE8A2Indices p k) i
  have hz : (∑ j : Fin 3, d j • leechSeventhE8RootLocal (leechSeventhE8A2Indices p j)) =
      (48 : ℤ) • leechSeventhE8RootLocal (leechSeventhE8A2Indices p k) := by
    ext i
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      leechSeventhE8A2_root_gram p k i
  let E : (Fin 8 → ℤ) →ₗ[ℤ] (Fin 24 → ℝ) :=
    leechCoordinateEmbedding.comp generatedFifthFrameInsert
  have hm := congrArg E hz
  simp only [map_sum, map_smul] at hm
  have he (j : Fin 3) : E (leechSeventhE8RootLocal (leechSeventhE8A2Indices p j)) =
      leechSeventhE8A2PlaneRoots p j := by
    simp only [E, LinearMap.comp_apply, leechSeventhE8A2PlaneRoots,
      leechSeventhE8RealRoot, leechSeventhE8Root_physical]
  simp only [he] at hm
  have hm' : (∑ j : Fin 3, (d j : ℝ) • leechSeventhE8A2PlaneRoots p j) =
      (48 : ℝ) • leechSeventhE8A2PlaneRoots p k := by
    simp only [← Int.cast_smul_eq_zsmul ℝ] at hm
    simpa only [Int.cast_ofNat] using hm
  calc
    _ = ∑ j : Fin 3, ((d j : ℝ) / 8) • leechSeventhE8A2PlaneRoots p j := by
      rw [leechSeventhRootOuterSum_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [show leechSeventhE8A2PlaneRoots p j ⬝ᵥ leechSeventhE8A2PlaneRoots p k =
        (d j : ℝ) / 8 from leechSeventhE8RealRoot_pairing _ _]
    _ = (1 / 8 : ℝ) • ∑ j : Fin 3, (d j : ℝ) • leechSeventhE8A2PlaneRoots p j := by
      simp only [Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring
    _ = _ := by rw [hm', smul_smul]; norm_num

/-- Membership in each actual finite plane is recognized by its genuine outer sum. -/
theorem leechSeventhE8A2Plane_mem_iff (p : Fin 1120) (x : Fin 24 → ℝ) :
    x ∈ leechSeventhE8A2Plane p ↔
      leechSeventhRootOuterSum (leechSeventhE8A2PlaneRoots p) x = (6 : ℝ) • x :=
  leechSeventhRootOuterSum_span_iff _ 6 (by norm_num) (leechSeventhE8A2Plane_gram p) x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
