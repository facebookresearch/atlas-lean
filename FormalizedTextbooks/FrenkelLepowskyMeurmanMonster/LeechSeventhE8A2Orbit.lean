/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2PlaneCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2PlaneOrbitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2SectionAction

/-! Original section-generator parent edges give genuine transitivity on all A2 planes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A finite original-generator three-line image is exactly its actual real plane image. -/
theorem leechSeventhE8A2Plane_generator_image (g : Fin 18) (p q : Fin 1120)
    (h : (Finset.univ.image (fun j : Fin 3 =>
      leechSeventhE8RootImage g (leechSeventhE8A2Indices p j))) =
        Finset.univ.image (leechSeventhE8A2Indices q)) :
    (leechSeventhE8A2Plane p).map (generatedFifthSectionGenerator g).val.toLinearMap =
      leechSeventhE8A2Plane q := by
  apply le_antisymm
  · rw [leechSeventhE8A2Plane, Submodule.map_span, Submodule.span_le]
    rintro x ⟨y, ⟨j, rfl⟩, rfl⟩
    change (generatedFifthSectionGenerator g).val
      (leechSeventhE8RealRoot (leechSeventhE8A2Indices p j)) ∈ leechSeventhE8A2Plane q
    rw [leechSeventhE8RealRoot_action]
    have hi : leechSeventhE8RootImage g (leechSeventhE8A2Indices p j) ∈
        Finset.univ.image (leechSeventhE8A2Indices q) := by
      rw [← h]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hi
    apply Submodule.smul_mem
    rw [← hk]
    exact leechSeventhE8A2Plane_root_mem q k
  · rw [leechSeventhE8A2Plane, Submodule.span_le]
    rintro x ⟨k, rfl⟩
    have hi : leechSeventhE8A2Indices q k ∈
        Finset.univ.image (fun j : Fin 3 =>
          leechSeventhE8RootImage g (leechSeventhE8A2Indices p j)) := by
      rw [h]
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    have hm : (generatedFifthSectionGenerator g).val (leechSeventhE8A2PlaneRoots p j) ∈
        (leechSeventhE8A2Plane p).map (generatedFifthSectionGenerator g).val.toLinearMap :=
      Submodule.mem_map_of_mem (leechSeventhE8A2Plane_root_mem p j)
    change (generatedFifthSectionGenerator g).val
      (leechSeventhE8RealRoot (leechSeventhE8A2Indices p j)) ∈ _ at hm
    change leechSeventhE8RealRoot (leechSeventhE8A2Indices q k) ∈
      (leechSeventhE8A2Plane p).map (generatedFifthSectionGenerator g).val.toLinearMap
    rw [leechSeventhE8RealRoot_action, hj] at hm
    rcases leechSeventhE8Root_sign_certificate g (leechSeventhE8A2Indices p j) with hs | hs
    · rw [hs] at hm
      simpa only [Int.cast_one, one_smul, leechSeventhE8A2PlaneRoots] using hm
    · rw [hs] at hm
      simpa only [Int.cast_neg, Int.cast_one, neg_one_smul, Submodule.neg_mem_iff,
        leechSeventhE8A2PlaneRoots] using hm

/-- Every finite original parent-tree target is reached by a genuine full-section element. -/
theorem leechSeventhE8A2Orbit_reachable (p : Fin 1120) :
    ∃ e : leechSeventhE8SectionGroup,
      (leechSeventhE8A2Plane (leechSeventhE8A2OrbitIndex 0)).map e.val.val.toLinearMap =
        leechSeventhE8A2Plane (leechSeventhE8A2OrbitIndex p) := by
  refine WellFoundedLT.induction (motive := fun p : Fin 1120 =>
    ∃ e : leechSeventhE8SectionGroup,
      (leechSeventhE8A2Plane (leechSeventhE8A2OrbitIndex 0)).map e.val.val.toLinearMap =
        leechSeventhE8A2Plane (leechSeventhE8A2OrbitIndex p)) p ?_
  intro p ih
  by_cases hp : p = 0
  · subst p
    exact ⟨1, Submodule.map_id _⟩
  · obtain ⟨e, he⟩ := ih (leechSeventhE8A2OrbitParent p)
      (leechSeventhE8A2_orbit_parent_lt p hp)
    let g : leechSeventhE8SectionGroup :=
      generatedAxisE8FrameSystemOrbitLetter (leechSeventhE8A2OrbitLetter p)
    refine ⟨g * e, ?_⟩
    change (leechSeventhE8A2Plane (leechSeventhE8A2OrbitIndex 0)).map
      (g.val.val.toLinearMap.comp e.val.val.toLinearMap) = _
    rw [Submodule.map_comp, he]
    exact leechSeventhE8A2Plane_generator_image _ _ _ (leechSeventhE8A2_orbit_edge p hp)
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
