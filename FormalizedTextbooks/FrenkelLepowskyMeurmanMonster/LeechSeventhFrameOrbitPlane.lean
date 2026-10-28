/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhFrameOrbitWords

/-! Original signed word root images fix the genuine real triangle plane. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A full actual section element with the same three root lines fixes their real plane. -/
theorem leechSeventhFrame_plane_fixed_of_root_images (g : leechSeventhE8SectionGroup)
    (p : Fin 1120)
    (h : Finset.univ.image (fun j : Fin 3 =>
      leechSeventhE8SectionRootIndex g (leechSeventhE8A2Indices p j)) =
        Finset.univ.image (leechSeventhE8A2Indices p)) :
    (leechSeventhE8A2Plane p).map g.val.val.toLinearMap = leechSeventhE8A2Plane p := by
  apply le_antisymm
  · rw [leechSeventhE8A2Plane, Submodule.map_span, Submodule.span_le]
    rintro x ⟨y, ⟨j, rfl⟩, rfl⟩
    change g.val.val (leechSeventhE8RealRoot (leechSeventhE8A2Indices p j)) ∈
      leechSeventhE8A2Plane p
    have hi : leechSeventhE8SectionRootIndex g (leechSeventhE8A2Indices p j) ∈
        Finset.univ.image (leechSeventhE8A2Indices p) := by
      rw [← h]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hi
    have hm : leechSeventhE8RealRoot
        (leechSeventhE8SectionRootIndex g (leechSeventhE8A2Indices p j)) ∈
        leechSeventhE8A2Plane p := by
      rw [← hk]
      exact leechSeventhE8A2Plane_root_mem p k
    rcases leechSeventhE8SectionRoot_real_sign g (leechSeventhE8A2Indices p j) with hs | hs
    · rw [hs]
      exact hm
    · rw [hs]
      exact Submodule.neg_mem _ hm
  · rw [leechSeventhE8A2Plane, Submodule.span_le]
    rintro x ⟨k, rfl⟩
    have hi : leechSeventhE8A2Indices p k ∈
        Finset.univ.image (fun j : Fin 3 =>
          leechSeventhE8SectionRootIndex g (leechSeventhE8A2Indices p j)) := by
      rw [h]
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    have hm := Submodule.mem_map_of_mem (f := g.val.val.toLinearMap)
      (leechSeventhE8A2Plane_root_mem p j)
    change g.val.val (leechSeventhE8RealRoot (leechSeventhE8A2Indices p j)) ∈
      (leechSeventhE8A2Plane p).map g.val.val.toLinearMap at hm
    change leechSeventhE8RealRoot (leechSeventhE8A2Indices p k) ∈ _
    rcases leechSeventhE8SectionRoot_real_sign g (leechSeventhE8A2Indices p j) with hs | hs
    · rw [hs, hj] at hm
      exact hm
    · rw [hs, hj] at hm
      exact (Submodule.neg_mem_iff _).mp hm

/-- All 27 original signed words fix the actual triangle plane with their root signs retained. -/
theorem leechSeventhFrameOrbitWord_plane_fixed (k : Fin 27) :
    (leechSeventhE8A2Plane 537).map
      (leechSeventhFrameWord (leechSeventhFrameOrbitWord k)).val.toLinearMap =
        leechSeventhE8A2Plane 537 := by
  apply leechSeventhFrame_plane_fixed_of_root_images
    ⟨_, leechSeventhFrameWord_mem _⟩ 537
  simpa only [leechSeventhFrameWord_section_root_index] using
    leechSeventhFrameOrbitWord_triangle k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
