/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22PointTransitivity

/-! Every actual auxiliary M22 local distant graph is connected through original hexad lines. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine Golay point transitivity transports the checked base local tree to every point. -/
theorem co1ResidueM22_local_connected (x : Co1ResidueM22Point 0 1)
    (s t : {s : Co1ResidueM22Point 0 1 // co1ResidueM22Distant 0 1 x s}) :
    Relation.ReflTransGen (fun s t => ∃ w,
      (co1ResidueM22Line 0 1 s.val t.val w ∨ co1ResidueM22Line 0 1 t.val s.val w) ∧
      ¬ co1ResidueM22Distant 0 1 x w) s t := by
  obtain ⟨g, h0, h1, hx⟩ := co1ResidueM22Point_transitive x
  let F : {s : Co1ResidueM22Point 0 1 //
      co1ResidueM22Distant 0 1 (co1ResidueM22FinitePoint 0) s} →
      {s : Co1ResidueM22Point 0 1 // co1ResidueM22Distant 0 1 x s} := fun u =>
    ⟨co1ResidueM22PointMap g h0 h1 u.val, by
      have h := (co1ResidueM22_distant_map_iff g h0 h1 _ _).mpr u.property
      rwa [hx] at h⟩
  have hF : Function.Surjective F := by
    intro u
    obtain ⟨v, hv⟩ := co1ResidueM22PointMap_surjective g h0 h1 u.val
    have hd : co1ResidueM22Distant 0 1 (co1ResidueM22FinitePoint 0) v :=
      (co1ResidueM22_distant_map_iff g h0 h1 _ _).mp (by rw [hx, hv]; exact u.property)
    exact ⟨⟨v, hd⟩, Subtype.ext hv⟩
  obtain ⟨u, rfl⟩ := hF s
  obtain ⟨v, rfl⟩ := hF t
  apply Relation.ReflTransGen.lift F _ _ _ (co1ResidueM22Finite_local_base_connected u v)
  intro a b hab
  obtain ⟨w, hline, hn⟩ := hab
  refine ⟨co1ResidueM22PointMap g h0 h1 w, ?_, ?_⟩
  · rcases hline with hline | hline
    · exact Or.inl (co1ResidueM22_line_map g h0 h1 _ _ _ hline)
    · exact Or.inr (co1ResidueM22_line_map g h0 h1 _ _ _ hline)
  · intro hd
    apply hn
    apply (co1ResidueM22_distant_map_iff g h0 h1 _ _).mp
    rwa [hx]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
