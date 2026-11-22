/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceIncomingBeads
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceBeadImageOperators

/-!
# Full original necklace epimorphisms from actual joint images

The SAME original vertex-surjective map with exact original joint images
is surjective on EVERY full native simplex. The proof lifts entire
original target beads through their actual incoming source beads and
keeps the genuine dimension-zero target.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

open CategoryTheory.CoherentRealization.OriginalBeadInterval

/-- The original dimension-zero necklace has exactly one whole simplex in every scalar arity. -/
theorem zero_simplex_unique (T : Data) (hn : T.dimension = 0) {d : ℕ}
    (s t : T.object.{u} _⦋d⦌) : s = t := by
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  have : Subsingleton (Fin (T.dimension + 1)) := hn.symm ▸ inferInstanceAs (Subsingleton (Fin 1))
  exact Subsingleton.elim _ _

/-- The original full necklace map lifts every original target simplex, including a zero-dimensional target. -/
theorem map_surjective_all_simplices {T U : Data} (f : T ⟶ U)
    (hf : Function.Surjective f.operator.toOrderHom)
    (hj : ∀ j, j ∈ U.joints ↔ ∃ i ∈ T.joints, f.operator.toOrderHom i = j)
    (d : ℕ) : Function.Surjective (f.map.{u}.app (op ⦋d⦌)) := by
  intro s
  by_cases hn : U.dimension = 0
  · let a : (Δ[0] : SSet.{u}) _⦋d⦌ := stdSimplex.objEquiv.symm (SimplexCategory.const ⦋d⦌ ⦋0⦌ 0)
    refine ⟨(vertexMap T.joints 0).app (op ⦋d⦌) a, zero_simplex_unique U hn _ s⟩
  · obtain ⟨a, b, hb, hs⟩ := simplex_in_bead U (Nat.pos_of_ne_zero hn) s.val s.property
    obtain ⟨c, e, hc, hfc, hfe⟩ := exists_incoming_bead f hj hb
    have hfp : f.operator.toOrderHom c < f.operator.toOrderHom e := by rw [hfc, hfe]; exact hb.positive
    have hjmap : ∀ i ∈ T.joints, f.operator.toOrderHom i ∈ U.joints :=
      fun i hi => (hj _).mpr ⟨i, hi, rfl⟩
    let hImage := bead_image f hc hjmap hfp
    have hs' : ∀ j, f.operator.toOrderHom c ≤ s.val j ∧ s.val j ≤ f.operator.toOrderHom e := by
      intro j
      rw [hfc, hfe]
      exact hs j
    obtain ⟨r, hr⟩ := exists_bead_simplex_preimage hImage s.val hs'
    let F := beadImageOperator f hc
    let := beadImageOperator_epi f hc hf
    let := isSplitEpi_of_epi F
    have hepi : Epi (SSet.stdSimplex.map F : (Δ[length c e] : SSet.{u}) ⟶ _) := by infer_instance
    obtain ⟨t, ht⟩ := (epi_iff_surjective ((SSet.stdSimplex.map F).app (op ⦋d⦌))).mp inferInstance r
    refine ⟨(beadMap hc).app (op ⦋d⦌) t, ?_⟩
    have hw := ConcreteCategory.congr_hom
      (congr_app (beadMap_image_square.{u} f hc hjmap hfp) (op ⦋d⦌)) t
    change (beadMap hImage).app (op ⦋d⦌) ((SSet.stdSimplex.map F).app (op ⦋d⦌) t) =
      f.map.app (op ⦋d⦌) ((beadMap hc).app (op ⦋d⦌) t) at hw
    rw [ht] at hw
    exact hw.symm.trans (Subtype.ext hr)

/-- The SAME original full necklace map is genuinely epi in simplicial sets. -/
theorem map_epi_of_joint_image {T U : Data} (f : T ⟶ U)
    (hf : Function.Surjective f.operator.toOrderHom)
    (hj : ∀ j, j ∈ U.joints ↔ ∃ i ∈ T.joints, f.operator.toOrderHom i = j) : Epi f.map.{u} := by
  rw [NatTrans.epi_iff_epi_app]
  rintro ⟨⟨d⟩⟩
  exact (epi_iff_surjective _).mpr (map_surjective_all_simplices f hf hj d)

end SSet.OriginalNecklace
