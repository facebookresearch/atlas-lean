/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceLocalBeadRigidity

/-!
# Genuine uniqueness of original flanked maps

Every actual original flanked map to a totally nondegenerate original
input is unique. The proof proceeds through all original vertices and
full bead intervals, retaining the SAME original maps and flags. This
is the uniqueness direction of the original canonical-component proof.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace OriginalBeadInterval

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- Equality on a whole original bead detects every actual original vertex of that bead. -/
theorem bead_vertex_eq_of_maps {T U : Object K x y q} (f g : T ⟶ U)
    {a b : Fin (T.necklace.dimension + 1)} (h : IsBead T.necklace a b)
    (hm : beadMap.{u} h ≫ f.necklaceMap.map = beadMap h ≫ g.necklaceMap.map)
    (j : Fin (T.necklace.dimension + 1)) (hj : a ≤ j ∧ j ≤ b) :
    f.necklaceMap.operator.toOrderHom j = g.necklaceMap.operator.toOrderHom j := by
  have hr : ULift.up.{u} j ∈ Set.range (liftedEmbedding a b h.positive.le) :=
    coverage a b h.positive.le (ULift.up.{u} j)
      (by rw [lifted_zero]; exact hj.1) (by rw [lifted_last]; exact hj.2)
  obtain ⟨i, hi⟩ := hr
  have he := ConcreteCategory.congr_hom (congr_app hm (op ⦋length a b⦌))
    (SSet.yonedaEquiv (𝟙 (Δ[length a b] : SSet.{u})))
  have hv := congrArg (fun s : U.necklace.object.{u} _⦋length a b⦌ => s.val i.down) he
  change f.necklaceMap.operator.toOrderHom (embedding a b h.positive.le i.down) =
    g.necklaceMap.operator.toOrderHom (embedding a b h.positive.le i.down) at hv
  have hji : embedding a b h.positive.le i.down = j := congrArg ULift.down hi
  exact hji ▸ hv

/-- Both SAME original flanked morphisms agree at every original ordinal vertex. -/
theorem totallyNondegenerate_vertex_unique {T U : Object K x y q} (f g : T ⟶ U)
    (hT : IsFlanked T) (hU : IsFlanked U) (hND : TotallyNondegenerate U)
    (j : Fin (T.necklace.dimension + 1)) :
    f.necklaceMap.operator.toOrderHom j = g.necklaceMap.operator.toOrderHom j := by
  induction j using Fin.strong_induction_on with
  | h j ih =>
    by_cases hj : j = 0
    · subst j
      exact f.necklaceMap.source.trans g.necklaceMap.source.symm
    · let i := j.pred hj
      obtain ⟨a, b, hab, ha, hb⟩ := exists_bead_at_edge T.necklace i
      have hja : a < j := ha.trans_lt (by rw [← Fin.succ_pred j hj]; exact i.castSucc_lt_succ)
      have hm := bead_maps_eq_of_initial_eq f g hT hU hND hab (ih a hja)
      apply bead_vertex_eq_of_maps f g hab hm j
      exact ⟨hja.le, (Fin.succ_pred j hj).symm.le.trans hb⟩

/-- The SAME full original flanked map over a totally nondegenerate target input is unique. -/
theorem totallyNondegenerate_map_unique {T U : Object K x y q} (f g : T ⟶ U)
    (hT : IsFlanked T) (hU : IsFlanked U) (hND : TotallyNondegenerate U) : f = g := by
  apply Hom.ext
  apply SSet.OriginalNecklace.Morphism.ext
  ext j : 3
  exact totallyNondegenerate_vertex_unique f g hT hU hND j

/-- The actual original Hom type into a flanked totally nondegenerate original input is subsingleton. -/
theorem totallyNondegenerate_hom_subsingleton (T U : Object K x y q)
    (hT : IsFlanked T) (hU : IsFlanked U) (hND : TotallyNondegenerate U) : Subsingleton (T ⟶ U) :=
  ⟨fun f g => totallyNondegenerate_map_unique f g hT hU hND⟩

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
