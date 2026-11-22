/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNondegenerateSimplexDescent
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceMapUniqueness

/-!
# Same original source-bead fibre descent

For two actual original flanked maps from the SAME source, the map into
an original totally nondegenerate target is constant on every actual
vertex fibre of the other map within a whole source bead. All original
input simplices and both full interval epi maps are retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace OriginalBeadInterval

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The SAME map to a nondegenerate target is constant on a whole source-bead fibre of the other original map. -/
theorem paired_bead_vertex_fibre_constant {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T)
    {a b : Fin (A.necklace.dimension + 1)} (h : IsBead A.necklace a b)
    (i j : Fin (length a b + 1))
    (hij : g.necklaceMap.operator.toOrderHom (embedding a b h.positive.le i) =
      g.necklaceMap.operator.toOrderHom (embedding a b h.positive.le j)) :
    f.necklaceMap.operator.toOrderHom (embedding a b h.positive.le i) =
      f.necklaceMap.operator.toOrderHom (embedding a b h.positive.le j) := by
  by_cases hf : f.necklaceMap.operator.toOrderHom a = f.necklaceMap.operator.toOrderHom b
  · exact (bead_collapsed f.necklaceMap h hf i).trans (bead_collapsed f.necklaceMap h hf j).symm
  have hfp : f.necklaceMap.operator.toOrderHom a < f.necklaceMap.operator.toOrderHom b :=
    lt_of_le_of_ne (f.necklaceMap.operator.toOrderHom.monotone h.positive.le) hf
  by_cases hg : g.necklaceMap.operator.toOrderHom a = g.necklaceMap.operator.toOrderHom b
  · have hc := bead_collapsed_of_constant_input f hA hT hND h
      (inputVertex V (g.necklaceMap.operator.toOrderHom a)) (beadInputSimplex_collapsed g h hg)
    exact False.elim (hf hc)
  have hgp : g.necklaceMap.operator.toOrderHom a < g.necklaceMap.operator.toOrderHom b :=
    lt_of_le_of_ne (g.necklaceMap.operator.toOrderHom.monotone h.positive.le) hg
  let bf := bead_image f.necklaceMap h (flanked_joint_maps f hA hT) hfp
  let bg := bead_image g.necklaceMap h (flanked_joint_maps g hA hV) hgp
  let := beadInputSimplex_factor_epi f hT h
  let := beadInputSimplex_factor_epi g hV h
  have hG : (beadImageOperator g.necklaceMap h).toOrderHom i =
      (beadImageOperator g.necklaceMap h).toOrderHom j := by
    apply Fin.ext
    exact congrArg (fun z => z.val - (g.necklaceMap.operator.toOrderHom a).val) hij
  have hF := SSet.OriginalSimplexDescent.vertex_fibre_constant (beadInputSimplex A h)
    (beadImageOperator f.necklaceMap h) (beadImageOperator g.necklaceMap h)
    ⟨beadInputSimplex T bf, hND _ _ bf⟩ (beadInputSimplex V bg)
    (beadInputSimplex_factor f hA hT h hfp).symm
    (beadInputSimplex_factor g hA hV h hgp).symm i j hG
  apply Fin.ext
  have hv := congrArg Fin.val hF
  change (f.necklaceMap.operator.toOrderHom (embedding a b h.positive.le i)).val -
      (f.necklaceMap.operator.toOrderHom a).val =
    (f.necklaceMap.operator.toOrderHom (embedding a b h.positive.le j)).val -
      (f.necklaceMap.operator.toOrderHom a).val at hv
  have hi := (bead_image_bounds f.necklaceMap h i).1
  have hj := (bead_image_bounds f.necklaceMap h j).1
  change (f.necklaceMap.operator.toOrderHom a).val ≤ _ at hi
  change (f.necklaceMap.operator.toOrderHom a).val ≤ _ at hj
  omega

/-- Both entire original source vertices have the SAME fibre constancy within one actual bead interval. -/
theorem paired_bead_fibre_constant {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T)
    {a b : Fin (A.necklace.dimension + 1)} (h : IsBead A.necklace a b)
    (i j : Fin (A.necklace.dimension + 1)) (hi : a ≤ i ∧ i ≤ b) (hj : a ≤ j ∧ j ≤ b)
    (hij : g.necklaceMap.operator.toOrderHom i = g.necklaceMap.operator.toOrderHom j) :
    f.necklaceMap.operator.toOrderHom i = f.necklaceMap.operator.toOrderHom j := by
  obtain ⟨i', hi'⟩ := coverage a b h.positive.le (ULift.up.{u} i)
    (by rw [lifted_zero]; exact hi.1) (by rw [lifted_last]; exact hi.2)
  obtain ⟨j', hj'⟩ := coverage a b h.positive.le (ULift.up.{u} j)
    (by rw [lifted_zero]; exact hj.1) (by rw [lifted_last]; exact hj.2)
  have hei : embedding a b h.positive.le i'.down = i := congrArg ULift.down hi'
  have hej : embedding a b h.positive.le j'.down = j := congrArg ULift.down hj'
  have h := paired_bead_vertex_fibre_constant f g hA hT hV hND h i'.down j'.down
    ((congrArg g.necklaceMap.operator.toOrderHom hei).trans
      (hij.trans (congrArg g.necklaceMap.operator.toOrderHom hej).symm))
  simpa only [hei, hej] using h

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
