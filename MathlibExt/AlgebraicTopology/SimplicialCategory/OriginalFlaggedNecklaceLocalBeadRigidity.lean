/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceBeadCollapseRigidity

/-!
# Genuine original local bead rigidity

Two actual flanked maps over the SAME totally nondegenerate target input
agree on each entire original source bead once they agree at its initial
joint. The proof keeps the full native interval operators and uses the
uniqueness of genuine epi factorizations of the original input simplex.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace OriginalBeadInterval

/-- Actual positive beads with the SAME initial original joint have the SAME terminal joint. -/
theorem bead_end_unique {T : Data} {a b c : Fin (T.dimension + 1)}
    (h : IsBead T a b) (h' : IsBead T a c) : b = c := by
  have hbc := (h.consecutive c h'.target).resolve_left (not_le_of_gt h'.positive)
  have hcb := (h'.consecutive b h.target).resolve_left (not_le_of_gt h.positive)
  exact le_antisymm hbc hcb

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

private theorem native_epi_vertex_unique {n m₁ m₂ : ℕ} (s : K _⦋n⦌)
    (F : ⦋n⦌ ⟶ ⦋m₁⦌) [Epi F] (σ : K.nonDegenerate m₁) (hF : s = K.map F.op σ)
    (G : ⦋n⦌ ⟶ ⦋m₂⦌) [Epi G] (τ : K.nonDegenerate m₂) (hG : s = K.map G.op τ)
    (i : Fin (n + 1)) : (F.toOrderHom i).val = (G.toOrderHom i).val := by
  have hm := SSet.unique_nonDegenerate_dim K s F σ hF G τ hG
  subst m₂
  exact congrArg (fun f : ⦋n⦌ ⟶ ⦋m₁⦌ => (f.toOrderHom i).val)
    (SSet.unique_nonDegenerate_map K s F σ hF G τ hG)

/-- Both actual positive image beads have identical original interval endpoints from their SAME initial joint. -/
theorem positive_image_end_eq {T U : Object K x y q} (f g : T ⟶ U)
    (hT : IsFlanked T) (hU : IsFlanked U)
    {a b : Fin (T.necklace.dimension + 1)} (h : IsBead T.necklace a b)
    (hf : f.necklaceMap.operator.toOrderHom a < f.necklaceMap.operator.toOrderHom b)
    (hg : g.necklaceMap.operator.toOrderHom a < g.necklaceMap.operator.toOrderHom b)
    (ha : f.necklaceMap.operator.toOrderHom a = g.necklaceMap.operator.toOrderHom a) :
    f.necklaceMap.operator.toOrderHom b = g.necklaceMap.operator.toOrderHom b := by
  have hb := bead_image f.necklaceMap h (flanked_joint_maps f hT hU) hf
  have hc := bead_image g.necklaceMap h (flanked_joint_maps g hT hU) hg
  rw [← ha] at hc
  exact bead_end_unique hb hc

/-- The original whole positive source-bead maps agree from the SAME original initial joint. -/
theorem positive_bead_maps_eq {T U : Object K x y q} (f g : T ⟶ U)
    (hT : IsFlanked T) (hU : IsFlanked U) (hND : TotallyNondegenerate U)
    {a b : Fin (T.necklace.dimension + 1)} (h : IsBead T.necklace a b)
    (hf : f.necklaceMap.operator.toOrderHom a < f.necklaceMap.operator.toOrderHom b)
    (hg : g.necklaceMap.operator.toOrderHom a < g.necklaceMap.operator.toOrderHom b)
    (ha : f.necklaceMap.operator.toOrderHom a = g.necklaceMap.operator.toOrderHom a) :
    beadMap.{u} h ≫ f.necklaceMap.map = beadMap h ≫ g.necklaceMap.map := by
  have hb := positive_image_end_eq f g hT hU h hf hg ha
  let bf := bead_image f.necklaceMap h (flanked_joint_maps f hT hU) hf
  let bg := bead_image g.necklaceMap h (flanked_joint_maps g hT hU) hg
  let F := beadImageOperator f.necklaceMap h
  let G := beadImageOperator g.necklaceMap h
  let := beadInputSimplex_factor_epi f hU h
  let := beadInputSimplex_factor_epi g hU h
  have hfacf := (beadInputSimplex_factor f hT hU h hf).symm
  have hfacg := (beadInputSimplex_factor g hT hU h hg).symm
  have hfND := hND _ _ bf
  have hgND := hND _ _ bg
  have he : (operator a b h.positive.le ≫ f.necklaceMap.operator) =
      operator a b h.positive.le ≫ g.necklaceMap.operator := by
    ext i : 3
    apply Fin.ext
    have hFG := native_epi_vertex_unique (beadInputSimplex T h)
      F ⟨beadInputSimplex U bf, hfND⟩ hfacf G ⟨beadInputSimplex U bg, hgND⟩ hfacg i
    change (f.necklaceMap.operator.toOrderHom (embedding a b h.positive.le i)).val -
        (f.necklaceMap.operator.toOrderHom a).val =
      (g.necklaceMap.operator.toOrderHom (embedding a b h.positive.le i)).val -
        (g.necklaceMap.operator.toOrderHom a).val at hFG
    change (f.necklaceMap.operator.toOrderHom (embedding a b h.positive.le i)).val =
      (g.necklaceMap.operator.toOrderHom (embedding a b h.positive.le i)).val
    have hfBound := (bead_image_bounds f.necklaceMap h i).1
    have hgBound := (bead_image_bounds g.necklaceMap h i).1
    have haVal := congrArg Fin.val ha
    change (f.necklaceMap.operator.toOrderHom a).val ≤ _ at hfBound
    change (g.necklaceMap.operator.toOrderHom a).val ≤ _ at hgBound
    omega
  apply (cancel_mono (complex.{u} U.necklace.joints).ι).1
  rw [Category.assoc, Morphism.map_ι, ← Category.assoc, beadMap_ι,
    Category.assoc, Morphism.map_ι, ← Category.assoc, beadMap_ι,
    ← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
  exact congrArg (fun k => SSet.stdSimplex.map k) he

/-- Both original whole source-bead maps agree from their SAME initial joint, including genuine collapses. -/
theorem bead_maps_eq_of_initial_eq {T U : Object K x y q} (f g : T ⟶ U)
    (hT : IsFlanked T) (hU : IsFlanked U) (hND : TotallyNondegenerate U)
    {a b : Fin (T.necklace.dimension + 1)} (h : IsBead T.necklace a b)
    (ha : f.necklaceMap.operator.toOrderHom a = g.necklaceMap.operator.toOrderHom a) :
    beadMap.{u} h ≫ f.necklaceMap.map = beadMap h ≫ g.necklaceMap.map := by
  by_cases hf : f.necklaceMap.operator.toOrderHom a = f.necklaceMap.operator.toOrderHom b
  · have hg := (bead_collapse_iff f g hT hU hND h).mp hf
    apply (cancel_mono (complex.{u} U.necklace.joints).ι).1
    rw [Category.assoc, Morphism.map_ι, ← Category.assoc, beadMap_ι,
      Category.assoc, Morphism.map_ι, ← Category.assoc, beadMap_ι,
      ← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
    congr 1
    ext i : 3
    exact (bead_collapsed f.necklaceMap h hf i).trans
      (ha.trans (bead_collapsed g.necklaceMap h hg i).symm)
  · have hg := mt (bead_collapse_iff f g hT hU hND h).mpr hf
    exact positive_bead_maps_eq f g hT hU hND h
      (lt_of_le_of_ne (f.necklaceMap.operator.toOrderHom.monotone h.positive.le) hf)
      (lt_of_le_of_ne (g.necklaceMap.operator.toOrderHom.monotone h.positive.le) hg) ha

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
