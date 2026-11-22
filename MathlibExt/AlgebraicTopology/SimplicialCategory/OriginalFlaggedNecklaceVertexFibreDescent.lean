/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceBeadFibreDescent
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceSurjectiveFullMaps

/-!
# Whole original vertex-fibre descent

For two actual original flanked maps from the SAME source, the map to a
genuinely totally nondegenerate target is constant on EVERY original
vertex fibre of the other map. Its exact original full simplicial map
is epi in every scalar arity.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace OriginalBeadInterval

private theorem fibre_constant_of_consecutive {n m l : ℕ}
    (F : ⦋n⦌ ⟶ ⦋m⦌) (G : ⦋n⦌ ⟶ ⦋l⦌)
    (h : ∀ k : Fin n, G.toOrderHom k.castSucc = G.toOrderHom k.succ →
      F.toOrderHom k.castSucc = F.toOrderHom k.succ)
    (i j : Fin (n + 1)) (hij : G.toOrderHom i = G.toOrderHom j) :
    F.toOrderHom i = F.toOrderHom j := by
  have H : ∀ j : Fin (n + 1), ∀ i ≤ j,
      G.toOrderHom i = G.toOrderHom j → F.toOrderHom i = F.toOrderHom j := by
    intro j
    induction j using Fin.strong_induction_on with
    | h j ih =>
      intro i hij hG
      by_cases he : i = j
      · exact congrArg F.toOrderHom he
      · have hij' : i < j := lt_of_le_of_ne hij he
        have hj0 : j ≠ 0 := by intro hj; subst j; exact (not_lt_of_ge (Fin.zero_le i)) hij'
        let k := j.pred hj0
        have hik : i ≤ k.castSucc := (Fin.le_castSucc_pred_iff hj0).mpr hij'
        have hkG : G.toOrderHom k.castSucc = G.toOrderHom j :=
          le_antisymm (G.toOrderHom.monotone (Fin.castSucc_pred_lt hj0).le)
            (hG.symm.le.trans (G.toOrderHom.monotone hik))
        have hk := h k (hkG.trans (congrArg G.toOrderHom (Fin.succ_pred j hj0)).symm)
        have hki := ih k.castSucc (Fin.castSucc_pred_lt hj0) i hik (hG.trans hkG.symm)
        exact hki.trans (hk.trans (congrArg F.toOrderHom (Fin.succ_pred j hj0)))
  rcases le_total i j with he | he
  · exact H j i he hij
  · exact (H i j he hij.symm).symm

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The original map to a totally nondegenerate target is constant on EVERY actual original vertex fibre. -/
theorem paired_vertex_fibre_constant {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T)
    (i j : Fin (A.necklace.dimension + 1))
    (hij : g.necklaceMap.operator.toOrderHom i = g.necklaceMap.operator.toOrderHom j) :
    f.necklaceMap.operator.toOrderHom i = f.necklaceMap.operator.toOrderHom j := by
  apply fibre_constant_of_consecutive f.necklaceMap.operator g.necklaceMap.operator ?_ i j hij
  intro k hk
  obtain ⟨a, b, h, ha, hb⟩ := exists_bead_at_edge A.necklace k
  exact paired_bead_fibre_constant f g hA hT hV hND h k.castSucc k.succ
    ⟨ha, k.castSucc_le_succ.trans hb⟩ ⟨ha.trans k.castSucc_le_succ, hb⟩ hk

/-- The SAME full original flagged-necklace map is genuinely epi, retaining all native marked-free simplices. -/
theorem flanked_full_map_epi {A V : Object K x y q} (g : A ⟶ V)
    (hA : IsFlanked A) (hV : IsFlanked V) : Epi g.necklaceMap.map.{u} :=
  map_epi_of_joint_image g.necklaceMap (flanked_operator_surjective g hV)
    (flanked_joint_image g hA hV)

/-- Every SAME original target simplex lifts through the entire actual original flanked map. -/
theorem flanked_full_map_surjective {A V : Object K x y q} (g : A ⟶ V)
    (hA : IsFlanked A) (hV : IsFlanked V) (d : ℕ) :
    Function.Surjective (g.necklaceMap.map.{u}.app (op ⦋d⦌)) :=
  map_surjective_all_simplices g.necklaceMap (flanked_operator_surjective g hV)
    (flanked_joint_image g hA hV) d

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
