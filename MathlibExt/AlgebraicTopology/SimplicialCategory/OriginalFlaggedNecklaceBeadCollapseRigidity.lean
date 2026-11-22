/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceBeadInputs

/-!
# Original bead-collapse rigidity over a totally nondegenerate input

Two actual original flanked maps over the SAME input must collapse the
same source beads when their target's full original bead inputs are
nondegenerate. The proof compares genuine native epi factorizations of
the same input simplex, including the actual dimension-zero simplex.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace OriginalBeadInterval

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- A constant whole source-bead input cannot surject onto a positive nondegenerate target input. -/
theorem bead_collapsed_of_constant_input {T U : Object K x y q} (f : T ⟶ U)
    (hT : IsFlanked T) (hU : IsFlanked U) (hND : TotallyNondegenerate U)
    {a b : Fin (T.necklace.dimension + 1)} (h : IsBead T.necklace a b)
    (z : K _⦋0⦌)
    (hz : beadInputSimplex T h = K.map (SimplexCategory.const ⦋length a b⦌ ⦋0⦌ 0).op z) :
    f.necklaceMap.operator.toOrderHom a = f.necklaceMap.operator.toOrderHom b := by
  by_contra hf
  have hlt : f.necklaceMap.operator.toOrderHom a < f.necklaceMap.operator.toOrderHom b :=
    lt_of_le_of_ne (f.necklaceMap.operator.toOrderHom.monotone h.positive.le) hf
  let hb := bead_image f.necklaceMap h (flanked_joint_maps f hT hU) hlt
  let := beadInputSimplex_factor_epi f hU h
  let c := SimplexCategory.const ⦋length a b⦌ ⦋0⦌ 0
  let : Epi c := (SimplexCategory.epi_iff_surjective (f := c)).mpr (fun i =>
    ⟨0, @Subsingleton.elim (Fin 1) inferInstance _ i⟩)
  have hdim := SSet.unique_nonDegenerate_dim K (beadInputSimplex T h)
    (beadImageOperator f.necklaceMap h) ⟨beadInputSimplex U hb, hND _ _ hb⟩
      (beadInputSimplex_factor f hT hU h hlt).symm
    c ⟨z, K.nonDegenerate_zero.symm ▸ Set.mem_univ z⟩ hz
  change (f.necklaceMap.operator.toOrderHom b).val - (f.necklaceMap.operator.toOrderHom a).val = 0 at hdim
  change (f.necklaceMap.operator.toOrderHom a).val < (f.necklaceMap.operator.toOrderHom b).val at hlt
  omega

/-- Both SAME original flanked maps collapse precisely the same source bead over a nondegenerate target. -/
theorem bead_collapse_iff {T U : Object K x y q} (f g : T ⟶ U)
    (hT : IsFlanked T) (hU : IsFlanked U) (hND : TotallyNondegenerate U)
    {a b : Fin (T.necklace.dimension + 1)} (h : IsBead T.necklace a b) :
    f.necklaceMap.operator.toOrderHom a = f.necklaceMap.operator.toOrderHom b ↔
      g.necklaceMap.operator.toOrderHom a = g.necklaceMap.operator.toOrderHom b := by
  constructor
  · intro hf
    exact bead_collapsed_of_constant_input g hT hU hND h
      (inputVertex U (f.necklaceMap.operator.toOrderHom a)) (beadInputSimplex_collapsed f h hf)
  · intro hg
    exact bead_collapsed_of_constant_input f hT hU hND h
      (inputVertex U (g.necklaceMap.operator.toOrderHom a)) (beadInputSimplex_collapsed g h hg)

/-- A positive original source bead cannot collapse under a map from a totally nondegenerate original input. -/
theorem totallyNondegenerate_bead_not_collapsed {T U : Object K x y q} (f : T ⟶ U)
    (hND : TotallyNondegenerate T) {a b : Fin (T.necklace.dimension + 1)}
    (h : IsBead T.necklace a b) :
    f.necklaceMap.operator.toOrderHom a ≠ f.necklaceMap.operator.toOrderHom b := by
  intro hf
  apply (hND a b h)
  refine ⟨0, ?_, SimplexCategory.const ⦋length a b⦌ ⦋0⦌ 0,
    inputVertex U (f.necklaceMap.operator.toOrderHom a), (beadInputSimplex_collapsed f h hf).symm⟩
  change 0 < b.val - a.val
  have hh := h.positive
  change a.val < b.val at hh
  omega

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
