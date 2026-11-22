/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceBeadNormalizationFlags
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceConcatenatedBeads

/-!
# Genuine full-bead nondegeneracy under original concatenation

Every actual full bead of the SAME native concatenation is an original
full bead on one side of its pivot. The exact native interval maps and
whole input readbacks show that concatenating two genuinely totally
nondegenerate inputs retains this property, including zero sides.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace OriginalBeadInterval
open SSet.OriginalTwoBead.OrdinalCharts

private theorem equalLengthOperator_vertex {n m : ℕ} (h : n = m) (i : Fin (n + 1)) :
    ((eqToHom (congrArg SimplexCategory.mk h)).toOrderHom i).val = i.val := by
  subst m
  rfl

private theorem nonDegenerate_pullback_iso {K : SSet.{u}} {n m : ℕ}
    (β : ⦋n⦌ ⟶ ⦋m⦌) [IsIso β] (σ : K.nonDegenerate m) :
    K.map β.op σ ∈ K.nonDegenerate n := by
  have hm := SimplexCategory.eq_of_isIso β
  subst m
  rw [SimplexCategory.eq_id_of_epi β, op_id, CategoryTheory.Functor.map_id]
  exact σ.property

variable {K : SSet.{u}} {x y z : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The SAME original prefix image of a whole bead retains its actual nondegenerate input. -/
theorem concat_prefix_bead_nondegenerate (T : Object K x y q) (U : Object K y z q)
    (hT : TotallyNondegenerate T) {a b : Fin (T.necklace.dimension + 1)}
    (h : IsBead T.necklace a b)
    (h' : IsBead (concat T U).necklace
      (prefixEmbedding T.necklace.dimension U.necklace.dimension a)
      (prefixEmbedding T.necklace.dimension U.necklace.dimension b)) :
    beadInputSimplex (concat T U) h' ∈ K.nonDegenerate
      (length (prefixEmbedding T.necklace.dimension U.necklace.dimension a)
        (prefixEmbedding T.necklace.dimension U.necklace.dimension b)) := by
  have hm : length (prefixEmbedding T.necklace.dimension U.necklace.dimension a)
      (prefixEmbedding T.necklace.dimension U.necklace.dimension b) = length a b := rfl
  let β := eqToHom (congrArg SimplexCategory.mk hm)
  have hb : SSet.stdSimplex.map β ≫ beadMap.{u} h ≫ concatLeft T.necklace U.necklace = beadMap h' := by
    apply (cancel_mono (complex.{u} (T.necklace.concat U.necklace).joints).ι).1
    rw [Category.assoc, Category.assoc, concatLeft_ι, ← Category.assoc (beadMap h),
      beadMap_ι, beadMap_ι, ← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
    congr 1
  have hi : beadInputSimplex (concat T U) h' = K.map β.op (beadInputSimplex T h) := by
    unfold beadInputSimplex
    rw [SSet.yonedaEquiv_naturality, ← hb]
    simp only [Category.assoc, concatLeft_input]
  rw [hi]
  exact nonDegenerate_pullback_iso β ⟨beadInputSimplex T h, hT _ _ h⟩

/-- The SAME original suffix image of a whole bead retains its actual nondegenerate input. -/
theorem concat_suffix_bead_nondegenerate (T : Object K x y q) (U : Object K y z q)
    (hU : TotallyNondegenerate U) {a b : Fin (U.necklace.dimension + 1)}
    (h : IsBead U.necklace a b)
    (h' : IsBead (concat T U).necklace
      (suffix T.necklace.dimension U.necklace.dimension a)
      (suffix T.necklace.dimension U.necklace.dimension b)) :
    beadInputSimplex (concat T U) h' ∈ K.nonDegenerate
      (length (suffix T.necklace.dimension U.necklace.dimension a)
        (suffix T.necklace.dimension U.necklace.dimension b)) := by
  have hm : length (suffix T.necklace.dimension U.necklace.dimension a)
      (suffix T.necklace.dimension U.necklace.dimension b) = length a b := by
    change T.necklace.dimension + b.val - (T.necklace.dimension + a.val) = b.val - a.val
    omega
  let β := eqToHom (congrArg SimplexCategory.mk hm)
  have hb : SSet.stdSimplex.map β ≫ beadMap.{u} h ≫ concatRight T.necklace U.necklace = beadMap h' := by
    apply (cancel_mono (complex.{u} (T.necklace.concat U.necklace).joints).ι).1
    rw [Category.assoc, Category.assoc, concatRight_ι, ← Category.assoc (beadMap h),
      beadMap_ι, beadMap_ι, ← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
    congr 1
    ext i : 3
    apply Fin.ext
    have hi := equalLengthOperator_vertex hm i
    change (β.toOrderHom i).val = i.val at hi
    change T.necklace.dimension + (a.val + (β.toOrderHom i).val) =
      T.necklace.dimension + a.val + i.val
    omega
  have hi : beadInputSimplex (concat T U) h' = K.map β.op (beadInputSimplex U h) := by
    unfold beadInputSimplex
    rw [SSet.yonedaEquiv_naturality, ← hb]
    simp only [Category.assoc, concatRight_input]
  rw [hi]
  exact nonDegenerate_pullback_iso β ⟨beadInputSimplex U h, hU _ _ h⟩

/-- Both SAME genuinely totally nondegenerate original inputs concatenate to a genuine nondegenerate input. -/
theorem concat_totallyNondegenerate (T : Object K x y q) (U : Object K y z q)
    (hT : TotallyNondegenerate T) (hU : TotallyNondegenerate U) : TotallyNondegenerate (concat T U) := by
  intro a b h
  rcases concat_bead_cases T.necklace U.necklace h with ⟨c, d, hc, ha, hb⟩ | ⟨c, d, hc, ha, hb⟩
  · subst a
    subst b
    exact concat_prefix_bead_nondegenerate T U hT hc h
  · subst a
    subst b
    exact concat_suffix_bead_nondegenerate T U hU hc h

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
