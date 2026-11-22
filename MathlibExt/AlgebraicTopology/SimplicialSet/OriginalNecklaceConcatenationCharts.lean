/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceConcatenationMaps

/-!
# Native full charts of a concatenated necklace

Each actual original prefix and suffix image is exactly its complete
piece of the concatenation. The charts use the native image map and
retain every scalar simplex and the full original inclusion equation.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

open OriginalTwoBead OriginalTwoBead.OrdinalCharts

/-- The whole first original piece is the exact image of the original first necklace. -/
theorem concatLeftPiece_image (T U : Data) :
    concatLeftPiece.{u} T U = (complex T.joints).image
      (SSet.stdSimplex.map (prefixOperator T.dimension U.dimension)) := by
  ext ⟨⟨d⟩⟩ s
  constructor
  · intro hs
    change s ∈ (complex (T.concat U).joints).obj (op ⦋d⦌) ∧
      s ∈ (left (pivot T.dimension U.dimension)).obj (op ⦋d⦌) at hs
    let a := (leftIso.{u} T.dimension U.dimension).inv.app (op ⦋d⦌) ⟨s, hs.2⟩
    have ha : (SSet.stdSimplex.map (prefixOperator T.dimension U.dimension)).app
        (op ⦋d⦌) a = s := by
      rw [← leftIso_inclusion, NatTrans.comp_app_apply]
      have he := ConcreteCategory.congr_hom
        (congr_app (leftIso.{u} T.dimension U.dimension).inv_hom_id (op ⦋d⦌)) ⟨s, hs.2⟩
      exact congrArg Subtype.val he
    refine ⟨a, ?_, ha⟩
    exact (prefix_mem_concat_iff T U a).mp (ha.symm ▸ hs.1)
  · rintro ⟨a, ha, rfl⟩
    constructor
    · exact (prefix_mem_concat_iff T U a).mpr ha
    · rw [← leftIso_inclusion, NatTrans.comp_app_apply]
      exact ((leftIso.{u} T.dimension U.dimension).hom.app (op ⦋d⦌) a).property

/-- The whole second original piece is the exact image of the original second necklace. -/
theorem concatRightPiece_image (T U : Data) :
    concatRightPiece.{u} T U = (complex U.joints).image
      (SSet.stdSimplex.map (suffixOperator T.dimension U.dimension)) := by
  ext ⟨⟨d⟩⟩ s
  constructor
  · intro hs
    change s ∈ (complex (T.concat U).joints).obj (op ⦋d⦌) ∧
      s ∈ (right (pivot T.dimension U.dimension)).obj (op ⦋d⦌) at hs
    let a := (rightIso.{u} T.dimension U.dimension).inv.app (op ⦋d⦌) ⟨s, hs.2⟩
    have ha : (SSet.stdSimplex.map (suffixOperator T.dimension U.dimension)).app
        (op ⦋d⦌) a = s := by
      rw [← rightIso_inclusion, NatTrans.comp_app_apply]
      have he := ConcreteCategory.congr_hom
        (congr_app (rightIso.{u} T.dimension U.dimension).inv_hom_id (op ⦋d⦌)) ⟨s, hs.2⟩
      exact congrArg Subtype.val he
    refine ⟨a, ?_, ha⟩
    exact (suffix_mem_concat_iff T U a).mp (ha.symm ▸ hs.1)
  · rintro ⟨a, ha, rfl⟩
    constructor
    · exact (suffix_mem_concat_iff T U a).mpr ha
    · rw [← rightIso_inclusion, NatTrans.comp_app_apply]
      exact ((rightIso.{u} T.dimension U.dimension).hom.app (op ⦋d⦌) a).property

/-- The same complete original prefix operator is a monomorphism. -/
instance prefix_mono (T U : Data) :
    Mono (SSet.stdSimplex.map (prefixOperator T.dimension U.dimension) :
      (Δ[T.dimension] : SSet.{u}) ⟶ Δ[T.dimension + U.dimension]) := by
  rw [← leftIso_inclusion.{u} T.dimension U.dimension]
  infer_instance

/-- The same complete original suffix operator is a monomorphism. -/
instance suffix_mono (T U : Data) :
    Mono (SSet.stdSimplex.map (suffixOperator T.dimension U.dimension) :
      (Δ[U.dimension] : SSet.{u}) ⟶ Δ[T.dimension + U.dimension]) := by
  rw [← rightIso_inclusion.{u} T.dimension U.dimension]
  infer_instance

/-- The native full first-necklace image map is an isomorphism. -/
instance left_image_iso (T U : Data) :
    IsIso ((complex.{u} T.joints).toImage
      (SSet.stdSimplex.map (prefixOperator T.dimension U.dimension))) := by
  have hm : Mono ((complex.{u} T.joints).toImage
      (SSet.stdSimplex.map (prefixOperator T.dimension U.dimension))) :=
    mono_of_mono_fac (Subcomplex.toImage_ι _ _)
  exact isIso_of_mono_of_epi _

/-- The native full second-necklace image map is an isomorphism. -/
instance right_image_iso (T U : Data) :
    IsIso ((complex.{u} U.joints).toImage
      (SSet.stdSimplex.map (suffixOperator T.dimension U.dimension))) := by
  have hm : Mono ((complex.{u} U.joints).toImage
      (SSet.stdSimplex.map (suffixOperator T.dimension U.dimension))) :=
    mono_of_mono_fac (Subcomplex.toImage_ι _ _)
  exact isIso_of_mono_of_epi _

/-- The canonical native chart of the complete original first necklace piece. -/
noncomputable def concatLeftChart (T U : Data) :
    T.object.{u} ≅ concatLeftPiece T U := by
  letI := left_image_iso.{u} T U
  exact asIso ((complex.{u} T.joints).toImage
    (SSet.stdSimplex.map (prefixOperator T.dimension U.dimension))) ≪≫
      Subcomplex.eqToIso (concatLeftPiece_image T U).symm

/-- The canonical native chart of the complete original second necklace piece. -/
noncomputable def concatRightChart (T U : Data) :
    U.object.{u} ≅ concatRightPiece T U := by
  letI := right_image_iso.{u} T U
  exact asIso ((complex.{u} U.joints).toImage
    (SSet.stdSimplex.map (suffixOperator T.dimension U.dimension))) ≪≫
      Subcomplex.eqToIso (concatRightPiece_image T U).symm

/-- The entire first chart retains the exact original prefix inclusion. -/
@[reassoc]
theorem concatLeftChart_ι (T U : Data) :
    (concatLeftChart.{u} T U).hom ≫ (concatLeftPiece T U).ι =
      (complex T.joints).ι ≫ SSet.stdSimplex.map
        (prefixOperator T.dimension U.dimension) := by
  rw [concatLeftChart, Iso.trans_hom, Category.assoc]
  exact Subcomplex.toImage_ι _ _

/-- The entire second chart retains the exact original suffix inclusion. -/
@[reassoc]
theorem concatRightChart_ι (T U : Data) :
    (concatRightChart.{u} T U).hom ≫ (concatRightPiece T U).ι =
      (complex U.joints).ι ≫ SSet.stdSimplex.map
        (suffixOperator T.dimension U.dimension) := by
  rw [concatRightChart, Iso.trans_hom, Category.assoc]
  exact Subcomplex.toImage_ι _ _

end SSet.OriginalNecklace
