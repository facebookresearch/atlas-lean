/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceConcatenationCharts

/-!
# Genuine original native necklace concatenation pushout

The actual original necklaces form a pushout along their same native
endpoint maps. Gluing retains both complete input maps and their target
naturality. Neither the pushout nor any comparison outcome is assumed.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

open OriginalTwoBead OriginalTwoBead.OrdinalCharts

/-- The actual pivot into the complete original first piece. -/
def concatPivotLeft (T U : Data) :
    (stdSimplex.face {pivot T.dimension U.dimension} : SSet.{u}) ⟶ concatLeftPiece T U :=
  Subcomplex.homOfLE (by rw [← concatPieces_inf]; exact inf_le_left)

/-- The same pivot into the complete original second piece. -/
def concatPivotRight (T U : Data) :
    (stdSimplex.face {pivot T.dimension U.dimension} : SSet.{u}) ⟶ concatRightPiece T U :=
  Subcomplex.homOfLE (by rw [← concatPieces_inf]; exact inf_le_right)

/-- The complete original first piece into the whole native concatenation. -/
def concatPieceLeft (T U : Data) : (concatLeftPiece.{u} T U : SSet.{u}) ⟶ (T.concat U).object :=
  Subcomplex.homOfLE inf_le_left

/-- The complete original second piece into the whole native concatenation. -/
def concatPieceRight (T U : Data) : (concatRightPiece.{u} T U : SSet.{u}) ⟶ (T.concat U).object :=
  Subcomplex.homOfLE inf_le_left

/-- The same original pivot and full pieces give the genuine native lattice pushout. -/
theorem concatPieces_isPushout (T U : Data) :
    IsPushout (concatPivotLeft.{u} T U) (concatPivotRight T U)
      (concatPieceLeft T U) (concatPieceRight T U) :=
  Subcomplex.BicartSq.isPushout
    (show Subcomplex.BicartSq (stdSimplex.face {pivot T.dimension U.dimension})
      (concatLeftPiece T U) (concatRightPiece T U) (complex (T.concat U).joints) from
      { sup_eq := concatPieces_sup T U, inf_eq := concatPieces_inf T U })

/-- The full native first chart reads the same original first-necklace map. -/
theorem concatLeftChart_piece (T U : Data) :
    (concatLeftChart.{u} T U).hom ≫ concatPieceLeft T U = concatLeft T U := by
  apply (cancel_mono (complex (T.concat U).joints).ι).1
  rw [Category.assoc]
  change (concatLeftChart T U).hom ≫ (concatLeftPiece T U).ι = _
  rw [concatLeftChart_ι, concatLeft_ι]

/-- The full native second chart reads the same original second-necklace map. -/
theorem concatRightChart_piece (T U : Data) :
    (concatRightChart.{u} T U).hom ≫ concatPieceRight T U = concatRight T U := by
  apply (cancel_mono (complex (T.concat U).joints).ι).1
  rw [Category.assoc]
  change (concatRightChart T U).hom ≫ (concatRightPiece T U).ι = _
  rw [concatRightChart_ι, concatRight_ι]

/-- The first original endpoint chart reads the same entire native pivot map. -/
theorem concatPivotLeft_chart (T U : Data) :
    (stdSimplex.faceSingletonIso.{u} (pivot T.dimension U.dimension)).hom ≫
      concatPivotLeft T U = T.target ≫ (concatLeftChart T U).hom := by
  apply (cancel_mono (concatLeftPiece T U).ι).1
  rw [Category.assoc]
  change (stdSimplex.faceSingletonIso _).hom ≫ (stdSimplex.face {_}).ι = _
  rw [Category.assoc, concatLeftChart_ι, ← Category.assoc]
  change _ = (vertexMap T.joints (Fin.last T.dimension) ≫ (complex T.joints).ι) ≫ _
  rw [vertexMap_ι, ← SSet.stdSimplex.map_comp]
  ext d s
  rfl

/-- The second original endpoint chart reads the same entire native pivot map. -/
theorem concatPivotRight_chart (T U : Data) :
    (stdSimplex.faceSingletonIso.{u} (pivot T.dimension U.dimension)).hom ≫
      concatPivotRight T U = U.source ≫ (concatRightChart T U).hom := by
  apply (cancel_mono (concatRightPiece T U).ι).1
  rw [Category.assoc]
  change (stdSimplex.faceSingletonIso _).hom ≫ (stdSimplex.face {_}).ι = _
  rw [Category.assoc, concatRightChart_ι, ← Category.assoc]
  change _ = (vertexMap U.joints 0 ≫ (complex U.joints).ι) ≫ _
  rw [vertexMap_ι, ← SSet.stdSimplex.map_comp]
  ext d s
  rfl

/-- The SAME original necklaces form the genuine pushout along their actual endpoint maps. -/
theorem concat_isPushout (T U : Data) :
    IsPushout (T.target.{u}) U.source (concatLeft T U) (concatRight T U) := by
  apply (concatPieces_isPushout T U).of_iso
    (stdSimplex.faceSingletonIso (pivot T.dimension U.dimension)).symm
    (concatLeftChart T U).symm (concatRightChart T U).symm (Iso.refl _)
  · apply (cancel_epi (stdSimplex.faceSingletonIso (pivot T.dimension U.dimension)).hom).1
    simp only [Iso.symm_hom]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, concatPivotLeft_chart,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · apply (cancel_epi (stdSimplex.faceSingletonIso (pivot T.dimension U.dimension)).hom).1
    simp only [Iso.symm_hom]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, concatPivotRight_chart,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    rw [← concatLeftChart_piece, Iso.inv_hom_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    rw [← concatRightChart_piece, Iso.inv_hom_id_assoc]

/-- Glue both entire original necklace inputs with their genuine original endpoint equality. -/
noncomputable def concatInput (T U : Data) {K : SSet.{u}}
    (l : T.object ⟶ K) (r : U.object ⟶ K)
    (h : T.target ≫ l = U.source ≫ r) : (T.concat U).object ⟶ K :=
  (concat_isPushout T U).desc l r h

/-- The actual gluing reads back the same complete original first input. -/
theorem concatLeft_input (T U : Data) {K : SSet.{u}}
    (l : T.object ⟶ K) (r : U.object ⟶ K)
    (h : T.target ≫ l = U.source ≫ r) :
    concatLeft T U ≫ concatInput T U l r h = l :=
  (concat_isPushout T U).inl_desc l r h

/-- The actual gluing reads back the same complete original second input. -/
theorem concatRight_input (T U : Data) {K : SSet.{u}}
    (l : T.object ⟶ K) (r : U.object ⟶ K)
    (h : T.target ≫ l = U.source ≫ r) :
    concatRight T U ≫ concatInput T U l r h = r :=
  (concat_isPushout T U).inr_desc l r h

/-- The entire original glued input is natural in every original target map. -/
theorem concatInput_naturality (T U : Data) {K L : SSet.{u}}
    (l : T.object ⟶ K) (r : U.object ⟶ K)
    (h : T.target ≫ l = U.source ≫ r) (f : K ⟶ L) :
    concatInput T U l r h ≫ f =
      concatInput T U (l ≫ f) (r ≫ f)
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ f) h).trans (Category.assoc _ _ _))) := by
  apply (concat_isPushout T U).hom_ext
  · rw [← Category.assoc, concatLeft_input, concatLeft_input]
  · rw [← Category.assoc, concatRight_input, concatRight_input]

end SSet.OriginalNecklace
