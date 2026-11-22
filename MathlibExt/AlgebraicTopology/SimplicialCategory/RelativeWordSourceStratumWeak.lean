/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordSourceLayerMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordSourceShapeBoundaryWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceCoproducts

/-!
# Genuine weakness of the original raw source strata and attaching boundaries

Every original finite label shape is retained, with the unchanged target
letters and the actual original source Hom maps. The complete raw stratum
and its full attaching boundary are their genuine original indexed sums.
The proved shape maps therefore give weak maps on those SAME strata,
through the literal original decoding isomorphisms.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords
variable {O : Type u} {C D : FixedObjects O}

/-- Map each original finite shape by the same original complete factor map. -/
def shapeSumSourceChange (T : Data C) (F : C ⟶ D) (a b : O) (n : ℕ) :
    shapeSum T a b n ⟶ shapeSum (sourceChange T F) a b n :=
  SSet.IndexedSums.map (fun s : Shape O n => shapeSpace T s a b)
    (fun s => shapeSourceChange T F s a b)

/-- The complete original shape decoding retains the same raw source map. -/
theorem shapeSumSourceChange_square (T : Data C) (F : C ⟶ D) (a b : O) (n : ℕ) :
    (shapeSumIso T a b n).hom ≫ sourceRawLayerMap T F a b n =
      shapeSumSourceChange T F a b (n + 1) ≫ (shapeSumIso (sourceChange T F) a b n).hom := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro p
  apply Subtype.ext
  exact (shapeSourceChange_decode T F q p.1 p.2).symm

/-- The whole raw source map is weak for the genuine original Homwise weak input. -/
theorem sourceRawLayerMap_weak (T : Data C) (F : C ⟶ D)
    (hF : FixedObjectModel.weakEquivalences O F) (a b : O) (n : ℕ) :
    SSet.realizationWeakEquivalences (sourceRawLayerMap T F a b n) := by
  have h : SSet.realizationWeakEquivalences (shapeSumSourceChange T F a b (n + 1)) :=
    SSet.IndexedSums.map_property (fun s : Shape O (n + 1) => shapeSpace T s a b)
      SSet.realizationWeakEquivalences (fun s => shapeSourceChange T F s a b)
      (fun s => shapeSourceChange_weak T F hF s a b)
  exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
    (Arrow.isoMk' _ _ (shapeSumIso T a b n) (shapeSumIso (sourceChange T F) a b n)
      (shapeSumSourceChange_square T F a b n))).mp h

/-- Retain all original marked attaching-image shape boundaries in the full indexed map. -/
def boundaryShapesSourceChange (T : Data C) (F : C ⟶ D) (a b : O) (n : ℕ) :
    boundaryShapes T a b n ⟶ boundaryShapes (sourceChange T F) a b n :=
  SSet.IndexedSums.map (fun s : Shape O (n + 1) => (shapeBoundary T s a b).toSSet)
    (fun s => shapeBoundarySourceChange T F s a b)

/-- Decode every original boundary factor through the same actual raw source map. -/
theorem boundaryShapesSourceChange_square (T : Data C) (F : C ⟶ D) (a b : O) (n : ℕ) :
    boundaryShapesHom T a b n ≫ sourceBoundaryLayerMap T F a b n =
      boundaryShapesSourceChange T F a b n ≫ boundaryShapesHom (sourceChange T F) a b n := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro p
  apply Subtype.ext
  exact (shapeSourceChange_decode T F q p.1 p.2.val).symm

/-- The full original raw attaching boundary map is weak from genuine original source weakness. -/
theorem sourceBoundaryLayerMap_weak (T : Data C) (F : C ⟶ D)
    (hF : FixedObjectModel.weakEquivalences O F) (a b : O) (n : ℕ) :
    SSet.realizationWeakEquivalences (sourceBoundaryLayerMap T F a b n) := by
  have h : SSet.realizationWeakEquivalences (boundaryShapesSourceChange T F a b n) :=
    SSet.IndexedSums.map_property (fun s : Shape O (n + 1) => (shapeBoundary T s a b).toSSet)
      SSet.realizationWeakEquivalences (fun s => shapeBoundarySourceChange T F s a b)
      (fun s => shapeBoundarySourceChange_weak T F hF s a b)
  exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
    (Arrow.isoMk' _ _ (asIso (boundaryShapesHom T a b n))
      (asIso (boundaryShapesHom (sourceChange T F) a b n))
      (boundaryShapesSourceChange_square T F a b n))).mp h

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
