/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornFaces
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOrdinalFace

/-!
# Whole Hom maps of the supplied original coherent horn faces

The maps are extracted from the actual horn map. Their targets use the
same individual horn vertices, with both endpoint transports explicit.
The negative face reads back the original coherent face Hom map. All
common-face agreements follow from the original horn map, rather than
from supplied compatibility data.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornHomFaces
open SimplicialEnrichment

/-- Retarget an actual enriched Hom map using precisely its two original endpoint equalities. -/
def retargetMap {C D : Carrier.{u}} (F : C ⟶ D) (a b : C) {x y : D}
    (ha : F.obj a = x) (hb : F.obj b = y) : (a ⟶[SSet.{u}] b) ⟶ (x ⟶[SSet.{u}] y) :=
  F.map a b ≫ eqToHom (congrArg₂ (fun x y : D => x ⟶[SSet.{u}] y) ha hb)

/-- Whole enriched-map equality retains the same Hom map with the same original endpoint
transports. -/
theorem retargetMap_eq {C D : Carrier.{u}} {F G : C ⟶ D} (h : F = G) (a b : C)
    {x y : D} (ha : F.obj a = x) (hb : F.obj b = y)
    (ha' : G.obj a = x) (hb' : G.obj b = y) :
    retargetMap F a b ha hb = retargetMap G a b ha' hb' := by
  subst G
  rfl

variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- The actual supplied face Hom map into the same individual original horn endpoints. -/
def faceMap (j : Fin (n + 3)) (hj : j ≠ i) (a b : coherentSimplex.{u} ⦋n + 1⦌) :
    (a ⟶[SSet.{u}] b) ⟶
      (HornFaces.object f (j.succAbove a.as.down) ⟶[SSet.{u}]
        HornFaces.object f (j.succAbove b.as.down)) :=
  retargetMap (HornFaces.faceFunctor f j hj) a b
    (HornFaces.faceFunctor_obj f j hj a) (HornFaces.faceFunctor_obj f j hj b)

/-- The actual negative face map with the same original ordinal embedding and endpoints. -/
def negativeMap (j : Fin (n + 3)) (hj : j ≠ i) (a b : ULift.{u} (Fin (n + 2))) :
    (HomBoxDecomposition.negative ((OrdinalFace.embedding j) a) (ULift.up j)
      ((OrdinalFace.embedding j) b) : SSet.{u}) ⟶
        (HornFaces.object f (j.succAbove a.down) ⟶[SSet.{u}]
          HornFaces.object f (j.succAbove b.down)) :=
  (OrdinalFace.negativeIso j a b).inv ≫ faceMap f j hj (.mk a) (.mk b)

/-- Reading the whole supplied negative face returns exactly its original face Hom map. -/
theorem negativeMap_readback (j : Fin (n + 3)) (hj : j ≠ i)
    (a b : ULift.{u} (Fin (n + 2))) :
    (OrdinalFace.negativeIso j a b).hom ≫ negativeMap f j hj a b =
      faceMap f j hj (.mk a) (.mk b) := by
  exact (Category.assoc (OrdinalFace.negativeIso j a b).hom
      (OrdinalFace.negativeIso j a b).inv (faceMap f j hj (.mk a) (.mk b))).symm.trans
    ((congrArg (fun g => g ≫ faceMap f j hj (.mk a) (.mk b))
      (OrdinalFace.negativeIso j a b).hom_inv_id).trans (Category.id_comp _))

/-- The two actual common ordinal faces have exactly the same original vertex label. -/
theorem common_vertex (j k : Fin (n + 3)) (hjk : j < k) (a : Fin (n + 1)) :
    j.succAbove ((k.pred (Fin.ne_zero_of_lt hjk)).succAbove a) =
      k.succAbove ((j.castPred (Fin.ne_last_of_lt hjk)).succAbove a) := by
  have h : SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ SimplexCategory.δ k =
      SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ SimplexCategory.δ j := by
    apply SimplexCategory.δ_comp_δ'
    simpa only [Fin.castSucc_castPred] using hjk
  exact (congrArg (fun g : ⦋n⦌ ⟶ ⦋n + 2⦌ => g.toOrderHom a) h).symm

/-- The two supplied common coherent faces agree on the whole original Hom map with literal
common endpoints. -/
theorem common_map (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k)
    (a b : coherentSimplex.{u} ⦋n⦌) :
    retargetMap
      (coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))) ≫
        HornFaces.faceFunctor f j hj) a b
      (HornFaces.faceFunctor_obj f j hj
        ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).obj a))
      (HornFaces.faceFunctor_obj f j hj
        ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).obj b)) =
    retargetMap
      (coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk))) ≫
        HornFaces.faceFunctor f k hk) a b
      ((HornFaces.faceFunctor_obj f k hk
        ((coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)))).obj a)).trans
        (congrArg (HornFaces.object f) (common_vertex j k hjk a.as.down).symm))
      ((HornFaces.faceFunctor_obj f k hk
        ((coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)))).obj b)).trans
        (congrArg (HornFaces.object f) (common_vertex j k hjk b.as.down).symm)) :=
  retargetMap_eq (HornFaces.faceFunctor_compatibility f j k hj hk hjk) a b _ _ _ _

-- Materialize the unfolding equation here so importing modules share its source owner.
attribute [local simp] retargetMap

end CategoryTheory.CoherentRealization.HornHomFaces
