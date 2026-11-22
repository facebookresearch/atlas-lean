/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalMappingComposition
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerMapping
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# Gluing adjacent triangles in a Segal space

The union of the 012 and 123 faces of a tetrahedron presents compatible adjacent triangles as a
pullback of mapping spaces. With four prescribed vertices, restriction from tetrahedra to
adjacent triangles is a Kan fibration for Reedy-fibrant simplicial spaces and a trivial
fibration for Segal spaces. The face, edge and comparison maps retain their projection and
target-naturality equations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen
open SimplicialSpace SegalHomotopy

namespace SimplicialSpace.AdjacentTriangle

/-- The literal original adjacent triangle union, ordered012 then123. -/
def faceUnion : (Δ[3] : SSet.{u}).Subcomplex :=
  SSet.stdSimplex.face {(3 : Fin 4)}ᶜ ⊔ SSet.stdSimplex.face {(0 : Fin 4)}ᶜ

/-- The whole original tetrahedron object over its three prescribed edges. -/
abbrev tetrahedron (W : SimplicialSpace.{u}) (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  pullback (threeEdgeComparison W) (threeEdgePair W w x y z)

/-- The actual original W3 projection. -/
abbrev tetrahedronProjection (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) : tetrahedron W w x y z ⟶ W.diagram _⦋3⦌ :=
  pullback.fst _ _

/-- The actual prescribed composable triple projection. -/
abbrev tetrahedronEdges (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedron W w x y z ⟶ (mappingFibre W w x ⨯ mappingFibre W x y) ⨯ mappingFibre W y z :=
  pullback.snd _ _

/-- Compatible adjacent original triangles share precisely the original12 mapping fibre. -/
abbrev pair (W : SimplicialSpace.{u}) (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  pullback (triangleComparison W w x y ≫ prod.snd)
    (triangleComparison W x y z ≫ prod.fst)

/-- The actual012 triangle projection. -/
abbrev pair012 (W : SimplicialSpace.{u}) (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    pair W w x y z ⟶ triangleSpace W w x y := pullback.fst _ _

/-- The actual123 triangle projection. -/
abbrev pair123 (W : SimplicialSpace.{u}) (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    pair W w x y z ⟶ triangleSpace W x y z := pullback.snd _ _

/-- The actual full triple from a compatible pair uses the SAME central12 once. -/
def pairEdges (W : SimplicialSpace.{u}) (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    pair W w x y z ⟶ (mappingFibre W w x ⨯ mappingFibre W x y) ⨯ mappingFibre W y z :=
  prod.lift
    (prod.lift (pair012 W w x y z ≫ triangleComparison W w x y ≫ prod.fst)
      (pair012 W w x y z ≫ triangleComparison W w x y ≫ prod.snd))
    (pair123 W w x y z ≫ triangleComparison W x y z ≫ prod.snd)

/-- The original central edge equation is the entire native pullback condition. -/
theorem pair_central (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    pair012 W w x y z ≫ triangleComparison W w x y ≫ prod.snd =
      pair123 W w x y z ≫ triangleComparison W x y z ≫ prod.fst :=
  pullback.condition

/-- The original tetrahedron keeps its whole original triple matching equation. -/
theorem tetrahedron_condition (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedronProjection W w x y z ≫ threeEdgeComparison W =
      tetrahedronEdges W w x y z ≫ threeEdgePair W w x y z :=
  pullback.condition

/-- The original face union has exactly the original central12 intersection. -/
theorem faceIntersection :
    SSet.stdSimplex.face.{u} {(3 : Fin 4)}ᶜ ⊓ SSet.stdSimplex.face {(0 : Fin 4)}ᶜ =
      SSet.stdSimplex.face {(0 : Fin 4), 3}ᶜ := by
  rw [SSet.stdSimplex.face_inter_face]
  congr 1

/-- The original adjacent faces form their actual union pushout. -/
theorem faceUnion_isPushout :
    IsPushout
      (SSet.Subcomplex.homOfLE (show SSet.stdSimplex.face.{u} {(0 : Fin 4), 3}ᶜ ≤
        SSet.stdSimplex.face {(3 : Fin 4)}ᶜ from by rw [← faceIntersection]; exact inf_le_left))
      (SSet.Subcomplex.homOfLE (show SSet.stdSimplex.face.{u} {(0 : Fin 4), 3}ᶜ ≤
        SSet.stdSimplex.face {(0 : Fin 4)}ᶜ from by rw [← faceIntersection]; exact inf_le_right))
      (SSet.Subcomplex.homOfLE (le_sup_left : SSet.stdSimplex.face.{u} {(3 : Fin 4)}ᶜ ≤ faceUnion))
      (SSet.Subcomplex.homOfLE (le_sup_right : SSet.stdSimplex.face.{u} {(0 : Fin 4)}ᶜ ≤
          faceUnion)) :=
  (show SSet.Subcomplex.BicartSq (SSet.stdSimplex.face.{u} {(0 : Fin 4), 3}ᶜ)
    (SSet.stdSimplex.face {(3 : Fin 4)}ᶜ) (SSet.stdSimplex.face {(0 : Fin 4)}ᶜ) faceUnion from
      ⟨rfl, faceIntersection⟩).isPushout


private theorem discretePreservesPushouts :
    PreservesColimitsOfShape WalkingSpan SSet.simplicialSpaceDiscrete.{u} :=
  ⟨fun {K} => ⟨fun c {hc} => ⟨by
    apply evaluationJointlyReflectsColimits _ (fun k => ?_)
    change IsColimit
      ((((evaluation _ _).obj k ⋙ SimplicialObject.const (Type u)).mapCocone c))
    exact isColimitOfPreserves _ hc⟩⟩⟩

private theorem innerFlipPreservesPullbacks (W : SimplicialSpace.{u}) :
    PreservesLimitsOfShape WalkingCospan (innerHomFunctor.flip.obj W) := by
  let : ∀ K : SSet.{u}, PreservesColimitsOfShape WalkingCospanᵒᵖ
      (innerTensorBifunctor.flip.obj K) := fun K => by
    change PreservesColimitsOfShape WalkingCospanᵒᵖ (innerTensor K)
    let : (innerTensor K).IsLeftAdjoint := (innerTensorCotensorAdjunction K).isLeftAdjoint
    infer_instance
  exact innerTensorHomAdjunction₂.preservesLimitsOfShape_flip_obj WalkingCospan W

/-- The original012 face inclusion into the union. -/
abbrev union012 : (SSet.stdSimplex.face.{u} {(3 : Fin 4)}ᶜ : SSet.{u}) ⟶ faceUnion :=
  SSet.Subcomplex.homOfLE le_sup_left

/-- The original123 face inclusion into the union. -/
abbrev union123 : (SSet.stdSimplex.face.{u} {(0 : Fin 4)}ᶜ : SSet.{u}) ⟶ faceUnion :=
  SSet.Subcomplex.homOfLE le_sup_right

/-- The central12 edge inclusion into the original012 face. -/
abbrev central012 : (SSet.stdSimplex.face.{u} {(0 : Fin 4), 3}ᶜ : SSet.{u}) ⟶
    SSet.stdSimplex.face {(3 : Fin 4)}ᶜ :=
  SSet.Subcomplex.homOfLE (by rw [← faceIntersection]; exact inf_le_left)

/-- The same central12 edge inclusion into the original123 face. -/
abbrev central123 : (SSet.stdSimplex.face.{u} {(0 : Fin 4), 3}ᶜ : SSet.{u}) ⟶
    SSet.stdSimplex.face {(0 : Fin 4)}ᶜ :=
  SSet.Subcomplex.homOfLE (by rw [← faceIntersection]; exact inf_le_right)

/-- Actual inner mapping takes this original adjacent-face union to its chosen pullback. -/
theorem mappedUnion_isPullback (W : SimplicialSpace.{u}) :
    IsPullback ((discreteSourceMapping W).map union012.op)
      ((discreteSourceMapping W).map union123.op)
      ((discreteSourceMapping W).map central012.op)
      ((discreteSourceMapping W).map central123.op) := by
  let := discretePreservesPushouts.{u}
  let := innerFlipPreservesPullbacks W
  have sq := ((faceUnion_isPushout.{u}).map SSet.simplicialSpaceDiscrete).map ofSimplicialObject
  exact (sq.op.map (innerHomFunctor.flip.obj W)).flip

/-- Original mapping out of face012 identifies with the SAME W2. -/
def mapping012Iso (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).obj (op (SSet.stdSimplex.face.{u} {(3 : Fin 4)}ᶜ : SSet.{u})) ≅
      W.diagram _⦋2⦌ :=
  (discreteSourceMapping W).mapIso (SSet.stdSimplex.faceSingletonComplIso (3 : Fin 4)).op ≪≫
    discreteYonedaIso W 2

/-- Original mapping out of face123 identifies with the SAME W2. -/
def mapping123Iso (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).obj (op (SSet.stdSimplex.face.{u} {(0 : Fin 4)}ᶜ : SSet.{u})) ≅
      W.diagram _⦋2⦌ :=
  (discreteSourceMapping W).mapIso (SSet.stdSimplex.faceSingletonComplIso (0 : Fin 4)).op ≪≫
    discreteYonedaIso W 2

/-- Original mapping out of central12 identifies with the SAME W1. -/
def mappingCentralIso (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).obj (op (SSet.stdSimplex.face.{u} {(0 : Fin 4), 3}ᶜ : SSet.{u})) ≅
      W.diagram _⦋1⦌ :=
  (discreteSourceMapping W).mapIso
    (SSet.stdSimplex.facePairComplIso (0 : Fin 4) 3 (by decide)).op ≪≫ discreteYonedaIso W 1


private theorem central012_face :
    (SSet.stdSimplex.facePairComplIso.{u} (0 : Fin 4) 3 (by decide)).hom ≫ central012 =
      SSet.stdSimplex.δ (0 : Fin 3) ≫
        (SSet.stdSimplex.faceSingletonComplIso (3 : Fin 4)).hom := by
  apply (cancel_mono (SSet.stdSimplex.face.{u} {(3 : Fin 4)}ᶜ).ι).mp
  simp only [central012, Category.assoc, SSet.Subcomplex.homOfLE_ι,
    SSet.stdSimplex.faceSingletonComplIso_hom_ι, SSet.stdSimplex.facePairComplIso_hom_ι]
  rfl

private theorem central123_face :
    (SSet.stdSimplex.facePairComplIso.{u} (0 : Fin 4) 3 (by decide)).hom ≫ central123 =
      SSet.stdSimplex.δ (2 : Fin 3) ≫
        (SSet.stdSimplex.faceSingletonComplIso (0 : Fin 4)).hom := by
  apply (cancel_mono (SSet.stdSimplex.face.{u} {(0 : Fin 4)}ᶜ).ι).mp
  simp only [central123, Category.assoc, SSet.Subcomplex.homOfLE_ι,
    SSet.stdSimplex.faceSingletonComplIso_hom_ι, SSet.stdSimplex.facePairComplIso_hom_ι']
  rfl

/-- The original central12 inclusion in012 is precisely its last edge. -/
@[reassoc]
theorem mappingCentral012 (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).map central012.op ≫ (mappingCentralIso W).hom =
      (mapping012Iso W).hom ≫ W.diagram.δ (0 : Fin 3) := by
  unfold mappingCentralIso mapping012Iso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  change (discreteSourceMapping W).map central012.op ≫
      (discreteSourceMapping W).map (SSet.stdSimplex.facePairComplIso (0 : Fin 4) 3
          (by decide)).hom.op ≫
        (discreteYonedaIso W 1).hom =
    (discreteSourceMapping W).map (SSet.stdSimplex.faceSingletonComplIso (3 : Fin 4)).hom.op ≫
      (discreteYonedaIso W 2).hom ≫ W.diagram.δ (0 : Fin 3)
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ _ => (discreteSourceMapping W).map f.op)
    central012_face.{u}
  simp only [op_comp, Functor.map_comp] at h
  rw [← Category.assoc, h, Category.assoc]
  exact congrArg (fun f =>
    (discreteSourceMapping W).map (SSet.stdSimplex.faceSingletonComplIso (3 : Fin 4)).hom.op ≫ f)
      (discreteYonedaIso_naturality_index W (SimplexCategory.δ (0 : Fin 3)))

/-- The SAME central12 inclusion in123 is precisely its first edge. -/
@[reassoc]
theorem mappingCentral123 (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).map central123.op ≫ (mappingCentralIso W).hom =
      (mapping123Iso W).hom ≫ W.diagram.δ (2 : Fin 3) := by
  unfold mappingCentralIso mapping123Iso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  change (discreteSourceMapping W).map central123.op ≫
      (discreteSourceMapping W).map (SSet.stdSimplex.facePairComplIso (0 : Fin 4) 3
          (by decide)).hom.op ≫
        (discreteYonedaIso W 1).hom =
    (discreteSourceMapping W).map (SSet.stdSimplex.faceSingletonComplIso (0 : Fin 4)).hom.op ≫
      (discreteYonedaIso W 2).hom ≫ W.diagram.δ (2 : Fin 3)
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ _ => (discreteSourceMapping W).map f.op)
    central123_face.{u}
  simp only [op_comp, Functor.map_comp] at h
  rw [← Category.assoc, h, Category.assoc]
  exact congrArg (fun f =>
    (discreteSourceMapping W).map (SSet.stdSimplex.faceSingletonComplIso (0 : Fin 4)).hom.op ≫ f)
      (discreteYonedaIso_naturality_index W (SimplexCategory.δ (2 : Fin 3)))

/-- The original raw adjacent triangles meet at exactly edge12. -/
abbrev rawPair (W : SimplicialSpace.{u}) : SSet.{u} :=
  pullback (W.diagram.δ (0 : Fin 3)) (W.diagram.δ (2 : Fin 3))

private theorem mappedUnion_raw_isPullback (W : SimplicialSpace.{u}) :
    IsPullback
      ((discreteSourceMapping W).map union012.op ≫ (mapping012Iso W).hom)
      ((discreteSourceMapping W).map union123.op ≫ (mapping123Iso W).hom)
      (W.diagram.δ (0 : Fin 3)) (W.diagram.δ (2 : Fin 3)) :=
  (mappedUnion_isPullback W).of_iso (Iso.refl _) (mapping012Iso W) (mapping123Iso W)
    (mappingCentralIso W) (by simp) (by simp) (mappingCentral012 W) (mappingCentral123 W)

/-- Actual mapping out of the face union is the original raw adjacent-triangle pullback. -/
def mappingUnionIso (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).obj (op (faceUnion : SSet.{u})) ≅ rawPair W :=
  (mappedUnion_raw_isPullback W).isoPullback

/-- The union isomorphism retains the whole original012 projection. -/
@[reassoc (attr := simp)]
theorem mappingUnionIso_fst (W : SimplicialSpace.{u}) :
    (mappingUnionIso W).hom ≫ pullback.fst _ _ =
      (discreteSourceMapping W).map union012.op ≫ (mapping012Iso W).hom :=
  (mappedUnion_raw_isPullback W).isoPullback_hom_fst

/-- The union isomorphism retains the whole original123 projection. -/
@[reassoc (attr := simp)]
theorem mappingUnionIso_snd (W : SimplicialSpace.{u}) :
    (mappingUnionIso W).hom ≫ pullback.snd _ _ =
      (discreteSourceMapping W).map union123.op ≫ (mapping123Iso W).hom :=
  (mappedUnion_raw_isPullback W).isoPullback_hom_snd

/-- The inverse union isomorphism retains the entire original012 projection. -/
@[reassoc (attr := simp)]
theorem mappingUnionIso_inv_fst (W : SimplicialSpace.{u}) :
    (mappingUnionIso W).inv ≫ (discreteSourceMapping W).map union012.op ≫ (mapping012Iso W).hom =
      pullback.fst (W.diagram.δ (0 : Fin 3)) (W.diagram.δ (2 : Fin 3)) :=
  (mappedUnion_raw_isPullback W).isoPullback_inv_fst

/-- The inverse union isomorphism retains the entire original123 projection. -/
@[reassoc (attr := simp)]
theorem mappingUnionIso_inv_snd (W : SimplicialSpace.{u}) :
    (mappingUnionIso W).inv ≫ (discreteSourceMapping W).map union123.op ≫ (mapping123Iso W).hom =
      pullback.snd (W.diagram.δ (0 : Fin 3)) (W.diagram.δ (2 : Fin 3)) :=
  (mappedUnion_raw_isPullback W).isoPullback_inv_snd

private theorem face_edge_eq (W : SimplicialSpace.{u})
    (i : Fin 4) (j : Fin 3) (e : ⦋1⦌ ⟶ ⦋3⦌)
    (h : SimplexCategory.δ j ≫ SimplexCategory.δ i = e) :
    W.diagram.δ i ≫ W.diagram.δ j = W.diagram.map e.op := by
  change W.diagram.map (SimplexCategory.δ i).op ≫
    W.diagram.map (SimplexCategory.δ j).op = _
  rw [← Functor.map_comp, ← op_comp, h]

/-- The original adjacent triangle face maps share exactly edge12. -/
theorem raw_central (W : SimplicialSpace.{u}) :
    W.diagram.δ (3 : Fin 4) ≫ W.diagram.δ (0 : Fin 3) =
      W.diagram.δ (0 : Fin 4) ≫ W.diagram.δ (2 : Fin 3) := by
  rw [face_edge_eq W 3 0 (SimplexCategory.mkOfSucc (1 : Fin 3)) (by decide),
    face_edge_eq W 0 2 (SimplexCategory.mkOfSucc (1 : Fin 3)) (by decide)]

/-- The original raw restriction keeps both entire adjacent W2 faces. -/
def rawComparison (W : SimplicialSpace.{u}) : W.diagram _⦋3⦌ ⟶ rawPair W :=
  pullback.lift (W.diagram.δ (3 : Fin 4)) (W.diagram.δ (0 : Fin 4)) (raw_central W)

/-- The original first W3 edge is the first prescribed mapping fibre. -/
@[reassoc]
theorem tetrahedron_first (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedronProjection W w x y z ≫
        W.diagram.map (SimplexCategory.mkOfSucc (0 : Fin 3)).op =
      tetrahedronEdges W w x y z ≫ prod.fst ≫ prod.fst ≫ mappingFibre.fst W w x := by
  rw [← threeEdgeComparison_first, ← Category.assoc, tetrahedron_condition]
  rw [Category.assoc, threeEdgePair_first]

/-- The original middle W3 edge is the SAME central prescribed mapping fibre. -/
@[reassoc]
theorem tetrahedron_second (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedronProjection W w x y z ≫
        W.diagram.map (SimplexCategory.mkOfSucc (1 : Fin 3)).op =
      tetrahedronEdges W w x y z ≫ prod.fst ≫ prod.snd ≫ mappingFibre.fst W x y := by
  rw [← threeEdgeComparison_second, ← Category.assoc, tetrahedron_condition]
  rw [Category.assoc, threeEdgePair_second]

/-- The original last W3 edge is the last prescribed mapping fibre. -/
@[reassoc]
theorem tetrahedron_third (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedronProjection W w x y z ≫
        W.diagram.map (SimplexCategory.mkOfSucc (2 : Fin 3)).op =
      tetrahedronEdges W w x y z ≫ prod.snd ≫ mappingFibre.fst W y z := by
  rw [← threeEdgeComparison_third, ← Category.assoc, tetrahedron_condition]
  rw [Category.assoc, threeEdgePair_third]

/-- The literal012 face of the original tetrahedron. -/
def face012 (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedron W w x y z ⟶ triangleSpace W w x y :=
  pullback.lift (tetrahedronProjection W w x y z ≫ W.diagram.δ (3 : Fin 4))
    (tetrahedronEdges W w x y z ≫ prod.fst) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst]
        rw [face_edge_eq W 3 2 (SimplexCategory.mkOfSucc (0 : Fin 3)) (by decide)]
        exact tetrahedron_first W w x y z
      · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd]
        rw [face_edge_eq W 3 0 (SimplexCategory.mkOfSucc (1 : Fin 3)) (by decide)]
        exact tetrahedron_second W w x y z)

/-- The literal123 face of the SAME original tetrahedron. -/
def face123 (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedron W w x y z ⟶ triangleSpace W x y z :=
  pullback.lift (tetrahedronProjection W w x y z ≫ W.diagram.δ (0 : Fin 4))
    (prod.lift (tetrahedronEdges W w x y z ≫ prod.fst ≫ prod.snd)
      (tetrahedronEdges W w x y z ≫ prod.snd)) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst,
          prod.lift_fst_assoc]
        rw [face_edge_eq W 0 2 (SimplexCategory.mkOfSucc (1 : Fin 3)) (by decide)]
        exact tetrahedron_second W w x y z
      · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd, prod.lift_snd_assoc]
        rw [face_edge_eq W 0 0 (SimplexCategory.mkOfSucc (2 : Fin 3)) (by decide)]
        exact tetrahedron_third W w x y z)

/-- The012 face retains its original W2 projection. -/
@[reassoc (attr := simp)]
theorem face012_projection (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    face012 W w x y z ≫ triangleProjection W w x y =
      tetrahedronProjection W w x y z ≫ W.diagram.δ (3 : Fin 4) := pullback.lift_fst _ _ _

/-- The123 face retains its original W2 projection. -/
@[reassoc (attr := simp)]
theorem face123_projection (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    face123 W w x y z ≫ triangleProjection W x y z =
      tetrahedronProjection W w x y z ≫ W.diagram.δ (0 : Fin 4) := pullback.lift_fst _ _ _

/-- The012 face retains both original prescribed mapping fibres. -/
@[reassoc (attr := simp)]
theorem face012_edges (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    face012 W w x y z ≫ triangleComparison W w x y =
      tetrahedronEdges W w x y z ≫ prod.fst := pullback.lift_snd _ _ _

/-- The123 face retains the central and last original prescribed mapping fibres. -/
@[reassoc (attr := simp)]
theorem face123_edges (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    face123 W w x y z ≫ triangleComparison W x y z =
      prod.lift (tetrahedronEdges W w x y z ≫ prod.fst ≫ prod.snd)
        (tetrahedronEdges W w x y z ≫ prod.snd) := pullback.lift_snd _ _ _

/-- The123 triangle retains exactly the original central12 mapping fibre. -/
@[reassoc]
theorem face123_first (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    face123 W w x y z ≫ triangleComparison W x y z ≫ prod.fst =
      tetrahedronEdges W w x y z ≫ prod.fst ≫ prod.snd := by
  rw [← Category.assoc, face123_edges, prod.lift_fst]

/-- The123 triangle retains exactly the original last23 mapping fibre. -/
@[reassoc]
theorem face123_last (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    face123 W w x y z ≫ triangleComparison W x y z ≫ prod.snd =
      tetrahedronEdges W w x y z ≫ prod.snd := by
  rw [← Category.assoc, face123_edges, prod.lift_snd]

/-- The whole original adjacent comparison takes precisely the two literal adjacent faces. -/
def comparison (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) : tetrahedron W w x y z ⟶ pair W w x y z :=
  pullback.lift (face012 W w x y z) (face123 W w x y z)
    (by simp only [← Category.assoc, face012_edges, face123_edges, prod.lift_fst])

/-- The comparison retains the entire012 triangle. -/
@[reassoc (attr := simp)]
theorem comparison012 (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    comparison W w x y z ≫ pair012 W w x y z = face012 W w x y z :=
  pullback.lift_fst _ _ _

/-- The comparison retains the entire123 triangle. -/
@[reassoc (attr := simp)]
theorem comparison123 (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    comparison W w x y z ≫ pair123 W w x y z = face123 W w x y z :=
  pullback.lift_snd _ _ _

/-- The whole original triple is unchanged by adjacent gluing. -/
@[reassoc (attr := simp)]
theorem comparison_edges (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    comparison W w x y z ≫ pairEdges W w x y z = tetrahedronEdges W w x y z := by
  unfold pairEdges
  ext <;> simp only [Category.assoc, prod.lift_fst, prod.lift_snd, comparison012_assoc,
      comparison123_assoc,
    face012_edges_assoc, face123_edges_assoc]


private theorem restriction012 (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).map faceUnion.ι.op ≫
        (discreteSourceMapping W).map union012.op ≫ (mapping012Iso W).hom =
      (discreteYonedaIso W 3).hom ≫ W.diagram.δ (3 : Fin 4) := by
  unfold mapping012Iso
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  change (discreteSourceMapping W).map faceUnion.ι.op ≫
      (discreteSourceMapping W).map union012.op ≫
        (discreteSourceMapping W).map (SSet.stdSimplex.faceSingletonComplIso (3 : Fin 4)).hom.op ≫
          (discreteYonedaIso W 2).hom = _
  have h : (SSet.stdSimplex.faceSingletonComplIso.{u} (3 : Fin 4)).hom ≫
      union012 ≫ faceUnion.ι = SSet.stdSimplex.δ (3 : Fin 4) := by
    change (SSet.stdSimplex.faceSingletonComplIso.{u} (3 : Fin 4)).hom ≫
      (SSet.stdSimplex.face {(3 : Fin 4)}ᶜ).ι = _
    exact SSet.stdSimplex.faceSingletonComplIso_hom_ι (3 : Fin 4)
  have hm := congrArg (fun f : (Δ[2] : SSet.{u}) ⟶ Δ[3] => (discreteSourceMapping W).map f.op) h
  simp only [op_comp, Functor.map_comp, Category.assoc] at hm
  calc
    _ = (discreteSourceMapping W).map (SSet.stdSimplex.δ (3 : Fin 4)).op ≫
        (discreteYonedaIso W 2).hom := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ (discreteYonedaIso W 2).hom) hm
    _ = _ := discreteYonedaIso_naturality_index W (SimplexCategory.δ (3 : Fin 4))

private theorem restriction123 (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).map faceUnion.ι.op ≫
        (discreteSourceMapping W).map union123.op ≫ (mapping123Iso W).hom =
      (discreteYonedaIso W 3).hom ≫ W.diagram.δ (0 : Fin 4) := by
  unfold mapping123Iso
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  change (discreteSourceMapping W).map faceUnion.ι.op ≫
      (discreteSourceMapping W).map union123.op ≫
        (discreteSourceMapping W).map (SSet.stdSimplex.faceSingletonComplIso (0 : Fin 4)).hom.op ≫
          (discreteYonedaIso W 2).hom = _
  have h : (SSet.stdSimplex.faceSingletonComplIso.{u} (0 : Fin 4)).hom ≫
      union123 ≫ faceUnion.ι = SSet.stdSimplex.δ (0 : Fin 4) := by
    change (SSet.stdSimplex.faceSingletonComplIso.{u} (0 : Fin 4)).hom ≫
      (SSet.stdSimplex.face {(0 : Fin 4)}ᶜ).ι = _
    exact SSet.stdSimplex.faceSingletonComplIso_hom_ι (0 : Fin 4)
  have hm := congrArg (fun f : (Δ[2] : SSet.{u}) ⟶ Δ[3] => (discreteSourceMapping W).map f.op) h
  simp only [op_comp, Functor.map_comp, Category.assoc] at hm
  calc
    _ = (discreteSourceMapping W).map (SSet.stdSimplex.δ (0 : Fin 4)).op ≫
        (discreteYonedaIso W 2).hom := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ (discreteYonedaIso W 2).hom) hm
    _ = _ := discreteYonedaIso_naturality_index W (SimplexCategory.δ (0 : Fin 4))

/-- The original union restriction is precisely the two whole adjacent faces. -/
@[reassoc]
theorem rawComparison_eq_restriction (W : SimplicialSpace.{u}) :
    rawComparison W = (discreteYonedaIso W 3).inv ≫
      (discreteSourceMapping W).map faceUnion.ι.op ≫ (mappingUnionIso W).hom := by
  apply pullback.hom_ext
  · simp only [rawComparison, pullback.lift_fst, Category.assoc, mappingUnionIso_fst]
    rw [restriction012, Iso.inv_hom_id_assoc]
  · simp only [rawComparison, pullback.lift_snd, Category.assoc, mappingUnionIso_snd]
    rw [restriction123, Iso.inv_hom_id_assoc]


/-- The compatible pair retains its original raw adjacent W2 faces. -/
def pairProjection (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) : pair W w x y z ⟶ rawPair W :=
  pullback.lift (pair012 W w x y z ≫ triangleProjection W w x y)
    (pair123 W w x y z ≫ triangleProjection W x y z) (by
      simpa only [Category.assoc, triangleProjection_last, triangleProjection_first] using
        congrArg (fun f => f ≫ mappingFibre.fst W x y) (pair_central W w x y z))

/-- The raw projection preserves the entire012 W2 face. -/
@[reassoc (attr := simp)]
theorem pairProjection_fst (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    pairProjection W w x y z ≫ pullback.fst _ _ =
      pair012 W w x y z ≫ triangleProjection W w x y := pullback.lift_fst _ _ _

/-- The raw projection preserves the entire123 W2 face. -/
@[reassoc (attr := simp)]
theorem pairProjection_snd (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    pairProjection W w x y z ≫ pullback.snd _ _ =
      pair123 W w x y z ≫ triangleProjection W x y z := pullback.lift_snd _ _ _

/-- The original adjacent comparison lies over the original raw face restriction. -/
@[reassoc]
theorem comparison_projection (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    comparison W w x y z ≫ pairProjection W w x y z =
      tetrahedronProjection W w x y z ≫ rawComparison W := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pairProjection_fst, pairProjection_snd,
      comparison012_assoc, comparison123_assoc, face012_projection, face123_projection,
      rawComparison, pullback.lift_fst, pullback.lift_snd]

/-- The first two original edges of a pair are exactly its012 comparison. -/
@[reassoc (attr := simp)]
theorem pairEdges_fst (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    pairEdges W w x y z ≫ prod.fst = pair012 W w x y z ≫ triangleComparison W w x y := by
  apply prod.hom_ext <;> simp only [pairEdges, Category.assoc, prod.lift_fst, prod.lift_snd]

/-- The final original edge of a pair is exactly the final123 comparison edge. -/
@[reassoc (attr := simp)]
theorem pairEdges_snd (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    pairEdges W w x y z ≫ prod.snd =
      pair123 W w x y z ≫ triangleComparison W x y z ≫ prod.snd := prod.lift_snd _ _

/-- The last two original edges of a pair are exactly its123 comparison. -/
theorem pairEdges_lastTwo (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    prod.lift (pairEdges W w x y z ≫ prod.fst ≫ prod.snd)
      (pairEdges W w x y z ≫ prod.snd) =
        pair123 W w x y z ≫ triangleComparison W x y z := by
  apply prod.hom_ext
  · rw [prod.lift_fst, pairEdges_fst_assoc]
    exact pair_central W w x y z
  · rw [prod.lift_snd, pairEdges_snd, Category.assoc]

private theorem raw_fixed_edges (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) {A : SSet.{u}}
    (a : A ⟶ pair W w x y z) (b : A ⟶ W.diagram _⦋3⦌)
    (h : a ≫ pairProjection W w x y z = b ≫ rawComparison W) :
    b ≫ threeEdgeComparison W = a ≫ pairEdges W w x y z ≫ threeEdgePair W w x y z := by
  have h012 : a ≫ pair012 W w x y z ≫ triangleProjection W w x y =
      b ≫ W.diagram.δ (3 : Fin 4) := by
    simpa only [Category.assoc, pairProjection_fst, rawComparison, pullback.lift_fst] using
      congrArg (fun f => f ≫ pullback.fst _ _) h
  have h123 : a ≫ pair123 W w x y z ≫ triangleProjection W x y z =
      b ≫ W.diagram.δ (0 : Fin 4) := by
    simpa only [Category.assoc, pairProjection_snd, rawComparison, pullback.lift_snd] using
      congrArg (fun f => f ≫ pullback.snd _ _) h
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, threeEdgeComparison_first, threeEdgePair_first]
      rw [← face_edge_eq W 3 2 (SimplexCategory.mkOfSucc (0 : Fin 3)) (by decide)]
      rw [← reassoc_of% h012, triangleProjection_first]
      simp only [pairEdges_fst_assoc]
    · simp only [Category.assoc, threeEdgeComparison_second, threeEdgePair_second]
      rw [← face_edge_eq W 3 0 (SimplexCategory.mkOfSucc (1 : Fin 3)) (by decide)]
      rw [← reassoc_of% h012, triangleProjection_last]
      simp only [pairEdges_fst_assoc]
  · simp only [Category.assoc, threeEdgeComparison_third, threeEdgePair_third]
    rw [← face_edge_eq W 0 0 (SimplexCategory.mkOfSucc (2 : Fin 3)) (by decide)]
    rw [← reassoc_of% h123, triangleProjection_last]
    simp only [pairEdges_snd_assoc]

/-- The full prescribed-vertex comparison is the actual pullback of raw face restriction. -/
theorem comparison_isPullback (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    IsPullback (comparison W w x y z) (tetrahedronProjection W w x y z)
      (pairProjection W w x y z) (rawComparison W) := by
  refine ⟨⟨comparison_projection W w x y z⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift s.snd (s.fst ≫ pairEdges W w x y z)
      (raw_fixed_edges W w x y z s.fst s.snd s.condition)) ?_ ?_ ?_⟩⟩
  · intro s
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, comparison012_assoc, face012_projection,
          pullback.lift_fst_assoc]
        have h := congrArg (fun f => f ≫ pullback.fst _ _) s.condition
        simpa only [Category.assoc, pairProjection_fst, rawComparison,
            pullback.lift_fst] using h.symm
      · simp only [Category.assoc, comparison012_assoc, face012_edges,
          pullback.lift_snd_assoc, pairEdges_fst]
    · apply pullback.hom_ext
      · simp only [Category.assoc, comparison123_assoc, face123_projection,
          pullback.lift_fst_assoc]
        have h := congrArg (fun f => f ≫ pullback.snd _ _) s.condition
        simpa only [Category.assoc, pairProjection_snd, rawComparison,
            pullback.lift_snd] using h.symm
      · apply prod.hom_ext
        · simp only [Category.assoc, comparison123_assoc, face123_first,
            pullback.lift_snd_assoc, pairEdges_fst_assoc]
          simpa only [Category.assoc] using
            congrArg (fun f => s.fst ≫ f) (pair_central W w x y z)
        · simp only [Category.assoc, comparison123_assoc, face123_last,
            pullback.lift_snd_assoc, pairEdges_snd]
  · intro s
    exact pullback.lift_fst _ _ _
  · intro s m hm hn
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst] using hn
    · simpa only [Category.assoc, comparison_edges, pullback.lift_snd] using
        congrArg (fun f => f ≫ pairEdges W w x y z) hm

/-- Reedy fibrancy alone makes the original raw adjacent restriction a Kan fibration. -/
theorem rawComparison_fibration (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → fibrations SSet.{u} (rawComparison W) := by
  let : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  intro hW
  let : Mono (SSet.simplicialSpaceDiscrete.map faceUnion.ι) := by
    rw [NatTrans.mono_iff_mono_app]
    intro m
    rw [NatTrans.mono_iff_mono_app]
    intro j
    change Mono (faceUnion.ι.app m)
    have hi : Mono faceUnion.ι := inferInstance
    rw [NatTrans.mono_iff_mono_app] at hi
    exact hi m
  let i := ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map faceUnion.ι)
  have hi : cofibrations SimplicialSpace.{u} i :=
    (HomotopicalAlgebra.cofibration_iff i).mp ((ReedyModel.cofibration_iff i).mpr inferInstance)
  have hf := ReedyModel.inner_precomp_fibration i W hi hW
  change fibrations SSet.{u} ((discreteSourceMapping W).map faceUnion.ι.op) at hf
  let : Fibration ((discreteSourceMapping W).map faceUnion.ι.op) :=
    (HomotopicalAlgebra.fibration_iff _).mpr hf
  rw [rawComparison_eq_restriction]
  exact (HomotopicalAlgebra.fibration_iff _).mp inferInstance

/-- Reedy fibrancy alone makes the full original fixed-vertex comparison a Kan fibration. -/
theorem comparison_fibration (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → fibrations SSet.{u} (comparison W w x y z) := by
  let : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  intro hW
  exact MorphismProperty.of_isPullback (comparison_isPullback W w x y z).flip
    (rawComparison_fibration W hW)


/-- The full triple comparison is the actual pullback of the degree-three Segal map. -/
theorem tetrahedronEdges_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    trivialFibrations SSet.{u} (tetrahedronEdges W w x y z) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _)
    (threeEdgeComparison_trivialFibration W hW)

/-- The compatible pair-to-triple comparison is trivial by lifting BOTH original triangles. -/
theorem pairEdges_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    trivialFibrations SSet.{u} (pairEdges W w x y z) := by
  rw [← cofibrations_rlp]
  intro A B i hi
  have h012 := (triangleComparison_trivialFibration W hW w x y)
  have h123 := (triangleComparison_trivialFibration W hW x y z)
  rw [← cofibrations_rlp] at h012 h123
  let : HasLiftingProperty i (triangleComparison W w x y) := h012 i hi
  let : HasLiftingProperty i (triangleComparison W x y z) := h123 i hi
  refine ⟨fun {a b} sq => ?_⟩
  let sq012 : CommSq (a ≫ pair012 W w x y z) i (triangleComparison W w x y)
      (b ≫ prod.fst) := ⟨by
    simpa only [Category.assoc, pairEdges_fst] using
      congrArg (fun f => f ≫ prod.fst) sq.w⟩
  let sq123 : CommSq (a ≫ pair123 W w x y z) i (triangleComparison W x y z)
      (prod.lift (b ≫ prod.fst ≫ prod.snd) (b ≫ prod.snd)) := ⟨by
    apply prod.hom_ext
    · have h := congrArg (fun f => f ≫ prod.fst ≫ prod.snd) sq.w
      simp only [Category.assoc, pairEdges_fst_assoc] at h
      calc
        _ = a ≫ pair012 W w x y z ≫ triangleComparison W w x y ≫ prod.snd := by
          simpa only [Category.assoc] using
            (congrArg (fun f => a ≫ f) (pair_central W w x y z)).symm
        _ = _ := by simpa only [Category.assoc, prod.lift_fst] using h
    · simpa only [Category.assoc, pairEdges_snd, prod.lift_snd] using
        congrArg (fun f => f ≫ prod.snd) sq.w⟩
  have hc : sq012.lift ≫ triangleComparison W w x y ≫ prod.snd =
      sq123.lift ≫ triangleComparison W x y z ≫ prod.fst := by
    rw [← Category.assoc, sq012.fac_right, ← Category.assoc, sq123.fac_right, prod.lift_fst,
      Category.assoc]
  refine CommSq.HasLift.mk' ⟨pullback.lift sq012.lift sq123.lift hc, ?_, ?_⟩
  · apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, sq012.fac_left,
          sq123.fac_left]
  · apply prod.hom_ext
    · simp only [Category.assoc, pairEdges_fst, pullback.lift_fst_assoc, sq012.fac_right]
    · simp only [Category.assoc, pairEdges_snd, pullback.lift_snd_assoc,
        sq123.fac_right_assoc, prod.lift_snd]

/-- The original adjacent-triangle comparison is a trivial fibration for a Segal space. -/
theorem comparison_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    trivialFibrations SSet.{u} (comparison W w x y z) := by
  have hf := comparison_fibration W w x y z hW.1
  have hp := (pairEdges_trivialFibration W hW w x y z).2
  have ht := (tetrahedronEdges_trivialFibration W hW w x y z).2
  have hw : weakEquivalences SSet.{u} (comparison W w x y z) :=
    (weakEquivalences SSet.{u}).of_postcomp (comparison W w x y z) (pairEdges W w x y z)
      hp (by simpa only [comparison_edges] using ht)
  exact ⟨hf, hw⟩


section Transport
variable {W V : SimplicialSpace.{u}} (f : W ⟶ V)
  {w x y z : (W.diagram _⦋0⦌) _⦋0⦌} {w' x' y' z' : (V.diagram _⦋0⦌) _⦋0⦌}

/-- The actual mapping-fibre triple map for every explicitly moved vertex. -/
def tripleMap (hw : mappingVertexMap f w = w') (hx : mappingVertexMap f x = x')
    (hy : mappingVertexMap f y = y') (hz : mappingVertexMap f z = z') :
    (mappingFibre W w x ⨯ mappingFibre W x y) ⨯ mappingFibre W y z ⟶
      (mappingFibre V w' x' ⨯ mappingFibre V x' y') ⨯ mappingFibre V y' z' :=
  prod.map (prod.map (mappingFibre.map f hw hx) (mappingFibre.map f hx hy))
    (mappingFibre.map f hy hz)

/-- The original raw triangle transport retains its whole W2 simplex and both moved fibres. -/
def triangleMap (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y')
    (hz : mappingVertexMap f z = z') : triangleSpace W x y z ⟶ triangleSpace V x' y' z' :=
  pullback.lift (triangleProjection W x y z ≫ f.hom.app (op ⦋2⦌))
    (triangleComparison W x y z ≫ prod.map (mappingFibre.map f hx hy) (mappingFibre.map f hy hz))
    (by
      apply pullback.hom_ext
      · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst,
          prod.map_fst_assoc, mappingFibre.map_fst]
        rw [← SimplicialObject.δ_naturality f.hom (2 : Fin 3), triangleProjection_first_assoc]
      · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd,
          prod.map_snd_assoc, mappingFibre.map_fst]
        rw [← SimplicialObject.δ_naturality f.hom (0 : Fin 3), triangleProjection_last_assoc])

/-- The triangle transport retains the original W2 target-map equation. -/
@[reassoc (attr := simp)]
theorem triangleMap_projection (hx : mappingVertexMap f x = x')
    (hy : mappingVertexMap f y = y') (hz : mappingVertexMap f z = z') :
    triangleMap f hx hy hz ≫ triangleProjection V x' y' z' =
      triangleProjection W x y z ≫ f.hom.app (op ⦋2⦌) := pullback.lift_fst _ _ _

/-- The triangle transport retains both original mapping-fibre target-map equations. -/
@[reassoc (attr := simp)]
theorem triangleMap_edges (hx : mappingVertexMap f x = x')
    (hy : mappingVertexMap f y = y') (hz : mappingVertexMap f z = z') :
    triangleMap f hx hy hz ≫ triangleComparison V x' y' z' =
      triangleComparison W x y z ≫
        prod.map (mappingFibre.map f hx hy) (mappingFibre.map f hy hz) := pullback.lift_snd _ _ _

/-- The whole original tetrahedron transports its W3 simplex and all three moved fibres. -/
def tetrahedronMap (hw : mappingVertexMap f w = w') (hx : mappingVertexMap f x = x')
    (hy : mappingVertexMap f y = y') (hz : mappingVertexMap f z = z') :
    tetrahedron W w x y z ⟶ tetrahedron V w' x' y' z' :=
  pullback.lift (tetrahedronProjection W w x y z ≫ f.hom.app (op ⦋3⦌))
    (tetrahedronEdges W w x y z ≫ tripleMap f hw hx hy hz) (by
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, threeEdgeComparison_first, threeEdgePair_first,
            tripleMap, prod.map_fst_assoc, mappingFibre.map_fst]
          rw [← f.hom.naturality, tetrahedron_first_assoc]
        · simp only [Category.assoc, threeEdgeComparison_second, threeEdgePair_second,
            tripleMap, prod.map_fst_assoc, prod.map_snd_assoc, mappingFibre.map_fst]
          rw [← f.hom.naturality, tetrahedron_second_assoc]
      · simp only [Category.assoc, threeEdgeComparison_third, threeEdgePair_third,
          tripleMap, prod.map_snd_assoc, mappingFibre.map_fst]
        rw [← f.hom.naturality, tetrahedron_third_assoc])

/-- The tetrahedron transport retains the entire original W3 target-map square. -/
@[reassoc (attr := simp)]
theorem tetrahedronMap_projection (hw : mappingVertexMap f w = w')
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y')
    (hz : mappingVertexMap f z = z') :
    tetrahedronMap f hw hx hy hz ≫ tetrahedronProjection V w' x' y' z' =
      tetrahedronProjection W w x y z ≫ f.hom.app (op ⦋3⦌) := pullback.lift_fst _ _ _

/-- The tetrahedron transport retains its SAME entire prescribed triple. -/
@[reassoc (attr := simp)]
theorem tetrahedronMap_edges (hw : mappingVertexMap f w = w')
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y')
    (hz : mappingVertexMap f z = z') :
    tetrahedronMap f hw hx hy hz ≫ tetrahedronEdges V w' x' y' z' =
      tetrahedronEdges W w x y z ≫ tripleMap f hw hx hy hz := pullback.lift_snd _ _ _

/-- The whole compatible pair transports both original triangles with the SAME central map. -/
def pairMap (hw : mappingVertexMap f w = w') (hx : mappingVertexMap f x = x')
    (hy : mappingVertexMap f y = y') (hz : mappingVertexMap f z = z') :
    pair W w x y z ⟶ pair V w' x' y' z' :=
  pullback.lift (pair012 W w x y z ≫ triangleMap f hw hx hy)
    (pair123 W w x y z ≫ triangleMap f hx hy hz) (by
      simp only [Category.assoc, triangleMap_edges_assoc, prod.map_fst, prod.map_snd]
      exact congrArg (fun k => k ≫ mappingFibre.map f hx hy) (pair_central W w x y z))

/-- Pair transport retains the original012 triangle map. -/
@[reassoc (attr := simp)]
theorem pairMap012 (hw : mappingVertexMap f w = w')
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y')
    (hz : mappingVertexMap f z = z') :
    pairMap f hw hx hy hz ≫ pair012 V w' x' y' z' =
      pair012 W w x y z ≫ triangleMap f hw hx hy := pullback.lift_fst _ _ _

/-- Pair transport retains the original123 triangle map. -/
@[reassoc (attr := simp)]
theorem pairMap123 (hw : mappingVertexMap f w = w')
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y')
    (hz : mappingVertexMap f z = z') :
    pairMap f hw hx hy hz ≫ pair123 V w' x' y' z' =
      pair123 W w x y z ≫ triangleMap f hx hy hz := pullback.lift_snd _ _ _

/-- The whole triple projection obeys the original strict target-map naturality square. -/
@[reassoc]
theorem pairMap_edges (hw : mappingVertexMap f w = w')
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y')
    (hz : mappingVertexMap f z = z') :
    pairMap f hw hx hy hz ≫ pairEdges V w' x' y' z' =
      pairEdges W w x y z ≫ tripleMap f hw hx hy hz := by
  apply prod.hom_ext
  · simp only [Category.assoc, pairEdges_fst, pairMap012_assoc, triangleMap_edges,
      tripleMap, prod.map_fst, pairEdges_fst_assoc]
  · simp only [Category.assoc, pairEdges_snd, pairMap123_assoc, triangleMap_edges_assoc,
      prod.map_snd, tripleMap, pairEdges_snd_assoc]

/-- The literal012 face commutes with every original map and explicitly moved vertices. -/
@[reassoc]
theorem face012_naturality (hw : mappingVertexMap f w = w')
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y')
    (hz : mappingVertexMap f z = z') :
    tetrahedronMap f hw hx hy hz ≫ face012 V w' x' y' z' =
      face012 W w x y z ≫ triangleMap f hw hx hy := by
  apply pullback.hom_ext
  · simp only [Category.assoc, face012_projection, tetrahedronMap_projection_assoc,
      triangleMap_projection, face012_projection_assoc]
    rw [SimplicialObject.δ_naturality f.hom (3 : Fin 4)]
  · simp only [Category.assoc, face012_edges, tetrahedronMap_edges_assoc, tripleMap,
      prod.map_fst, triangleMap_edges, face012_edges_assoc]

/-- The literal123 face commutes with every original map and explicitly moved vertices. -/
@[reassoc]
theorem face123_naturality (hw : mappingVertexMap f w = w')
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y')
    (hz : mappingVertexMap f z = z') :
    tetrahedronMap f hw hx hy hz ≫ face123 V w' x' y' z' =
      face123 W w x y z ≫ triangleMap f hx hy hz := by
  apply pullback.hom_ext
  · simp only [Category.assoc, face123_projection, tetrahedronMap_projection_assoc,
      triangleMap_projection, face123_projection_assoc]
    rw [SimplicialObject.δ_naturality f.hom (0 : Fin 4)]
  · apply prod.hom_ext
    · simp only [Category.assoc, face123_first, tetrahedronMap_edges_assoc, tripleMap,
        prod.map_fst_assoc, prod.map_snd, triangleMap_edges_assoc, prod.map_fst,
        face123_first_assoc]
    · simp only [Category.assoc, face123_last, tetrahedronMap_edges_assoc, tripleMap,
        prod.map_snd, triangleMap_edges_assoc, face123_last_assoc]

/-- The whole adjacent comparison has the original strict naturality square. -/
@[reassoc]
theorem comparison_naturality (hw : mappingVertexMap f w = w')
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y')
    (hz : mappingVertexMap f z = z') :
    tetrahedronMap f hw hx hy hz ≫ comparison V w' x' y' z' =
      comparison W w x y z ≫ pairMap f hw hx hy hz := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, comparison012, comparison123, pairMap012, pairMap123,
      comparison012_assoc, comparison123_assoc, face012_naturality, face123_naturality]

end Transport

end SimplicialSpace.AdjacentTriangle
