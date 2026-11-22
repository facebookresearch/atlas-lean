/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalSpaces
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalHomotopyCategory
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Tactic.FinCases

/-!
# The original outer-horn mapping fork

The horn is the union of edges02 and01, with their common source vertex0.
Actual inner mapping takes the native union pushout to its original pullback.
All constructions are on the original simplicial space, without a fibrancy
or Segal hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial SimplicialSpace.Inner

namespace SSet.Rezk

/-- The original source vertex of the two outer-horn edges. -/
abbrev outerHornVertex : (Δ[2] : SSet.{u}).Subcomplex := stdSimplex.face {1, 2}ᶜ

/-- The first original edge of the fork is edge02. -/
abbrev outerHornLeftFace : (Δ[2] : SSet.{u}).Subcomplex := stdSimplex.face {1}ᶜ

/-- The second original edge of the fork is edge01. -/
abbrev outerHornRightFace : (Δ[2] : SSet.{u}).Subcomplex := stdSimplex.face {2}ᶜ

/-- The native vertex face is exactly the original vertex0. -/
theorem outerHornVertex_eq : outerHornVertex.{u} = stdSimplex.face {0} := by
  congr 1

/-- The literal outer horn is precisely the original edges02 and01. -/
theorem outerHorn_union :
    outerHornLeftFace.{u} ⊔ outerHornRightFace = horn 2 (0 : Fin 3) := by
  rw [horn_eq_iSup]
  apply le_antisymm
  · exact sup_le
      (le_iSup (fun j : ({(0 : Fin 3)}ᶜ : Set (Fin 3)) => stdSimplex.face {j.1}ᶜ)
        ⟨1, by decide⟩)
      (le_iSup (fun j : ({(0 : Fin 3)}ᶜ : Set (Fin 3)) => stdSimplex.face {j.1}ᶜ)
        ⟨2, by decide⟩)
  · apply iSup_le
    rintro ⟨j, hj⟩
    fin_cases j
    · simp at hj
    · exact le_sup_left
    · exact le_sup_right

/-- Both original edges intersect exactly in their original source vertex. -/
theorem outerHorn_intersection :
    outerHornLeftFace.{u} ⊓ outerHornRightFace = outerHornVertex := by
  rw [stdSimplex.face_inter_face]
  congr 1

/-- The original vertex inclusion into edge02. -/
def outerHornVertexLeft : (outerHornVertex.{u} : SSet.{u}) ⟶ outerHornLeftFace :=
  Subcomplex.homOfLE (by rw [← outerHorn_intersection]; exact inf_le_left)

/-- The original vertex inclusion into edge01. -/
def outerHornVertexRight : (outerHornVertex.{u} : SSet.{u}) ⟶ outerHornRightFace :=
  Subcomplex.homOfLE (by rw [← outerHorn_intersection]; exact inf_le_right)

/-- The original edge02 inclusion into the outer horn. -/
def outerHornLeft : (outerHornLeftFace.{u} : SSet.{u}) ⟶ (Λ[2, 0] : SSet.{u}) :=
  Subcomplex.homOfLE (by rw [← outerHorn_union]; exact le_sup_left)

/-- The original edge01 inclusion into the outer horn. -/
def outerHornRight : (outerHornRightFace.{u} : SSet.{u}) ⟶ (Λ[2, 0] : SSet.{u}) :=
  Subcomplex.homOfLE (by rw [← outerHorn_union]; exact le_sup_right)

@[reassoc (attr := simp)]
theorem outerHornVertexLeft_ι :
    outerHornVertexLeft.{u} ≫ outerHornLeftFace.ι = outerHornVertex.ι := rfl

@[reassoc (attr := simp)]
theorem outerHornVertexRight_ι :
    outerHornVertexRight.{u} ≫ outerHornRightFace.ι = outerHornVertex.ι := rfl

@[reassoc (attr := simp)]
theorem outerHornLeft_ι : outerHornLeft.{u} ≫ (horn 2 (0 : Fin 3)).ι =
    outerHornLeftFace.ι := rfl

@[reassoc (attr := simp)]
theorem outerHornRight_ι : outerHornRight.{u} ≫ (horn 2 (0 : Fin 3)).ι =
    outerHornRightFace.ι := rfl

/-- The same original four inclusions form a native union pushout. -/
theorem outerHorn_isPushout :
    IsPushout outerHornVertexLeft.{u} outerHornVertexRight outerHornLeft outerHornRight := by
  let sq : Subcomplex.BicartSq outerHornVertex.{u} outerHornLeftFace
      outerHornRightFace (horn 2 (0 : Fin 3)) :=
    { sup_eq := outerHorn_union, inf_eq := outerHorn_intersection }
  exact sq.isPushout

/-- The native represented point of the common original source vertex. -/
def outerHornVertexIso : (Δ[0] : SSet.{u}) ≅ outerHornVertex :=
  stdSimplex.facePairComplIso (1 : Fin 3) 2 (by decide)

/-- The represented first edge is the original edge02. -/
def outerHornLeftIso : (Δ[1] : SSet.{u}) ≅ outerHornLeftFace :=
  stdSimplex.faceSingletonComplIso (1 : Fin 3)

/-- The represented second edge is the original edge01. -/
def outerHornRightIso : (Δ[1] : SSet.{u}) ≅ outerHornRightFace :=
  stdSimplex.faceSingletonComplIso (2 : Fin 3)

@[reassoc (attr := simp)]
theorem outerHornLeftIso_ι : outerHornLeftIso.{u}.hom ≫ outerHornLeftFace.ι =
    stdSimplex.δ (1 : Fin 3) := rfl

@[reassoc (attr := simp)]
theorem outerHornRightIso_ι : outerHornRightIso.{u}.hom ≫ outerHornRightFace.ι =
    stdSimplex.δ (2 : Fin 3) := rfl

/-- The original point enters edge02 at its source vertex. -/
@[reassoc (attr := simp)]
theorem outerHornVertexLeft_eq : outerHornVertexIso.{u}.hom ≫ outerHornVertexLeft =
    stdSimplex.δ (1 : Fin 2) ≫ outerHornLeftIso.hom := by
  apply (cancel_mono outerHornLeftFace.ι).mp
  rw [Category.assoc, outerHornVertexLeft_ι, Category.assoc, outerHornLeftIso_ι]
  exact stdSimplex.facePairComplIso_hom_ι' (1 : Fin 3) 2 (by decide)

/-- The same original point enters edge01 at its source vertex. -/
@[reassoc (attr := simp)]
theorem outerHornVertexRight_eq : outerHornVertexIso.{u}.hom ≫ outerHornVertexRight =
    stdSimplex.δ (1 : Fin 2) ≫ outerHornRightIso.hom := by
  apply (cancel_mono outerHornRightFace.ι).mp
  rw [Category.assoc, outerHornVertexRight_ι, Category.assoc, outerHornRightIso_ι]
  exact stdSimplex.facePairComplIso_hom_ι (1 : Fin 3) 2 (by decide)

end SSet.Rezk

namespace SimplicialSpace

private theorem discretePreservesPushouts :
    PreservesColimitsOfShape WalkingSpan SSet.simplicialSpaceDiscrete.{u} :=
  ⟨fun {K} => ⟨fun c {hc} => ⟨by
    apply evaluationJointlyReflectsColimits _ (fun k => ?_)
    change IsColimit
      ((((evaluation _ _).obj k ⋙ SimplicialObject.const (Type u)).mapCocone c))
    exact isColimitOfPreserves _ hc⟩⟩⟩

private theorem innerMappingPreservesPullbacks (W : SimplicialSpace.{u}) :
    PreservesLimitsOfShape WalkingCospan (innerHomFunctor.flip.obj W) := by
  let : ∀ K : SSet.{u}, PreservesColimitsOfShape WalkingCospanᵒᵖ
      (innerTensorBifunctor.flip.obj K) := fun K => by
    change PreservesColimitsOfShape WalkingCospanᵒᵖ (innerTensor K)
    let : (innerTensor K).IsLeftAdjoint :=
      (innerTensorCotensorAdjunction K).isLeftAdjoint
    infer_instance
  exact innerTensorHomAdjunction₂.preservesLimitsOfShape_flip_obj WalkingCospan W

/-- Actual inner mapping sends the same original outer-horn pushout to its pullback. -/
theorem outerHornMapping_isPullback (W : SimplicialSpace.{u}) :
    IsPullback
      ((discreteSourceMapping W).map SSet.Rezk.outerHornLeft.{u}.op)
      ((discreteSourceMapping W).map SSet.Rezk.outerHornRight.{u}.op)
      ((discreteSourceMapping W).map SSet.Rezk.outerHornVertexLeft.{u}.op)
      ((discreteSourceMapping W).map SSet.Rezk.outerHornVertexRight.{u}.op) := by
  let := discretePreservesPushouts.{u}
  let := innerMappingPreservesPullbacks W
  have sq := ((SSet.Rezk.outerHorn_isPushout.{u}).map
    SSet.simplicialSpaceDiscrete).map ofSimplicialObject
  exact (sq.op.map (innerHomFunctor.flip.obj W)).flip

/-- The original partial matching fork has common source0, ordered edges02 and01. -/
abbrev outerHornFork (W : SimplicialSpace.{u}) : SSet.{u} :=
  pullback (W.diagram.δ (1 : Fin 2)) (W.diagram.δ (1 : Fin 2))

/-- The actual original degree-two comparison records middle02 and first01. -/
def outerHornComparison (W : SimplicialSpace.{u}) : W.diagram _⦋2⦌ ⟶ outerHornFork W :=
  pullback.lift (W.diagram.δ (1 : Fin 3)) (W.diagram.δ (2 : Fin 3)) (by
    change W.diagram.map (SimplexCategory.δ (1 : Fin 3)).op ≫
        W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op =
      W.diagram.map (SimplexCategory.δ (2 : Fin 3)).op ≫
        W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op
    have h : SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3) =
        SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3) := by decide
    simpa only [Functor.map_comp, op_comp] using
      congrArg (fun t => W.diagram.map t.op) h)

@[reassoc (attr := simp)]
theorem outerHornComparison_fst (W : SimplicialSpace.{u}) :
    outerHornComparison W ≫ pullback.fst _ _ = W.diagram.δ (1 : Fin 3) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem outerHornComparison_snd (W : SimplicialSpace.{u}) :
    outerHornComparison W ≫ pullback.snd _ _ = W.diagram.δ (2 : Fin 3) :=
  pullback.lift_snd _ _ _

/-- The point corner of the actual mapped outer-horn square is the original W₀. -/
def outerHornVertexMappingIso (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).obj (op (SSet.Rezk.outerHornVertex.{u} : SSet.{u})) ≅
      W.diagram _⦋0⦌ :=
  (discreteSourceMapping W).mapIso SSet.Rezk.outerHornVertexIso.{u}.op ≪≫
    discreteYonedaIso W 0

/-- The first mapped edge is the original W₁ on edge02. -/
def outerHornLeftMappingIso (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).obj (op (SSet.Rezk.outerHornLeftFace.{u} : SSet.{u})) ≅
      W.diagram _⦋1⦌ :=
  (discreteSourceMapping W).mapIso SSet.Rezk.outerHornLeftIso.{u}.op ≪≫
    discreteYonedaIso W 1

/-- The second mapped edge is the original W₁ on edge01. -/
def outerHornRightMappingIso (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).obj (op (SSet.Rezk.outerHornRightFace.{u} : SSet.{u})) ≅
      W.diagram _⦋1⦌ :=
  (discreteSourceMapping W).mapIso SSet.Rezk.outerHornRightIso.{u}.op ≪≫
    discreteYonedaIso W 1

/-- The first mapped vertex inclusion is the same original source map d₁. -/
@[reassoc (attr := simp)]
theorem outerHornLeftMapping_source (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).map SSet.Rezk.outerHornVertexLeft.{u}.op ≫
        (outerHornVertexMappingIso W).hom =
      (outerHornLeftMappingIso W).hom ≫ W.diagram.δ (1 : Fin 2) := by
  change (discreteSourceMapping W).map SSet.Rezk.outerHornVertexLeft.op ≫
      ((discreteSourceMapping W).map SSet.Rezk.outerHornVertexIso.hom.op ≫
        (discreteYonedaIso W 0).hom) =
    ((discreteSourceMapping W).map SSet.Rezk.outerHornLeftIso.hom.op ≫
      (discreteYonedaIso W 1).hom) ≫ W.diagram.δ (1 : Fin 2)
  have hY := discreteYonedaIso_naturality_index W (SimplexCategory.δ (1 : Fin 2))
  change (discreteSourceMapping W).map (SSet.stdSimplex.δ (1 : Fin 2)).op ≫
      (discreteYonedaIso W 0).hom =
    (discreteYonedaIso W 1).hom ≫ W.diagram.δ (1 : Fin 2) at hY
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp,
    SSet.Rezk.outerHornVertexLeft_eq, op_comp, Functor.map_comp, Category.assoc,
    hY, Category.assoc]

/-- The second mapped vertex inclusion is the same original source map d₁. -/
@[reassoc (attr := simp)]
theorem outerHornRightMapping_source (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).map SSet.Rezk.outerHornVertexRight.{u}.op ≫
        (outerHornVertexMappingIso W).hom =
      (outerHornRightMappingIso W).hom ≫ W.diagram.δ (1 : Fin 2) := by
  change (discreteSourceMapping W).map SSet.Rezk.outerHornVertexRight.op ≫
      ((discreteSourceMapping W).map SSet.Rezk.outerHornVertexIso.hom.op ≫
        (discreteYonedaIso W 0).hom) =
    ((discreteSourceMapping W).map SSet.Rezk.outerHornRightIso.hom.op ≫
      (discreteYonedaIso W 1).hom) ≫ W.diagram.δ (1 : Fin 2)
  have hY := discreteYonedaIso_naturality_index W (SimplexCategory.δ (1 : Fin 2))
  change (discreteSourceMapping W).map (SSet.stdSimplex.δ (1 : Fin 2)).op ≫
      (discreteYonedaIso W 0).hom =
    (discreteYonedaIso W 1).hom ≫ W.diagram.δ (1 : Fin 2) at hY
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp,
    SSet.Rezk.outerHornVertexRight_eq, op_comp, Functor.map_comp, Category.assoc,
    hY, Category.assoc]

private theorem outerHornSource_condition (W : SimplicialSpace.{u}) :
    ((discreteSourceMapping W).map SSet.Rezk.outerHornLeft.op ≫
      (outerHornLeftMappingIso W).hom) ≫ W.diagram.δ (1 : Fin 2) =
    ((discreteSourceMapping W).map SSet.Rezk.outerHornRight.op ≫
      (outerHornRightMappingIso W).hom) ≫ W.diagram.δ (1 : Fin 2) := by
  rw [Category.assoc, ← outerHornLeftMapping_source, ← Category.assoc,
    (outerHornMapping_isPullback W).w, Category.assoc, outerHornRightMapping_source,
    ← Category.assoc]

private def outerHornMapToFork (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).obj (op (Λ[2, 0] : SSet.{u})) ⟶ outerHornFork W :=
  pullback.lift
    ((discreteSourceMapping W).map SSet.Rezk.outerHornLeft.op ≫
      (outerHornLeftMappingIso W).hom)
    ((discreteSourceMapping W).map SSet.Rezk.outerHornRight.op ≫
      (outerHornRightMappingIso W).hom) (outerHornSource_condition W)

@[reassoc (attr := simp)]
private theorem outerHornMapToFork_fst (W : SimplicialSpace.{u}) :
    outerHornMapToFork W ≫ pullback.fst _ _ =
      (discreteSourceMapping W).map SSet.Rezk.outerHornLeft.op ≫
        (outerHornLeftMappingIso W).hom := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem outerHornMapToFork_snd (W : SimplicialSpace.{u}) :
    outerHornMapToFork W ≫ pullback.snd _ _ =
      (discreteSourceMapping W).map SSet.Rezk.outerHornRight.op ≫
        (outerHornRightMappingIso W).hom := pullback.lift_snd _ _ _

private theorem inverseIsoSquare {A B A' B' : SSet.{u}}
    (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : f ≫ eB.hom = eA.hom ≫ g) : eA.inv ≫ f = g ≫ eB.inv := by
  apply (cancel_mono eB.hom).mp
  simp only [Category.assoc, h, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

private theorem outerHornInverse_condition (W : SimplicialSpace.{u}) :
    (pullback.fst (W.diagram.δ (1 : Fin 2)) (W.diagram.δ (1 : Fin 2)) ≫
        (outerHornLeftMappingIso W).inv) ≫
      (discreteSourceMapping W).map SSet.Rezk.outerHornVertexLeft.op =
    (pullback.snd (W.diagram.δ (1 : Fin 2)) (W.diagram.δ (1 : Fin 2)) ≫
        (outerHornRightMappingIso W).inv) ≫
      (discreteSourceMapping W).map SSet.Rezk.outerHornVertexRight.op := by
  rw [Category.assoc, inverseIsoSquare _ _ _ _ (outerHornLeftMapping_source W),
    ← Category.assoc, pullback.condition, Category.assoc,
    ← inverseIsoSquare _ _ _ _ (outerHornRightMapping_source W), ← Category.assoc]

private def outerHornMapFromFork (W : SimplicialSpace.{u}) :
    outerHornFork W ⟶ (discreteSourceMapping W).obj (op (Λ[2, 0] : SSet.{u})) :=
  (outerHornMapping_isPullback W).lift
    (pullback.fst _ _ ≫ (outerHornLeftMappingIso W).inv)
    (pullback.snd _ _ ≫ (outerHornRightMappingIso W).inv)
    (outerHornInverse_condition W)

@[reassoc (attr := simp)]
private theorem outerHornMapFromFork_left (W : SimplicialSpace.{u}) :
    outerHornMapFromFork W ≫ (discreteSourceMapping W).map SSet.Rezk.outerHornLeft.op =
      pullback.fst _ _ ≫ (outerHornLeftMappingIso W).inv :=
  (outerHornMapping_isPullback W).lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem outerHornMapFromFork_right (W : SimplicialSpace.{u}) :
    outerHornMapFromFork W ≫ (discreteSourceMapping W).map SSet.Rezk.outerHornRight.op =
      pullback.snd _ _ ≫ (outerHornRightMappingIso W).inv :=
  (outerHornMapping_isPullback W).lift_snd _ _ _

/-- The actual outer-horn mapping object is its original source0 fork, for ANY W. -/
def outerHornMappingIso (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).obj (op (Λ[2, 0] : SSet.{u})) ≅ outerHornFork W where
  hom := outerHornMapToFork W
  inv := outerHornMapFromFork W
  hom_inv_id := by
    apply (outerHornMapping_isPullback W).hom_ext
    · simp only [Category.assoc, outerHornMapFromFork_left,
        outerHornMapToFork_fst_assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, outerHornMapFromFork_right,
        outerHornMapToFork_snd_assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, outerHornMapToFork_fst,
        outerHornMapFromFork_left_assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, outerHornMapToFork_snd,
        outerHornMapFromFork_right_assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- The first projection keeps the original edge02 restriction. -/
@[reassoc (attr := simp)]
theorem outerHornMappingIso_fst (W : SimplicialSpace.{u}) :
    (outerHornMappingIso W).hom ≫ pullback.fst _ _ =
      (discreteSourceMapping W).map SSet.Rezk.outerHornLeft.op ≫
        (outerHornLeftMappingIso W).hom := outerHornMapToFork_fst W

/-- The second projection keeps the original edge01 restriction. -/
@[reassoc (attr := simp)]
theorem outerHornMappingIso_snd (W : SimplicialSpace.{u}) :
    (outerHornMappingIso W).hom ≫ pullback.snd _ _ =
      (discreteSourceMapping W).map SSet.Rezk.outerHornRight.op ≫
        (outerHornRightMappingIso W).hom := outerHornMapToFork_snd W

/-- The inverse has the original edge02 projection with its original represented-face map. -/
@[reassoc (attr := simp)]
theorem outerHornMappingIso_inv_left (W : SimplicialSpace.{u}) :
    (outerHornMappingIso W).inv ≫
      (discreteSourceMapping W).map SSet.Rezk.outerHornLeft.op =
        pullback.fst _ _ ≫ (outerHornLeftMappingIso W).inv := outerHornMapFromFork_left W

/-- The inverse has the original edge01 projection with its original represented-face map. -/
@[reassoc (attr := simp)]
theorem outerHornMappingIso_inv_right (W : SimplicialSpace.{u}) :
    (outerHornMappingIso W).inv ≫
      (discreteSourceMapping W).map SSet.Rezk.outerHornRight.op =
        pullback.snd _ _ ≫ (outerHornRightMappingIso W).inv := outerHornMapFromFork_right W

private theorem outerHornFaceNormalization (W : SimplicialSpace.{u})
    {A : SSet.{u}} (i : A ⟶ (Δ[2] : SSet.{u})) (j : (Δ[1] : SSet.{u}) ⟶ A)
    (k : Fin 3) (h : j ≫ i = SSet.stdSimplex.δ k) :
    (discreteYonedaIso W 2).inv ≫ (discreteSourceMapping W).map i.op ≫
      (discreteSourceMapping W).map j.op ≫ (discreteYonedaIso W 1).hom =
        W.diagram.δ k := by
  have hm : (discreteSourceMapping W).map i.op ≫ (discreteSourceMapping W).map j.op =
      (discreteSourceMapping W).map (SSet.stdSimplex.δ k).op := by
    rw [← Functor.map_comp, ← op_comp, h]
  have hy := discreteYonedaIso_naturality_index W (SimplexCategory.δ k)
  change (discreteSourceMapping W).map (SSet.stdSimplex.δ k).op ≫
      (discreteYonedaIso W 1).hom =
    (discreteYonedaIso W 2).hom ≫ W.diagram.δ k at hy
  calc
    _ = (discreteYonedaIso W 2).inv ≫
        ((discreteSourceMapping W).map i.op ≫ (discreteSourceMapping W).map j.op) ≫
          (discreteYonedaIso W 1).hom := by simp only [Category.assoc]
    _ = (discreteYonedaIso W 2).inv ≫
        (discreteSourceMapping W).map (SSet.stdSimplex.δ k).op ≫
          (discreteYonedaIso W 1).hom := by rw [hm]
    _ = _ := by rw [hy, Iso.inv_hom_id_assoc]

/-- The same original horn restriction normalizes to the actual original W₂ fork map. -/
@[reassoc (attr := simp)]
theorem outerHornMappingIso_normalization (W : SimplicialSpace.{u}) :
    (discreteYonedaIso W 2).inv ≫
      (discreteSourceMapping W).map (SSet.horn 2 (0 : Fin 3)).ι.op ≫
        (outerHornMappingIso W).hom = outerHornComparison W := by
  apply pullback.hom_ext
  · simp only [Category.assoc, outerHornMappingIso_fst, outerHornComparison_fst]
    change (discreteYonedaIso W 2).inv ≫
      (discreteSourceMapping W).map (SSet.horn 2 (0 : Fin 3)).ι.op ≫
      (discreteSourceMapping W).map SSet.Rezk.outerHornLeft.op ≫
      (discreteSourceMapping W).map SSet.Rezk.outerHornLeftIso.hom.op ≫
      (discreteYonedaIso W 1).hom = W.diagram.δ (1 : Fin 3)
    have hh : SSet.Rezk.outerHornLeftIso.hom ≫ SSet.Rezk.outerHornLeft ≫
        (SSet.horn 2 (0 : Fin 3)).ι = SSet.stdSimplex.δ (1 : Fin 3) := by
      rw [SSet.Rezk.outerHornLeft_ι, SSet.Rezk.outerHornLeftIso_ι]
    simpa only [op_comp, Functor.map_comp, Category.assoc] using
      outerHornFaceNormalization W (SSet.horn 2 (0 : Fin 3)).ι
        (SSet.Rezk.outerHornLeftIso.hom ≫ SSet.Rezk.outerHornLeft) 1 hh
  · simp only [Category.assoc, outerHornMappingIso_snd, outerHornComparison_snd]
    change (discreteYonedaIso W 2).inv ≫
      (discreteSourceMapping W).map (SSet.horn 2 (0 : Fin 3)).ι.op ≫
      (discreteSourceMapping W).map SSet.Rezk.outerHornRight.op ≫
      (discreteSourceMapping W).map SSet.Rezk.outerHornRightIso.hom.op ≫
      (discreteYonedaIso W 1).hom = W.diagram.δ (2 : Fin 3)
    have hh : SSet.Rezk.outerHornRightIso.hom ≫ SSet.Rezk.outerHornRight ≫
        (SSet.horn 2 (0 : Fin 3)).ι = SSet.stdSimplex.δ (2 : Fin 3) := by
      rw [SSet.Rezk.outerHornRight_ι, SSet.Rezk.outerHornRightIso_ι]
    simpa only [op_comp, Functor.map_comp, Category.assoc] using
      outerHornFaceNormalization W (SSet.horn 2 (0 : Fin 3)).ι
        (SSet.Rezk.outerHornRightIso.hom ≫ SSet.Rezk.outerHornRight) 2 hh

/-- Every original target arrow induces the original source0 fork map. -/
def outerHornForkMap {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    outerHornFork W ⟶ outerHornFork V :=
  pullback.map (W.diagram.δ (1 : Fin 2)) (W.diagram.δ (1 : Fin 2))
    (V.diagram.δ (1 : Fin 2)) (V.diagram.δ (1 : Fin 2))
    (q.hom.app (op ⦋1⦌)) (q.hom.app (op ⦋1⦌)) (q.hom.app (op ⦋0⦌))
    (q.hom.naturality (SimplexCategory.δ (1 : Fin 2)).op)
    (q.hom.naturality (SimplexCategory.δ (1 : Fin 2)).op)

@[reassoc (attr := simp)]
theorem outerHornForkMap_fst {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    outerHornForkMap q ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ q.hom.app (op ⦋1⦌) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem outerHornForkMap_snd {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    outerHornForkMap q ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ q.hom.app (op ⦋1⦌) := pullback.lift_snd _ _ _

/-- The original W₂ comparison is strictly natural at every original target map. -/
@[reassoc]
theorem outerHornComparison_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    outerHornComparison W ≫ outerHornForkMap q =
      q.hom.app (op ⦋2⦌) ≫ outerHornComparison V := by
  apply pullback.hom_ext
  · simp only [Category.assoc, outerHornForkMap_fst, outerHornComparison_fst_assoc,
      outerHornComparison_fst]
    exact q.hom.naturality (SimplexCategory.δ (1 : Fin 3)).op
  · simp only [Category.assoc, outerHornForkMap_snd, outerHornComparison_snd_assoc,
      outerHornComparison_snd]
    exact q.hom.naturality (SimplexCategory.δ (2 : Fin 3)).op

private theorem representedFaceMapping_natural {W V : SimplicialSpace.{u}}
    (q : W ⟶ V) {A : SSet.{u}} (j : (Δ[1] : SSet.{u}) ⟶ A) :
    (discreteSourceMappingMap q).app (op A) ≫
      (discreteSourceMapping V).map j.op ≫ (discreteYonedaIso V 1).hom =
    (discreteSourceMapping W).map j.op ≫ (discreteYonedaIso W 1).hom ≫
      q.hom.app (op ⦋1⦌) := by
  rw [← Category.assoc, ← (discreteSourceMappingMap q).naturality j.op,
    Category.assoc, discreteYonedaIso_naturality_target]

/-- The first represented edge corner retains the original target-map naturality. -/
@[reassoc]
theorem outerHornLeftMappingIso_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    (discreteSourceMappingMap q).app (op (SSet.Rezk.outerHornLeftFace.{u} : SSet.{u})) ≫
      (outerHornLeftMappingIso V).hom =
        (outerHornLeftMappingIso W).hom ≫ q.hom.app (op ⦋1⦌) :=
  representedFaceMapping_natural q SSet.Rezk.outerHornLeftIso.hom

/-- The second represented edge corner retains the same original target-map naturality. -/
@[reassoc]
theorem outerHornRightMappingIso_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    (discreteSourceMappingMap q).app (op (SSet.Rezk.outerHornRightFace.{u} : SSet.{u})) ≫
      (outerHornRightMappingIso V).hom =
        (outerHornRightMappingIso W).hom ≫ q.hom.app (op ⦋1⦌) :=
  representedFaceMapping_natural q SSet.Rezk.outerHornRightIso.hom

/-- The original outer-horn mapping isomorphism is strictly target natural for ANY W,V. -/
@[reassoc]
theorem outerHornMappingIso_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    (discreteSourceMappingMap q).app (op (Λ[2, 0] : SSet.{u})) ≫
      (outerHornMappingIso V).hom = (outerHornMappingIso W).hom ≫ outerHornForkMap q := by
  apply pullback.hom_ext
  · rw [Category.assoc, outerHornMappingIso_fst, ← Category.assoc,
      ← (discreteSourceMappingMap q).naturality SSet.Rezk.outerHornLeft.op,
      Category.assoc, outerHornLeftMappingIso_natural]
    simp only [Category.assoc, outerHornForkMap_fst, outerHornMappingIso_fst_assoc]
  · rw [Category.assoc, outerHornMappingIso_snd, ← Category.assoc,
      ← (discreteSourceMappingMap q).naturality SSet.Rezk.outerHornRight.op,
      Category.assoc, outerHornRightMappingIso_natural]
    simp only [Category.assoc, outerHornForkMap_snd, outerHornMappingIso_snd_assoc]

/-- Its original inverse retains the same strict target naturality square. -/
@[reassoc]
theorem outerHornMappingIso_inv_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    (outerHornMappingIso W).inv ≫
      (discreteSourceMappingMap q).app (op (Λ[2, 0] : SSet.{u})) =
      outerHornForkMap q ≫ (outerHornMappingIso V).inv :=
  inverseIsoSquare (outerHornMappingIso W) (outerHornMappingIso V) _ _
    (outerHornMappingIso_natural q)

end SimplicialSpace

namespace SimplicialSpace.SegalHomotopy

/-- The original middle/first fibre edges form a fork with common source x. -/
def triangleShearPair (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x z ⨯ mappingFibre W x y ⟶ outerHornFork W :=
  pullback.lift (prod.fst ≫ mappingFibre.fst W x z)
    (prod.snd ≫ mappingFibre.fst W x y) (by
      simp only [Category.assoc, mappingFibre.source_eq]
      have h : (prod.fst : mappingFibre W x z ⨯ mappingFibre W x y ⟶ _) ≫
          mappingFibre.snd W x z = prod.snd ≫ mappingFibre.snd W x y :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      simpa only [Category.assoc] using
        congrArg (fun t => t ≫ SSet.yonedaEquiv.symm x) h)

@[reassoc (attr := simp)]
theorem triangleShearPair_fst (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearPair W x y z ≫ pullback.fst _ _ = prod.fst ≫ mappingFibre.fst W x z :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem triangleShearPair_snd (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearPair W x y z ≫ pullback.snd _ _ = prod.snd ≫ mappingFibre.fst W x y :=
  pullback.lift_snd _ _ _

/-- The actual pullback of the original degree-two fork over the prescribed fibre pair. -/
abbrev triangleShearPullback (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  pullback (outerHornComparison W) (triangleShearPair W x y z)

/-- The original degree-two projection of this same chosen pullback. -/
abbrev triangleShearPullbackFst (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearPullback W x y z ⟶ W.diagram _⦋2⦌ :=
  pullback.fst (outerHornComparison W) (triangleShearPair W x y z)

/-- The same native pullback's prescribed middle/first fibre-pair projection. -/
abbrev triangleShearPullbackSnd (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearPullback W x y z ⟶ mappingFibre W x z ⨯ mappingFibre W x y :=
  pullback.snd (outerHornComparison W) (triangleShearPair W x y z)

@[reassoc]
theorem triangleShearPullback_condition (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearPullbackFst W x y z ≫ outerHornComparison W =
      triangleShearPullbackSnd W x y z ≫ triangleShearPair W x y z := pullback.condition

/-- The original middle02 face is the same prescribed x-to-z fibre edge. -/
@[reassoc (attr := simp)]
theorem triangleShearPullback_middle (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearPullbackFst W x y z ≫ W.diagram.δ (1 : Fin 3) =
      triangleShearPullbackSnd W x y z ≫ prod.fst ≫ mappingFibre.fst W x z := by
  have h := congrArg (fun t => t ≫ pullback.fst
    (W.diagram.δ (1 : Fin 2)) (W.diagram.δ (1 : Fin 2)))
    (triangleShearPullback_condition W x y z)
  simpa only [Category.assoc, outerHornComparison_fst, triangleShearPair_fst] using h

/-- The original first01 face is the same prescribed x-to-y fibre edge. -/
@[reassoc (attr := simp)]
theorem triangleShearPullback_first (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearPullbackFst W x y z ≫ W.diagram.δ (2 : Fin 3) =
      triangleShearPullbackSnd W x y z ≫ prod.snd ≫ mappingFibre.fst W x y := by
  have h := congrArg (fun t => t ≫ pullback.snd
    (W.diagram.δ (1 : Fin 2)) (W.diagram.δ (1 : Fin 2)))
    (triangleShearPullback_condition W x y z)
  simpa only [Category.assoc, outerHornComparison_snd, triangleShearPair_snd] using h

/-- The original shear is literally the middle02 and first01 pair. -/
def triangleShear (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleSpace W x y z ⟶ mappingFibre W x z ⨯ mappingFibre W x y :=
  prod.lift (triangleMiddle W x y z) (triangleComparison W x y z ≫ prod.fst)

@[reassoc (attr := simp)]
theorem triangleShear_middle (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShear W x y z ≫ prod.fst = triangleMiddle W x y z := prod.lift_fst _ _

@[reassoc (attr := simp)]
theorem triangleShear_first (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShear W x y z ≫ prod.snd = triangleComparison W x y z ≫ prod.fst :=
  prod.lift_snd _ _

private theorem shear_last_source_face (W : SimplicialSpace.{u}) :
    W.diagram.δ (0 : Fin 3) ≫ W.diagram.δ (1 : Fin 2) =
      W.diagram.δ (2 : Fin 3) ≫ W.diagram.δ (0 : Fin 2) := by
  change W.diagram.map (SimplexCategory.δ (0 : Fin 3)).op ≫
      W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op =
    W.diagram.map (SimplexCategory.δ (2 : Fin 3)).op ≫
      W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op
  have h : SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (0 : Fin 3) =
      SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3) := by decide
  simpa only [Functor.map_comp, op_comp] using
    congrArg (fun t => W.diagram.map t.op) h

private theorem shear_last_target_face (W : SimplicialSpace.{u}) :
    W.diagram.δ (0 : Fin 3) ≫ W.diagram.δ (0 : Fin 2) =
      W.diagram.δ (1 : Fin 3) ≫ W.diagram.δ (0 : Fin 2) := by
  change W.diagram.map (SimplexCategory.δ (0 : Fin 3)).op ≫
      W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op =
    W.diagram.map (SimplexCategory.δ (1 : Fin 3)).op ≫
      W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op
  have h : SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (0 : Fin 3) =
      SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3) := by decide
  simpa only [Functor.map_comp, op_comp] using
    congrArg (fun t => W.diagram.map t.op) h

/-- Recover the missing original edge12 with its original y/z endpoints and Delta0 point. -/
def triangleShearRecoverLast (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) : triangleShearPullback W x y z ⟶ mappingFibre W y z :=
  pullback.lift (triangleShearPullbackFst W x y z ≫ W.diagram.δ (0 : Fin 3))
    (triangleShearPullbackSnd W x y z ≫ prod.snd ≫ mappingFibre.snd W x y) (by
      apply prod.hom_ext
      · simp only [Category.assoc, mappingEndpoint_fst, mappingPointPair_fst]
        rw [shear_last_source_face, triangleShearPullback_first_assoc]
        simp only [mappingFibre.target_eq]
      · simp only [Category.assoc, mappingEndpoint_snd, mappingPointPair_snd]
        rw [shear_last_target_face, triangleShearPullback_middle_assoc]
        simp only [mappingFibre.target_eq]
        have h : triangleShearPullbackSnd W x y z ≫ prod.fst ≫ mappingFibre.snd W x z =
            triangleShearPullbackSnd W x y z ≫ prod.snd ≫ mappingFibre.snd W x y :=
          SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
        simpa only [Category.assoc] using
          congrArg (fun t => t ≫ SSet.yonedaEquiv.symm z) h)

@[reassoc (attr := simp)]
theorem triangleShearRecoverLast_fst (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearRecoverLast W x y z ≫ mappingFibre.fst W y z =
      triangleShearPullbackFst W x y z ≫ W.diagram.δ (0 : Fin 3) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem triangleShearRecoverLast_snd (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearRecoverLast W x y z ≫ mappingFibre.snd W y z =
      triangleShearPullbackSnd W x y z ≫ prod.snd ≫ mappingFibre.snd W x y :=
  pullback.lift_snd _ _ _

/-- Recovery retains the exact original source-y endpoint of edge12. -/
@[reassoc]
theorem triangleShearRecoverLast_source (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearRecoverLast W x y z ≫ mappingFibre.fst W y z ≫
        W.diagram.δ (1 : Fin 2) =
      triangleShearPullbackSnd W x y z ≫ prod.snd ≫ mappingFibre.snd W x y ≫
        SSet.yonedaEquiv.symm y := by
  rw [mappingFibre.source_eq, triangleShearRecoverLast_snd_assoc]

/-- Recovery retains the exact original target-z endpoint of edge12. -/
@[reassoc]
theorem triangleShearRecoverLast_target (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearRecoverLast W x y z ≫ mappingFibre.fst W y z ≫
        W.diagram.δ (0 : Fin 2) =
      triangleShearPullbackSnd W x y z ≫ prod.snd ≫ mappingFibre.snd W x y ≫
        SSet.yonedaEquiv.symm z := by
  rw [mappingFibre.target_eq, triangleShearRecoverLast_snd_assoc]

/-- The original triangle-to-Rout arrow, recording its W2 and middle/first pair. -/
def triangleShearToPullback (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) : triangleSpace W x y z ⟶ triangleShearPullback W x y z :=
  pullback.lift (triangleProjection W x y z) (triangleShear W x y z) (by
    apply pullback.hom_ext
    · simp only [Category.assoc, outerHornComparison_fst, triangleShearPair_fst,
        triangleShear_middle_assoc, triangleMiddle_fst]
    · simp only [Category.assoc, outerHornComparison_snd, triangleShearPair_snd,
        triangleShear_first_assoc, triangleProjection_first])

@[reassoc (attr := simp)]
private theorem triangleShearToPullback_fst (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearToPullback W x y z ≫ triangleShearPullbackFst W x y z =
      triangleProjection W x y z := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem triangleShearToPullback_snd (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearToPullback W x y z ≫ triangleShearPullbackSnd W x y z =
      triangleShear W x y z := pullback.lift_snd _ _ _

/-- The original Rout-to-triangle arrow, recovering the missing last12 edge. -/
def triangleShearFromPullback (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) : triangleShearPullback W x y z ⟶ triangleSpace W x y z :=
  pullback.lift (triangleShearPullbackFst W x y z)
    (prod.lift (triangleShearPullbackSnd W x y z ≫ prod.snd)
      (triangleShearRecoverLast W x y z)) (by
        apply pullback.hom_ext
        · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst,
            prod.lift_fst_assoc, triangleShearPullback_first]
        · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd,
            prod.lift_snd_assoc, triangleShearRecoverLast_fst])

@[reassoc (attr := simp)]
private theorem triangleShearFromPullback_projection (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearFromPullback W x y z ≫ triangleProjection W x y z =
      triangleShearPullbackFst W x y z := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem triangleShearFromPullback_comparison (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearFromPullback W x y z ≫ triangleComparison W x y z =
      prod.lift (triangleShearPullbackSnd W x y z ≫ prod.snd)
        (triangleShearRecoverLast W x y z) := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
private theorem triangleShearFromPullback_middle (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearFromPullback W x y z ≫ triangleMiddle W x y z =
      triangleShearPullbackSnd W x y z ≫ prod.fst := by
  apply pullback.hom_ext (f := mappingEndpoint W) (g := mappingPointPair W x z)
  · change (triangleShearFromPullback W x y z ≫ triangleMiddle W x y z) ≫
        mappingFibre.fst W x z =
      (triangleShearPullbackSnd W x y z ≫ prod.fst) ≫ mappingFibre.fst W x z
    simp only [Category.assoc, triangleMiddle_fst,
      triangleShearFromPullback_projection_assoc, triangleShearPullback_middle]
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

@[reassoc (attr := simp)]
private theorem triangleShearToPullback_recover (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearToPullback W x y z ≫ triangleShearRecoverLast W x y z =
      triangleComparison W x y z ≫ prod.snd := by
  apply pullback.hom_ext (f := mappingEndpoint W) (g := mappingPointPair W y z)
  · change (triangleShearToPullback W x y z ≫ triangleShearRecoverLast W x y z) ≫
        mappingFibre.fst W y z =
      (triangleComparison W x y z ≫ prod.snd) ≫ mappingFibre.fst W y z
    simp only [Category.assoc, triangleShearRecoverLast_fst,
      triangleShearToPullback_fst_assoc, triangleProjection_last]
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The original prescribed triangle space is the SAME middle/first fork pullback, for ANY W. -/
def triangleShearIso (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) : triangleSpace W x y z ≅ triangleShearPullback W x y z where
  hom := triangleShearToPullback W x y z
  inv := triangleShearFromPullback W x y z
  hom_inv_id := by
    apply pullback.hom_ext (f := twoEdgeComparison W) (g := twoEdgePair W x y z)
    · simp only [Category.assoc, triangleShearFromPullback_projection,
        triangleShearToPullback_fst, Category.id_comp]
    · apply prod.hom_ext
      · simp only [Category.assoc, triangleShearFromPullback_comparison,
          prod.lift_fst, triangleShearToPullback_snd_assoc,
          triangleShear_first, Category.id_comp]
      · simp only [Category.assoc, triangleShearFromPullback_comparison,
          prod.lift_snd, triangleShearToPullback_recover, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext (f := outerHornComparison W) (g := triangleShearPair W x y z)
    · simp only [Category.assoc, triangleShearToPullback_fst,
        triangleShearFromPullback_projection, Category.id_comp]
    · apply prod.hom_ext
      · simp only [Category.assoc, triangleShearToPullback_snd,
          triangleShear_middle, triangleShearFromPullback_middle, Category.id_comp]
      · simp only [Category.assoc, triangleShearToPullback_snd,
          triangleShear_first, triangleShearFromPullback_comparison_assoc,
          prod.lift_fst, Category.id_comp]

/-- The forward isomorphism retains the original W2 projection. -/
@[reassoc (attr := simp)]
theorem triangleShearIso_hom_projection (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    (triangleShearIso W x y z).hom ≫ triangleShearPullbackFst W x y z =
      triangleProjection W x y z := triangleShearToPullback_fst W x y z

/-- The forward isomorphism followed by the native second projection is the exact shear. -/
@[reassoc (attr := simp)]
theorem triangleShearIso_hom_pair (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    (triangleShearIso W x y z).hom ≫ triangleShearPullbackSnd W x y z =
      triangleShear W x y z := triangleShearToPullback_snd W x y z

/-- Its inverse retains the same original W2 projection. -/
@[reassoc (attr := simp)]
theorem triangleShearIso_inv_projection (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    (triangleShearIso W x y z).inv ≫ triangleProjection W x y z =
      triangleShearPullbackFst W x y z := triangleShearFromPullback_projection W x y z

/-- Its inverse retains the original prescribed first01 mapping-fibre edge. -/
@[reassoc (attr := simp)]
theorem triangleShearIso_inv_first (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    (triangleShearIso W x y z).inv ≫ triangleComparison W x y z ≫ prod.fst =
      triangleShearPullbackSnd W x y z ≫ prod.snd := by
  simp only [triangleShearIso, triangleShearFromPullback_comparison_assoc, prod.lift_fst]

/-- Its inverse reconstructs exactly the original missing last12 mapping-fibre edge. -/
@[reassoc (attr := simp)]
theorem triangleShearIso_inv_last (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    (triangleShearIso W x y z).inv ≫ triangleComparison W x y z ≫ prod.snd =
      triangleShearRecoverLast W x y z := by
  simp only [triangleShearIso, triangleShearFromPullback_comparison_assoc, prod.lift_snd]

/-- Its inverse retains the SAME original prescribed middle02 mapping-fibre edge. -/
@[reassoc (attr := simp)]
theorem triangleShearIso_inv_middle (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    (triangleShearIso W x y z).inv ≫ triangleMiddle W x y z =
      triangleShearPullbackSnd W x y z ≫ prod.fst := triangleShearFromPullback_middle W x y z

private def shearTwoEdgeMap {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    twoEdgePullback W ⟶ twoEdgePullback V :=
  pullback.map (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (1 : Fin 2))
    (V.diagram.δ (0 : Fin 2)) (V.diagram.δ (1 : Fin 2))
    (q.hom.app (op ⦋1⦌)) (q.hom.app (op ⦋1⦌)) (q.hom.app (op ⦋0⦌))
    (q.hom.naturality (SimplexCategory.δ (0 : Fin 2)).op)
    (q.hom.naturality (SimplexCategory.δ (1 : Fin 2)).op)

@[reassoc (attr := simp)]
private theorem shearTwoEdgeMap_fst {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    shearTwoEdgeMap q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ q.hom.app (op ⦋1⦌) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem shearTwoEdgeMap_snd {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    shearTwoEdgeMap q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ q.hom.app (op ⦋1⦌) :=
  pullback.lift_snd _ _ _

private theorem shearTwoEdgeComparison_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    twoEdgeComparison W ≫ shearTwoEdgeMap q = q.hom.app (op ⦋2⦌) ≫ twoEdgeComparison V := by
  apply pullback.hom_ext
  · simp only [Category.assoc, shearTwoEdgeMap_fst, twoEdgeComparison_fst_assoc,
      twoEdgeComparison_fst]
    exact q.hom.naturality (SimplexCategory.δ (2 : Fin 3)).op
  · simp only [Category.assoc, shearTwoEdgeMap_snd, twoEdgeComparison_snd_assoc,
      twoEdgeComparison_snd]
    exact q.hom.naturality (SimplexCategory.δ (0 : Fin 3)).op

private theorem shearTwoEdgePair_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    twoEdgePair W x y z ≫ shearTwoEdgeMap q =
      prod.map (mappingFibre.map q (x := x) (y := y) rfl rfl)
        (mappingFibre.map q (x := y) (y := z) rfl rfl) ≫
      twoEdgePair V (mappingVertexMap q x) (mappingVertexMap q y) (mappingVertexMap q z) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, shearTwoEdgeMap_fst, twoEdgePair_fst,
      twoEdgePair_fst_assoc, prod.map_fst_assoc, mappingFibre.map_fst]
  · simp only [Category.assoc, shearTwoEdgeMap_snd, twoEdgePair_snd,
      twoEdgePair_snd_assoc, prod.map_snd_assoc, mappingFibre.map_fst]

/-- The OWN public original triangle transport, built from the actual two-edge pullbacks. -/
def triangleShearTriangleMap {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleSpace W x y z ⟶
      triangleSpace V (mappingVertexMap q x) (mappingVertexMap q y) (mappingVertexMap q z) :=
  pullback.map (twoEdgeComparison W) (twoEdgePair W x y z)
    (twoEdgeComparison V)
    (twoEdgePair V (mappingVertexMap q x) (mappingVertexMap q y) (mappingVertexMap q z))
    (q.hom.app (op ⦋2⦌))
    (prod.map (mappingFibre.map q (x := x) (y := y) rfl rfl)
      (mappingFibre.map q (x := y) (y := z) rfl rfl)) (shearTwoEdgeMap q)
    (shearTwoEdgeComparison_natural q) (shearTwoEdgePair_natural q x y z)

/-- Public triangle transport retains the original outer-two component. -/
@[reassoc (attr := simp)]
theorem triangleShearTriangleMap_projection {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearTriangleMap q x y z ≫
        triangleProjection V (mappingVertexMap q x) (mappingVertexMap q y) (mappingVertexMap q z) =
      triangleProjection W x y z ≫ q.hom.app (op ⦋2⦌) := pullback.lift_fst _ _ _

/-- Public triangle transport retains both original moving mapping-fibre edges. -/
@[reassoc (attr := simp)]
theorem triangleShearTriangleMap_comparison {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearTriangleMap q x y z ≫
        triangleComparison V (mappingVertexMap q x) (mappingVertexMap q y) (mappingVertexMap q z) =
      triangleComparison W x y z ≫
        prod.map (mappingFibre.map q (x := x) (y := y) rfl rfl)
          (mappingFibre.map q (x := y) (y := z) rfl rfl) := pullback.lift_snd _ _ _

/-- Public triangle transport preserves the original middle02 edge with moved vertices. -/
@[reassoc (attr := simp)]
theorem triangleShearTriangleMap_middle {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearTriangleMap q x y z ≫
        triangleMiddle V (mappingVertexMap q x) (mappingVertexMap q y) (mappingVertexMap q z) =
      triangleMiddle W x y z ≫ mappingFibre.map q (x := x) (y := z) rfl rfl := by
  apply pullback.hom_ext (f := mappingEndpoint V)
    (g := mappingPointPair V (mappingVertexMap q x) (mappingVertexMap q z))
  · change (triangleShearTriangleMap q x y z ≫
        triangleMiddle V (mappingVertexMap q x) (mappingVertexMap q y) (mappingVertexMap q z)) ≫
      mappingFibre.fst V (mappingVertexMap q x) (mappingVertexMap q z) =
      (triangleMiddle W x y z ≫ mappingFibre.map q (x := x) (y := z) rfl rfl) ≫
        mappingFibre.fst V (mappingVertexMap q x) (mappingVertexMap q z)
    simp only [Category.assoc, triangleMiddle_fst, triangleShearTriangleMap_projection_assoc,
      mappingFibre.map_fst]
    rw [triangleMiddle_fst_assoc]
    exact congrArg (fun t => triangleProjection W x y z ≫ t)
      (SimplicialObject.δ_naturality q.hom (1 : Fin 3)).symm
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The original prescribed middle/first pair retains strict target-map naturality. -/
@[reassoc]
theorem triangleShearPair_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearPair W x y z ≫ outerHornForkMap q =
      prod.map (mappingFibre.map q (x := x) (y := z) rfl rfl)
        (mappingFibre.map q (x := x) (y := y) rfl rfl) ≫
      triangleShearPair V (mappingVertexMap q x) (mappingVertexMap q y) (mappingVertexMap q z) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, outerHornForkMap_fst, triangleShearPair_fst_assoc,
      triangleShearPair_fst, prod.map_fst_assoc, mappingFibre.map_fst]
  · simp only [Category.assoc, outerHornForkMap_snd, triangleShearPair_snd_assoc,
      triangleShearPair_snd, prod.map_snd_assoc, mappingFibre.map_fst]

/-- The OWN public original Rout transport is the native pullback map of the same fork data. -/
def triangleShearPullbackMap {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearPullback W x y z ⟶
      triangleShearPullback V (mappingVertexMap q x) (mappingVertexMap q y)
          (mappingVertexMap q z) :=
  pullback.map (outerHornComparison W) (triangleShearPair W x y z)
    (outerHornComparison V)
    (triangleShearPair V (mappingVertexMap q x) (mappingVertexMap q y) (mappingVertexMap q z))
    (q.hom.app (op ⦋2⦌))
    (prod.map (mappingFibre.map q (x := x) (y := z) rfl rfl)
      (mappingFibre.map q (x := x) (y := y) rfl rfl)) (outerHornForkMap q)
    (outerHornComparison_natural q) (triangleShearPair_natural q x y z)

@[reassoc (attr := simp)]
theorem triangleShearPullbackMap_projection {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearPullbackMap q x y z ≫
        triangleShearPullbackFst V (mappingVertexMap q x) (mappingVertexMap q y)
            (mappingVertexMap q z) =
      triangleShearPullbackFst W x y z ≫ q.hom.app (op ⦋2⦌) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem triangleShearPullbackMap_pair {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearPullbackMap q x y z ≫
        triangleShearPullbackSnd V (mappingVertexMap q x) (mappingVertexMap q y)
            (mappingVertexMap q z) =
      triangleShearPullbackSnd W x y z ≫
        prod.map (mappingFibre.map q (x := x) (y := z) rfl rfl)
          (mappingFibre.map q (x := x) (y := y) rfl rfl) := pullback.lift_snd _ _ _

/-- The exact raw middle-first shear is strictly natural at every original target arrow. -/
@[reassoc]
theorem triangleShear_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearTriangleMap q x y z ≫
        triangleShear V (mappingVertexMap q x) (mappingVertexMap q y) (mappingVertexMap q z) =
      triangleShear W x y z ≫
        prod.map (mappingFibre.map q (x := x) (y := z) rfl rfl)
          (mappingFibre.map q (x := x) (y := y) rfl rfl) := by
  apply prod.hom_ext
  · simp only [Category.assoc, triangleShear_middle, triangleShearTriangleMap_middle,
      prod.map_fst, triangleShear_middle_assoc]
  · simp only [Category.assoc, triangleShear_first, triangleShearTriangleMap_comparison_assoc,
      prod.map_fst, prod.map_snd, triangleShear_first_assoc]

/-- Both original pullback projections prove strict naturality of the constructed isomorphism. -/
@[reassoc]
theorem triangleShearIso_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleShearTriangleMap q x y z ≫
        (triangleShearIso V (mappingVertexMap q x) (mappingVertexMap q y)
            (mappingVertexMap q z)).hom =
      (triangleShearIso W x y z).hom ≫ triangleShearPullbackMap q x y z := by
  apply pullback.hom_ext (f := outerHornComparison V)
    (g := triangleShearPair V (mappingVertexMap q x) (mappingVertexMap q y) (mappingVertexMap q z))
  · change (triangleShearTriangleMap q x y z ≫
        (triangleShearIso V (mappingVertexMap q x) (mappingVertexMap q y)
            (mappingVertexMap q z)).hom) ≫
      triangleShearPullbackFst V (mappingVertexMap q x) (mappingVertexMap q y)
          (mappingVertexMap q z) =
      ((triangleShearIso W x y z).hom ≫ triangleShearPullbackMap q x y z) ≫
        triangleShearPullbackFst V (mappingVertexMap q x) (mappingVertexMap q y)
            (mappingVertexMap q z)
    simp only [Category.assoc, triangleShearIso_hom_projection,
      triangleShearTriangleMap_projection, triangleShearPullbackMap_projection,
      triangleShearIso_hom_projection_assoc]
  · change (triangleShearTriangleMap q x y z ≫
        (triangleShearIso V (mappingVertexMap q x) (mappingVertexMap q y)
            (mappingVertexMap q z)).hom) ≫
      triangleShearPullbackSnd V (mappingVertexMap q x) (mappingVertexMap q y)
          (mappingVertexMap q z) =
      ((triangleShearIso W x y z).hom ≫ triangleShearPullbackMap q x y z) ≫
        triangleShearPullbackSnd V (mappingVertexMap q x) (mappingVertexMap q y)
            (mappingVertexMap q z)
    simp only [Category.assoc, triangleShearIso_hom_pair, triangleShear_natural,
      triangleShearPullbackMap_pair, triangleShearIso_hom_pair_assoc]

/-- The original inverse isomorphism retains the same moving-vertex naturality. -/
@[reassoc]
theorem triangleShearIso_inv_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    (triangleShearIso W x y z).inv ≫ triangleShearTriangleMap q x y z =
      triangleShearPullbackMap q x y z ≫
        (triangleShearIso V (mappingVertexMap q x) (mappingVertexMap q y)
            (mappingVertexMap q z)).inv :=
  inverseIsoSquare _ _ _ _ (triangleShearIso_natural q x y z)

end SimplicialSpace.SegalHomotopy

namespace SimplicialSpace.ReedyModel

open SimplicialSpace.SegalHomotopy
open scoped SSet.modelCategoryQuillen

private theorem sourceHornComparison_fibration (W : SimplicialSpace.{u}) :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    IsFibrant W → Fibration (outerHornComparison W) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  dsimp only
  intro hW
  let i := (SSet.horn 2 (0 : Fin 3) : (Δ[2] : SSet.{u}).Subcomplex).ι
  have : Mono i := by dsimp [i]; infer_instance
  have : Mono (SSet.simplicialSpaceDiscrete.map i) := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [NatTrans.mono_iff_mono_app]
    intro k
    change Mono (i.app n)
    infer_instance
  let f := ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map i)
  have : Mono f := by dsimp [f]; infer_instance
  have hf : Cofibration f := (cofibration_iff f).2 inferInstance
  have hp := inner_precomp_fibration f W
    ((HomotopicalAlgebra.cofibration_iff f).1 hf) hW
  have : Fibration ((discreteSourceMapping W).map i.op) :=
    (HomotopicalAlgebra.fibration_iff _).2 hp
  rw [← outerHornMappingIso_normalization W]
  infer_instance

/-- Reedy fibrancy alone makes the original middle-first triangle shear a Kan fibration. -/
theorem triangleShear_fibration (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    IsFibrant W → Fibration (triangleShear W x y z) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  dsimp only
  intro hW
  let _ : Fibration (outerHornComparison W) := sourceHornComparison_fibration W hW
  let _ : Fibration (triangleShearPullbackSnd W x y z) := by
    change Fibration (pullback.snd (outerHornComparison W) (triangleShearPair W x y z))
    infer_instance
  rw [← triangleShearIso_hom_pair W x y z]
  infer_instance

/-- Every original positive horn has the lifting property against that same shear. -/
theorem triangleShear_hasLiftingProperty (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    IsFibrant W → ∀ (n : ℕ), 1 ≤ n → ∀ (i : Fin (n + 1)),
      HasLiftingProperty (SSet.horn n i).ι (triangleShear W x y z) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  dsimp only
  intro hW n hn i
  let _ : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)⟩
  exact (SSet.modelCategoryQuillen.fibration_iff _).1
    (triangleShear_fibration W x y z hW) _
    (SSet.modelCategoryQuillen.horn_ι_mem_J n i)

/-- A native diagonal for every original positive-horn square, with both factor equations. -/
def triangleShearHornLift (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    IsFibrant W → ∀ (n : ℕ) (_ : 1 ≤ n) (i : Fin (n + 1))
      (a : (Λ[n, i] : SSet.{u}) ⟶ triangleSpace W x y z)
      (b : (Δ[n] : SSet.{u}) ⟶ mappingFibre W x z ⨯ mappingFibre W x y)
      (sq : CommSq a (SSet.horn n i).ι (triangleShear W x y z) b), sq.LiftStruct := by
  letI : ModelCategory SimplicialSpace.{u} := modelCategory
  letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hW n hn i a b sq
  let hL : sq.HasLift := (triangleShear_hasLiftingProperty W x y z hW n hn i).sq_hasLift sq
  exact hL.exists_lift.some

/-- The original horn followed by the native diagonal is the original top arrow. -/
theorem triangleShearHornLift_fac_left (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    ∀ (hW : IsFibrant W) (n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 1))
      (a : (Λ[n, i] : SSet.{u}) ⟶ triangleSpace W x y z)
      (b : (Δ[n] : SSet.{u}) ⟶ mappingFibre W x z ⨯ mappingFibre W x y)
      (sq : CommSq a (SSet.horn n i).ι (triangleShear W x y z) b),
      (SSet.horn n i).ι ≫ (triangleShearHornLift W x y z hW n hn i a b sq).l = a := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  dsimp only
  intro hW n hn i a b sq
  exact (triangleShearHornLift W x y z hW n hn i a b sq).fac_left

/-- The native diagonal followed by the same shear is the original bottom arrow. -/
theorem triangleShearHornLift_fac_right (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    ∀ (hW : IsFibrant W) (n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 1))
      (a : (Λ[n, i] : SSet.{u}) ⟶ triangleSpace W x y z)
      (b : (Δ[n] : SSet.{u}) ⟶ mappingFibre W x z ⨯ mappingFibre W x y)
      (sq : CommSq a (SSet.horn n i).ι (triangleShear W x y z) b),
      (triangleShearHornLift W x y z hW n hn i a b sq).l ≫ triangleShear W x y z = b := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  dsimp only
  intro hW n hn i a b sq
  exact (triangleShearHornLift W x y z hW n hn i a b sq).fac_right

/-- Every original positive-horn square admits a diagonal retaining both original legs. -/
theorem triangleShear_original_hornLift (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    IsFibrant W → ∀ (n : ℕ) (_ : 1 ≤ n) (i : Fin (n + 1))
      (a : (Λ[n, i] : SSet.{u}) ⟶ triangleSpace W x y z)
      (b : (Δ[n] : SSet.{u}) ⟶ mappingFibre W x z ⨯ mappingFibre W x y)
      (_ : CommSq a (SSet.horn n i).ι (triangleShear W x y z) b),
      ∃ l : (Δ[n] : SSet.{u}) ⟶ triangleSpace W x y z,
        (SSet.horn n i).ι ≫ l = a ∧ l ≫ triangleShear W x y z = b := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  dsimp only
  intro hW n hn i a b sq
  let l := triangleShearHornLift W x y z hW n hn i a b sq
  exact ⟨l.l, l.fac_left, l.fac_right⟩

/-- Transporting a given original horn filler preserves both strict legs at moved vertices. -/
theorem triangleShearHornLift_transport {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) (i : Fin (n + 1))
    (a : (Λ[n, i] : SSet.{u}) ⟶ triangleSpace W x y z)
    (b : (Δ[n] : SSet.{u}) ⟶ mappingFibre W x z ⨯ mappingFibre W x y)
    (sq : CommSq a (SSet.horn n i).ι (triangleShear W x y z) b) (l : sq.LiftStruct) :
    (SSet.horn n i).ι ≫ (l.l ≫ triangleShearTriangleMap q x y z) =
        a ≫ triangleShearTriangleMap q x y z ∧
      (l.l ≫ triangleShearTriangleMap q x y z) ≫
          triangleShear V (mappingVertexMap q x) (mappingVertexMap q y) (mappingVertexMap q z) =
        b ≫ prod.map (mappingFibre.map q (x := x) (y := z) rfl rfl)
          (mappingFibre.map q (x := x) (y := y) rfl rfl) := by
  constructor
  · rw [← Category.assoc, l.fac_left]
  · rw [Category.assoc, triangleShear_natural, ← Category.assoc, l.fac_right]

end SimplicialSpace.ReedyModel
