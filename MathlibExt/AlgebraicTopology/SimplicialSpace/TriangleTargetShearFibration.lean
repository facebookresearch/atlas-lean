/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalSpaces
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalHomotopyCategory
import Mathlib.CategoryTheory.Adjunction.ParametrizedLimits
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# The original target-horn corners and their mapped pullback
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory
open scoped Simplicial SimplicialSpace.Inner

namespace SSet.Rezk

/-- The common original target vertex2. -/
abbrev outerHornTargetVertex : (Δ[2] : SSet.{u}).Subcomplex :=
  stdSimplex.face ({0, 1} : Finset (Fin 3))ᶜ

/-- The original02 edge, first in the target fork. -/
abbrev outerHornTargetLeftFace : (Δ[2] : SSet.{u}).Subcomplex :=
  stdSimplex.face ({1} : Finset (Fin 3))ᶜ

/-- The original12 edge, second in the target fork. -/
abbrev outerHornTargetRightFace : (Δ[2] : SSet.{u}).Subcomplex :=
  stdSimplex.face ({0} : Finset (Fin 3))ᶜ

/-- The literal target outer horn. -/
abbrev outerHornTarget : (Δ[2] : SSet.{u}).Subcomplex := horn 2 (2 : Fin 3)

/-- The two original edges intersect in vertex2. -/
theorem outerHornTarget_inf :
    outerHornTargetLeftFace.{u} ⊓ outerHornTargetRightFace = outerHornTargetVertex := by
  rw [stdSimplex.face_inter_face]
  congr 1

/-- Both original edges, in their given order, cover the actual horn. -/
theorem outerHornTarget_sup :
    outerHornTargetLeftFace.{u} ⊔ outerHornTargetRightFace = outerHornTarget := by
  change stdSimplex.face ({1} : Finset (Fin 3))ᶜ ⊔
    stdSimplex.face ({0} : Finset (Fin 3))ᶜ = horn 2 (2 : Fin 3)
  apply le_antisymm
  · exact sup_le (face_le_horn (1 : Fin 3) 2 (by decide))
      (face_le_horn (0 : Fin 3) 2 (by decide))
  · rw [horn_eq_iSup]
    apply iSup_le
    rintro ⟨j, hj⟩
    fin_cases j
    · exact le_sup_right
    · exact le_sup_left
    · simp at hj

/-- The original four corners form the actual bicartesian lattice square. -/
theorem outerHornTargetSquare :
    Subcomplex.BicartSq outerHornTargetVertex.{u} outerHornTargetLeftFace
      outerHornTargetRightFace outerHornTarget :=
  { inf_eq := outerHornTarget_inf
    sup_eq := outerHornTarget_sup }

/-- Include the common vertex in the first original edge. -/
def outerHornTargetVertexLeft :
    (outerHornTargetVertex.{u} : SSet.{u}) ⟶ outerHornTargetLeftFace :=
  Subcomplex.homOfLE outerHornTargetSquare.le₁₂

/-- Include the same common vertex in the second original edge. -/
def outerHornTargetVertexRight :
    (outerHornTargetVertex.{u} : SSet.{u}) ⟶ outerHornTargetRightFace :=
  Subcomplex.homOfLE outerHornTargetSquare.le₁₃

/-- The first original edge inclusion into the literal horn. -/
def outerHornTargetLeft :
    (outerHornTargetLeftFace.{u} : SSet.{u}) ⟶ outerHornTarget :=
  Subcomplex.homOfLE outerHornTargetSquare.le₂₄

/-- The second original edge inclusion into the literal horn. -/
def outerHornTargetRight :
    (outerHornTargetRightFace.{u} : SSet.{u}) ⟶ outerHornTarget :=
  Subcomplex.homOfLE outerHornTargetSquare.le₃₄

/-- The constructed original four-leg pushout. -/
theorem outerHornTarget_isPushout :
    IsPushout outerHornTargetVertexLeft.{u} outerHornTargetVertexRight
      outerHornTargetLeft outerHornTargetRight :=
  outerHornTargetSquare.isPushout

/-- The original common vertex is represented by Delta0. -/
def outerHornTargetVertexIso : (Δ[0] : SSet.{u}) ≅ outerHornTargetVertex :=
  stdSimplex.facePairComplIso (0 : Fin 3) 1 (by decide)

/-- The original02 edge is represented by Delta1. -/
def outerHornTargetLeftIso : (Δ[1] : SSet.{u}) ≅ outerHornTargetLeftFace :=
  stdSimplex.faceSingletonComplIso (1 : Fin 3)

/-- The original12 edge is represented by Delta1. -/
def outerHornTargetRightIso : (Δ[1] : SSet.{u}) ≅ outerHornTargetRightFace :=
  stdSimplex.faceSingletonComplIso (0 : Fin 3)

/-- Both represented vertex inclusions are the actual target delta0. -/
theorem outerHornTargetVertexLeft_normalization :
    outerHornTargetVertexIso.{u}.hom ≫ outerHornTargetVertexLeft =
      stdSimplex.δ (0 : Fin 2) ≫ outerHornTargetLeftIso.hom := by
  apply (cancel_mono outerHornTargetLeftFace.ι).mp
  rw [Category.assoc, outerHornTargetVertexLeft, Subcomplex.homOfLE_ι,
    outerHornTargetVertexIso, stdSimplex.facePairComplIso_hom_ι,
    Category.assoc, outerHornTargetLeftIso, stdSimplex.faceSingletonComplIso_hom_ι]
  have hc : (0 : Fin 3).castPred (by decide) = (0 : Fin 2) := rfl
  rw [hc]

/-- The other original target vertex inclusion retains the same delta0. -/
theorem outerHornTargetVertexRight_normalization :
    outerHornTargetVertexIso.{u}.hom ≫ outerHornTargetVertexRight =
      stdSimplex.δ (0 : Fin 2) ≫ outerHornTargetRightIso.hom := by
  apply (cancel_mono outerHornTargetRightFace.ι).mp
  rw [Category.assoc, outerHornTargetVertexRight, Subcomplex.homOfLE_ι,
    outerHornTargetVertexIso, stdSimplex.facePairComplIso_hom_ι',
    Category.assoc, outerHornTargetRightIso, stdSimplex.faceSingletonComplIso_hom_ι]
  have hp : (1 : Fin 3).pred (by decide) = (0 : Fin 2) := rfl
  rw [hp]

/-- The first represented edge retains its literal original coface d1 into Delta2. -/
theorem outerHornTargetLeftIso_inclusion :
    outerHornTargetLeftIso.{u}.hom ≫ outerHornTargetLeft ≫ outerHornTarget.ι =
      stdSimplex.δ (1 : Fin 3) := by
  rw [outerHornTargetLeft, Subcomplex.homOfLE_ι, outerHornTargetLeftIso,
    stdSimplex.faceSingletonComplIso_hom_ι]

/-- The second represented edge retains its literal original coface d0 into Delta2. -/
theorem outerHornTargetRightIso_inclusion :
    outerHornTargetRightIso.{u}.hom ≫ outerHornTargetRight ≫ outerHornTarget.ι =
      stdSimplex.δ (0 : Fin 3) := by
  rw [outerHornTargetRight, Subcomplex.homOfLE_ι, outerHornTargetRightIso,
    stdSimplex.faceSingletonComplIso_hom_ι]

end SSet.Rezk

namespace SimplicialSpace

open SSet.Rezk

private theorem targetDiscretePreservesPushouts :
    PreservesColimitsOfShape WalkingSpan SSet.simplicialSpaceDiscrete.{u} :=
  ⟨fun {K} => ⟨fun c {hc} => ⟨by
    apply evaluationJointlyReflectsColimits _ (fun k => ?_)
    change IsColimit
      ((((evaluation _ _).obj k ⋙ SimplicialObject.const (Type u)).mapCocone c))
    exact isColimitOfPreserves _ hc⟩⟩⟩

private theorem targetInnerPreservesPullbacks (W : SimplicialSpace.{u}) :
    PreservesLimitsOfShape WalkingCospan (innerHomFunctor.flip.obj W) := by
  let : ∀ K : SSet.{u}, PreservesColimitsOfShape WalkingCospanᵒᵖ
      (innerTensorBifunctor.flip.obj K) := fun K => by
    change PreservesColimitsOfShape WalkingCospanᵒᵖ (innerTensor K)
    let : (innerTensor K).IsLeftAdjoint := (innerTensorCotensorAdjunction K).isLeftAdjoint
    infer_instance
  exact innerTensorHomAdjunction₂.preservesLimitsOfShape_flip_obj WalkingCospan W

/-- Mapping the SAME four original target-horn legs gives their actual pullback. -/
theorem outerHornTargetMapping_isPullback (W : SimplicialSpace.{u}) :
    IsPullback
      ((discreteSourceMapping W).map outerHornTargetLeft.{u}.op)
      ((discreteSourceMapping W).map outerHornTargetRight.{u}.op)
      ((discreteSourceMapping W).map outerHornTargetVertexLeft.{u}.op)
      ((discreteSourceMapping W).map outerHornTargetVertexRight.{u}.op) := by
  let := targetDiscretePreservesPushouts.{u}
  let := targetInnerPreservesPullbacks W
  have sq := (outerHornTarget_isPushout.{u}.map SSet.simplicialSpaceDiscrete).map ofSimplicialObject
  exact (sq.op.map (innerHomFunctor.flip.obj W)).flip

/-- The mapped original target vertex is the actual W0. -/
def outerHornTargetVertexMappingIso (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).obj (op (outerHornTargetVertex.{u} : SSet.{u})) ≅
      W.diagram _⦋0⦌ :=
  (discreteSourceMapping W).mapIso outerHornTargetVertexIso.op ≪≫ discreteYonedaIso W 0

/-- The mapped original02 edge is the actual W1. -/
def outerHornTargetLeftMappingIso (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).obj (op (outerHornTargetLeftFace.{u} : SSet.{u})) ≅
      W.diagram _⦋1⦌ :=
  (discreteSourceMapping W).mapIso outerHornTargetLeftIso.op ≪≫ discreteYonedaIso W 1

/-- The mapped original12 edge is also the same actual W1. -/
def outerHornTargetRightMappingIso (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).obj (op (outerHornTargetRightFace.{u} : SSet.{u})) ≅
      W.diagram _⦋1⦌ :=
  (discreteSourceMapping W).mapIso outerHornTargetRightIso.op ≪≫ discreteYonedaIso W 1

private theorem targetMapNormalization (W : SimplicialSpace.{u})
    {A B : SSet.{u}} (i : A ⟶ B) (a : (Δ[0] : SSet.{u}) ≅ A)
    (b : (Δ[1] : SSet.{u}) ≅ B)
    (h : a.hom ≫ i = SSet.stdSimplex.δ (0 : Fin 2) ≫ b.hom) :
    (discreteSourceMapping W).map i.op ≫
        ((discreteSourceMapping W).mapIso a.op ≪≫ discreteYonedaIso W 0).hom =
      ((discreteSourceMapping W).mapIso b.op ≪≫ discreteYonedaIso W 1).hom ≫
        W.diagram.δ (0 : Fin 2) := by
  have hn : (discreteSourceMapping W).map (SSet.stdSimplex.δ (0 : Fin 2)).op ≫
      (discreteYonedaIso W 0).hom = (discreteYonedaIso W 1).hom ≫ W.diagram.δ (0 : Fin 2) :=
    discreteYonedaIso_naturality_index W (SimplexCategory.δ (0 : Fin 2))
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Category.assoc]
  rw [← Category.assoc, ← (discreteSourceMapping W).map_comp, ← op_comp, h, op_comp,
    (discreteSourceMapping W).map_comp, Category.assoc, hn]

/-- The first mapped original vertex restriction is exactly the actual d0. -/
theorem outerHornTargetVertexLeft_mapping (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).map outerHornTargetVertexLeft.{u}.op ≫
        (outerHornTargetVertexMappingIso W).hom =
      (outerHornTargetLeftMappingIso W).hom ≫ W.diagram.δ (0 : Fin 2) :=
  targetMapNormalization W _ _ _ outerHornTargetVertexLeft_normalization

/-- The other mapped original vertex restriction is exactly the same actual d0. -/
theorem outerHornTargetVertexRight_mapping (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).map outerHornTargetVertexRight.{u}.op ≫
        (outerHornTargetVertexMappingIso W).hom =
      (outerHornTargetRightMappingIso W).hom ≫ W.diagram.δ (0 : Fin 2) :=
  targetMapNormalization W _ _ _ outerHornTargetVertexRight_normalization

private theorem targetCornerNaturality {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    {A : SSet.{u}} {n : ℕ} (e : (Δ[n] : SSet.{u}) ≅ A) :
    (discreteSourceMappingMap q).app (op A) ≫
        ((discreteSourceMapping V).mapIso e.op ≪≫ discreteYonedaIso V n).hom =
      ((discreteSourceMapping W).mapIso e.op ≪≫ discreteYonedaIso W n).hom ≫
        q.hom.app (op ⦋n⦌) := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Category.assoc]
  rw [← Category.assoc, ← (discreteSourceMappingMap q).naturality, Category.assoc,
    discreteYonedaIso_naturality_target]

/-- The target vertex comparison retains every original W→V. -/
theorem outerHornTargetVertexMappingIso_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    (discreteSourceMappingMap q).app (op (outerHornTargetVertex.{u} : SSet.{u})) ≫
        (outerHornTargetVertexMappingIso V).hom =
      (outerHornTargetVertexMappingIso W).hom ≫ q.hom.app (op ⦋0⦌) :=
  targetCornerNaturality q outerHornTargetVertexIso

/-- The original02 corner comparison retains every actual target map. -/
theorem outerHornTargetLeftMappingIso_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    (discreteSourceMappingMap q).app (op (outerHornTargetLeftFace.{u} : SSet.{u})) ≫
        (outerHornTargetLeftMappingIso V).hom =
      (outerHornTargetLeftMappingIso W).hom ≫ q.hom.app (op ⦋1⦌) :=
  targetCornerNaturality q outerHornTargetLeftIso

/-- The original12 corner comparison retains every actual target map. -/
theorem outerHornTargetRightMappingIso_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    (discreteSourceMappingMap q).app (op (outerHornTargetRightFace.{u} : SSet.{u})) ≫
        (outerHornTargetRightMappingIso V).hom =
      (outerHornTargetRightMappingIso W).hom ≫ q.hom.app (op ⦋1⦌) :=
  targetCornerNaturality q outerHornTargetRightIso

/-- Every original inner operator is retained by the target-vertex comparison. -/
theorem outerHornTargetVertexMappingIso_operator (W : SimplicialSpace.{u})
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    ((discreteSourceMapping W).obj (op (outerHornTargetVertex.{u} : SSet.{u}))).map α ≫
        (outerHornTargetVertexMappingIso W).hom.app m =
      (outerHornTargetVertexMappingIso W).hom.app n ≫ (W.diagram _⦋0⦌).map α :=
  (outerHornTargetVertexMappingIso W).hom.naturality α

/-- Every original inner operator is retained by the first edge comparison. -/
theorem outerHornTargetLeftMappingIso_operator (W : SimplicialSpace.{u})
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    ((discreteSourceMapping W).obj (op (outerHornTargetLeftFace.{u} : SSet.{u}))).map α ≫
        (outerHornTargetLeftMappingIso W).hom.app m =
      (outerHornTargetLeftMappingIso W).hom.app n ≫ (W.diagram _⦋1⦌).map α :=
  (outerHornTargetLeftMappingIso W).hom.naturality α

/-- Every original inner operator is retained by the second edge comparison. -/
theorem outerHornTargetRightMappingIso_operator (W : SimplicialSpace.{u})
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    ((discreteSourceMapping W).obj (op (outerHornTargetRightFace.{u} : SSet.{u}))).map α ≫
        (outerHornTargetRightMappingIso W).hom.app m =
      (outerHornTargetRightMappingIso W).hom.app n ≫ (W.diagram _⦋1⦌).map α :=
  (outerHornTargetRightMappingIso W).hom.naturality α

end SimplicialSpace

namespace SimplicialSpace

open SSet.Rezk

/-- The actual target matching fork, ordered original02 then original12. -/
abbrev outerHornTargetFork (W : SimplicialSpace.{u}) : SSet.{u} :=
  pullback (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (0 : Fin 2))

/-- The original target-horn comparison retains the original middle and last cofaces. -/
def outerHornTargetComparison (W : SimplicialSpace.{u}) :
    W.diagram _⦋2⦌ ⟶ outerHornTargetFork W :=
  pullback.lift (W.diagram.δ (1 : Fin 3)) (W.diagram.δ (0 : Fin 3))
    (W.diagram.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2)) (by decide))

/-- The first target-fork projection is the literal original d1. -/
@[reassoc (attr := simp)]
theorem outerHornTargetComparison_fst (W : SimplicialSpace.{u}) :
    outerHornTargetComparison W ≫ pullback.fst _ _ = W.diagram.δ (1 : Fin 3) := by
  simp [outerHornTargetComparison]

/-- The second target-fork projection is the literal original d0. -/
@[reassoc (attr := simp)]
theorem outerHornTargetComparison_snd (W : SimplicialSpace.{u}) :
    outerHornTargetComparison W ≫ pullback.snd _ _ = W.diagram.δ (0 : Fin 3) := by
  simp [outerHornTargetComparison]

/-- Every original target map induces the native map of the two d0 pullbacks. -/
def outerHornTargetForkMap {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    outerHornTargetFork W ⟶ outerHornTargetFork V :=
  pullback.map _ _ _ _ (q.hom.app (op ⦋1⦌)) (q.hom.app (op ⦋1⦌))
    (q.hom.app (op ⦋0⦌))
    (q.hom.naturality (SimplexCategory.δ (0 : Fin 2)).op)
    (q.hom.naturality (SimplexCategory.δ (0 : Fin 2)).op)

/-- The native target-fork map preserves its first original edge. -/
@[reassoc (attr := simp)]
theorem outerHornTargetForkMap_fst {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    outerHornTargetForkMap q ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ q.hom.app (op ⦋1⦌) := by
  simp [outerHornTargetForkMap]

/-- The native target-fork map preserves its second original edge. -/
@[reassoc (attr := simp)]
theorem outerHornTargetForkMap_snd {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    outerHornTargetForkMap q ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ q.hom.app (op ⦋1⦌) := by
  simp [outerHornTargetForkMap]

/-- The original target comparison is natural in every original simplicial space map. -/
theorem outerHornTargetComparison_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    outerHornTargetComparison W ≫ outerHornTargetForkMap q =
      q.hom.app (op ⦋2⦌) ≫ outerHornTargetComparison V := by
  apply pullback.hom_ext
  · simp only [Category.assoc, outerHornTargetForkMap_fst,
      outerHornTargetComparison_fst_assoc, outerHornTargetComparison_fst]
    exact q.hom.naturality (SimplexCategory.δ (1 : Fin 3)).op
  · simp only [Category.assoc, outerHornTargetForkMap_snd,
      outerHornTargetComparison_snd_assoc, outerHornTargetComparison_snd]
    exact q.hom.naturality (SimplexCategory.δ (0 : Fin 3)).op

/-- The whole original horn mapping object is the actual target matching fork. -/
def outerHornTargetMappingIso (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).obj (op (outerHornTarget.{u} : SSet.{u})) ≅
      outerHornTargetFork W :=
  ((outerHornTargetMapping_isPullback W).of_iso
    (fst' := (discreteSourceMapping W).map outerHornTargetLeft.{u}.op ≫
      (outerHornTargetLeftMappingIso W).hom)
    (snd' := (discreteSourceMapping W).map outerHornTargetRight.{u}.op ≫
      (outerHornTargetRightMappingIso W).hom)
    (f' := W.diagram.δ (0 : Fin 2)) (g' := W.diagram.δ (0 : Fin 2)) (Iso.refl _)
    (outerHornTargetLeftMappingIso W) (outerHornTargetRightMappingIso W)
    (outerHornTargetVertexMappingIso W)
    (by simp) (by simp) (outerHornTargetVertexLeft_mapping W)
    (outerHornTargetVertexRight_mapping W)).isoPullback

/-- The full horn isomorphism retains the actual represented02 restriction. -/
@[reassoc (attr := simp)]
theorem outerHornTargetMappingIso_hom_fst (W : SimplicialSpace.{u}) :
    (outerHornTargetMappingIso W).hom ≫ pullback.fst _ _ =
      (discreteSourceMapping W).map outerHornTargetLeft.{u}.op ≫
        (outerHornTargetLeftMappingIso W).hom := by
  simp [outerHornTargetMappingIso]

/-- The full horn isomorphism retains the actual represented12 restriction. -/
@[reassoc (attr := simp)]
theorem outerHornTargetMappingIso_hom_snd (W : SimplicialSpace.{u}) :
    (outerHornTargetMappingIso W).hom ≫ pullback.snd _ _ =
      (discreteSourceMapping W).map outerHornTargetRight.{u}.op ≫
        (outerHornTargetRightMappingIso W).hom := by
  simp [outerHornTargetMappingIso]

/-- Its inverse retains the first literal original horn restriction. -/
@[reassoc (attr := simp)]
theorem outerHornTargetMappingIso_inv_left (W : SimplicialSpace.{u}) :
    (outerHornTargetMappingIso W).inv ≫
        (discreteSourceMapping W).map outerHornTargetLeft.{u}.op =
      pullback.fst _ _ ≫ (outerHornTargetLeftMappingIso W).inv := by
  apply (cancel_mono (outerHornTargetLeftMappingIso W).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp [outerHornTargetMappingIso]

/-- Its inverse retains the second literal original horn restriction. -/
@[reassoc (attr := simp)]
theorem outerHornTargetMappingIso_inv_right (W : SimplicialSpace.{u}) :
    (outerHornTargetMappingIso W).inv ≫
        (discreteSourceMapping W).map outerHornTargetRight.{u}.op =
      pullback.snd _ _ ≫ (outerHornTargetRightMappingIso W).inv := by
  apply (cancel_mono (outerHornTargetRightMappingIso W).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp [outerHornTargetMappingIso]

private theorem targetHornRestrictionNormalization (W : SimplicialSpace.{u})
    {A : SSet.{u}} (i : A ⟶ Δ[2]) (a : (Δ[1] : SSet.{u}) ≅ A) (k : Fin 3)
    (h : a.hom ≫ i = SSet.stdSimplex.δ k) :
    (discreteYonedaIso W 2).inv ≫ (discreteSourceMapping W).map i.op ≫
        ((discreteSourceMapping W).mapIso a.op ≪≫ discreteYonedaIso W 1).hom =
      W.diagram.δ k := by
  have hn : (discreteSourceMapping W).map (SSet.stdSimplex.δ k).op ≫
      (discreteYonedaIso W 1).hom = (discreteYonedaIso W 2).hom ≫ W.diagram.δ k :=
    discreteYonedaIso_naturality_index W (SimplexCategory.δ k)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom]
  rw [← Category.assoc ((discreteSourceMapping W).map i.op)
      ((discreteSourceMapping W).map a.hom.op) (discreteYonedaIso W 1).hom,
    ← (discreteSourceMapping W).map_comp, ← op_comp, h,
    hn, Iso.inv_hom_id_assoc]

/-- Under the original Yoneda isomorphism, literal horn restriction is the same d1,d0 comparison. -/
theorem outerHornTargetMappingIso_restriction (W : SimplicialSpace.{u}) :
    (discreteYonedaIso W 2).inv ≫
        (discreteSourceMapping W).map outerHornTarget.{u}.ι.op ≫
        (outerHornTargetMappingIso W).hom = outerHornTargetComparison W := by
  apply pullback.hom_ext
  · simp only [Category.assoc, outerHornTargetMappingIso_hom_fst,
      outerHornTargetComparison_fst]
    rw [← Category.assoc ((discreteSourceMapping W).map outerHornTarget.{u}.ι.op)
        ((discreteSourceMapping W).map outerHornTargetLeft.{u}.op)
        (outerHornTargetLeftMappingIso W).hom,
      ← (discreteSourceMapping W).map_comp, ← op_comp]
    exact targetHornRestrictionNormalization W
      (outerHornTargetLeft ≫ outerHornTarget.ι) outerHornTargetLeftIso (1 : Fin 3)
      outerHornTargetLeftIso_inclusion
  · simp only [Category.assoc, outerHornTargetMappingIso_hom_snd,
      outerHornTargetComparison_snd]
    rw [← Category.assoc ((discreteSourceMapping W).map outerHornTarget.{u}.ι.op)
        ((discreteSourceMapping W).map outerHornTargetRight.{u}.op)
        (outerHornTargetRightMappingIso W).hom,
      ← (discreteSourceMapping W).map_comp, ← op_comp]
    exact targetHornRestrictionNormalization W
      (outerHornTargetRight ≫ outerHornTarget.ι) outerHornTargetRightIso (0 : Fin 3)
      outerHornTargetRightIso_inclusion

/-- The whole horn isomorphism preserves the original target map on both projections. -/
theorem outerHornTargetMappingIso_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    (discreteSourceMappingMap q).app (op (outerHornTarget.{u} : SSet.{u})) ≫
        (outerHornTargetMappingIso V).hom =
      (outerHornTargetMappingIso W).hom ≫ outerHornTargetForkMap q := by
  apply pullback.hom_ext
  · simp only [Category.assoc, outerHornTargetMappingIso_hom_fst,
      outerHornTargetForkMap_fst, outerHornTargetMappingIso_hom_fst_assoc]
    rw [← Category.assoc, ← (discreteSourceMappingMap q).naturality,
      Category.assoc, outerHornTargetLeftMappingIso_natural]
  · simp only [Category.assoc, outerHornTargetMappingIso_hom_snd,
      outerHornTargetForkMap_snd, outerHornTargetMappingIso_hom_snd_assoc]
    rw [← Category.assoc, ← (discreteSourceMappingMap q).naturality,
      Category.assoc, outerHornTargetRightMappingIso_natural]

/-- The genuine whole inverse preserves the same original target map. -/
theorem outerHornTargetMappingIso_inv_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    outerHornTargetForkMap q ≫ (outerHornTargetMappingIso V).inv =
      (outerHornTargetMappingIso W).inv ≫
        (discreteSourceMappingMap q).app (op (outerHornTarget.{u} : SSet.{u})) := by
  apply (cancel_mono (outerHornTargetMappingIso V).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [outerHornTargetMappingIso_natural, Iso.inv_hom_id_assoc]

/-- Every inner operator is retained by the full horn isomorphism. -/
theorem outerHornTargetMappingIso_operator (W : SimplicialSpace.{u})
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    ((discreteSourceMapping W).obj (op (outerHornTarget.{u} : SSet.{u}))).map α ≫
        (outerHornTargetMappingIso W).hom.app m =
      (outerHornTargetMappingIso W).hom.app n ≫ (outerHornTargetFork W).map α :=
  (outerHornTargetMappingIso W).hom.naturality α

/-- Every inner operator is retained by the genuine inverse. -/
theorem outerHornTargetMappingIso_inv_operator (W : SimplicialSpace.{u})
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    (outerHornTargetFork W).map α ≫ (outerHornTargetMappingIso W).inv.app m =
      (outerHornTargetMappingIso W).inv.app n ≫
        ((discreteSourceMapping W).obj (op (outerHornTarget.{u} : SSet.{u}))).map α :=
  (outerHornTargetMappingIso W).inv.naturality α

end SimplicialSpace


namespace SimplicialSpace.SegalHomotopy

/-- The original02/12 prescribed pair shares the same targetz. -/
def triangleTargetShearPair (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x z ⨯ mappingFibre W y z ⟶ outerHornTargetFork W :=
  pullback.lift (prod.fst ≫ mappingFibre.fst W x z)
    (prod.snd ≫ mappingFibre.fst W y z) (by
      have h : (prod.fst : mappingFibre W x z ⨯ mappingFibre W y z ⟶ _) ≫
          mappingFibre.snd W x z = prod.snd ≫ mappingFibre.snd W y z :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      simpa only [Category.assoc, mappingFibre.target_eq] using
        congrArg (fun f => f ≫ SSet.yonedaEquiv.symm z) h)

/-- The first original prescribed target-fork edge is02. -/
@[reassoc]
theorem triangleTargetShearPair_fst (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleTargetShearPair W x y z ≫ pullback.fst _ _ =
      prod.fst ≫ mappingFibre.fst W x z := pullback.lift_fst _ _ _

/-- The second original prescribed target-fork edge is12. -/
@[reassoc]
theorem triangleTargetShearPair_snd (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleTargetShearPair W x y z ≫ pullback.snd _ _ =
      prod.snd ≫ mappingFibre.fst W y z := pullback.lift_snd _ _ _

/-- The actual raw target pullback retains its whole W2 simplex and prescribed02/12 pair. -/
abbrev triangleTargetShearPullback (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  pullback (outerHornTargetComparison W) (triangleTargetShearPair W x y z)

/-- The original whole W2 projection of the target pullback. -/
abbrev triangleTargetShearPullbackProjection (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleTargetShearPullback W x y z ⟶ W.diagram _⦋2⦌ := pullback.fst _ _

/-- The original whole02/12 product projection of the target pullback. -/
abbrev triangleTargetShearPullbackPair (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleTargetShearPullback W x y z ⟶ mappingFibre W x z ⨯ mappingFibre W y z :=
  pullback.snd _ _

/-- The exact original target-pullback matching equation. -/
@[reassoc]
theorem triangleTargetShearPullback_condition (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleTargetShearPullbackProjection W x y z ≫ outerHornTargetComparison W =
      triangleTargetShearPullbackPair W x y z ≫ triangleTargetShearPair W x y z :=
  pullback.condition

/-- The original d1 face is the prescribed middle02 edge. -/
@[reassoc]
theorem triangleTargetShearPullback_first (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleTargetShearPullbackProjection W x y z ≫ W.diagram.δ (1 : Fin 3) =
      triangleTargetShearPullbackPair W x y z ≫ prod.fst ≫ mappingFibre.fst W x z := by
  simpa only [Category.assoc, outerHornTargetComparison_fst, triangleTargetShearPair_fst] using
    congrArg (fun f => f ≫ pullback.fst _ _) (triangleTargetShearPullback_condition W x y z)

/-- The original d0 face is the prescribed last12 edge. -/
@[reassoc]
theorem triangleTargetShearPullback_last (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleTargetShearPullbackProjection W x y z ≫ W.diagram.δ (0 : Fin 3) =
      triangleTargetShearPullbackPair W x y z ≫ prod.snd ≫ mappingFibre.fst W y z := by
  simpa only [Category.assoc, outerHornTargetComparison_snd, triangleTargetShearPair_snd] using
    congrArg (fun f => f ≫ pullback.snd _ _) (triangleTargetShearPullback_condition W x y z)

/-- The actual middle-last comparison of the original prescribed triangle. -/
def triangleTargetShear (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleSpace W x y z ⟶ mappingFibre W x z ⨯ mappingFibre W y z :=
  prod.lift (triangleMiddle W x y z) (triangleComparison W x y z ≫ prod.snd)

/-- The first shear projection is the original triangle middle02. -/
@[reassoc]
theorem triangleTargetShear_fst (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleTargetShear W x y z ≫ prod.fst = triangleMiddle W x y z := prod.lift_fst _ _

/-- The second shear projection is the original triangle last12. -/
@[reassoc]
theorem triangleTargetShear_snd (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleTargetShear W x y z ≫ prod.snd = triangleComparison W x y z ≫ prod.snd :=
  prod.lift_snd _ _

private def targetToPullback (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleSpace W x y z ⟶ triangleTargetShearPullback W x y z :=
  pullback.lift (triangleProjection W x y z) (triangleTargetShear W x y z) (by
    apply pullback.hom_ext
    · simp only [Category.assoc, outerHornTargetComparison_fst, triangleTargetShearPair_fst,
        triangleTargetShear_fst_assoc, triangleMiddle_fst]
    · simp only [Category.assoc, outerHornTargetComparison_snd, triangleTargetShearPair_snd,
        triangleTargetShear_snd_assoc, triangleProjection_last])

@[reassoc]
private theorem targetToPullback_projection (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    targetToPullback W x y z ≫ triangleTargetShearPullbackProjection W x y z =
      triangleProjection W x y z := pullback.lift_fst _ _ _

@[reassoc]
private theorem targetToPullback_pair (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    targetToPullback W x y z ≫ triangleTargetShearPullbackPair W x y z =
      triangleTargetShear W x y z := pullback.lift_snd _ _ _

private theorem targetFirst_sourceFace (W : SimplicialSpace.{u}) :
    W.diagram.δ (2 : Fin 3) ≫ W.diagram.δ (1 : Fin 2) =
      W.diagram.δ (1 : Fin 3) ≫ W.diagram.δ (1 : Fin 2) :=
  W.diagram.δ_comp_δ (i := (1 : Fin 2)) (j := (1 : Fin 2)) (by decide)

private theorem targetFirst_targetFace (W : SimplicialSpace.{u}) :
    W.diagram.δ (2 : Fin 3) ≫ W.diagram.δ (0 : Fin 2) =
      W.diagram.δ (0 : Fin 3) ≫ W.diagram.δ (1 : Fin 2) :=
  W.diagram.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)

/-- Recover the original missing first01 edge from the WHOLE W2 simplex by d2. -/
def triangleTargetRecoveredFirst (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleTargetShearPullback W x y z ⟶ mappingFibre W x y :=
  pullback.lift (triangleTargetShearPullbackProjection W x y z ≫ W.diagram.δ (2 : Fin 3))
    (triangleTargetShearPullbackPair W x y z ≫ prod.fst ≫ mappingFibre.snd W x z) (by
      apply prod.hom_ext
      · simp only [Category.assoc, mappingEndpoint_fst, mappingPointPair_fst]
        rw [targetFirst_sourceFace, triangleTargetShearPullback_first_assoc, mappingFibre.source_eq]
      · simp only [Category.assoc, mappingEndpoint_snd, mappingPointPair_snd]
        rw [targetFirst_targetFace, triangleTargetShearPullback_last_assoc, mappingFibre.source_eq]
        have h : triangleTargetShearPullbackPair W x y z ≫ prod.snd ≫ mappingFibre.snd W y z =
            triangleTargetShearPullbackPair W x y z ≫ prod.fst ≫ mappingFibre.snd W x z :=
          SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫ SSet.yonedaEquiv.symm y) h)

/-- The recovered first01 edge retains precisely the original W2 d2. -/
@[reassoc]
theorem triangleTargetRecoveredFirst_fst (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleTargetRecoveredFirst W x y z ≫ mappingFibre.fst W x y =
      triangleTargetShearPullbackProjection W x y z ≫ W.diagram.δ (2 : Fin 3) :=
  pullback.lift_fst _ _ _

/-- The recovered first01 keeps the ORIGINAL common point from the02 fibre. -/
@[reassoc]
theorem triangleTargetRecoveredFirst_snd (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleTargetRecoveredFirst W x y z ≫ mappingFibre.snd W x y =
      triangleTargetShearPullbackPair W x y z ≫ prod.fst ≫ mappingFibre.snd W x z :=
  pullback.lift_snd _ _ _

private def targetFromPullback (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleTargetShearPullback W x y z ⟶ triangleSpace W x y z :=
  pullback.lift (triangleTargetShearPullbackProjection W x y z)
    (prod.lift (triangleTargetRecoveredFirst W x y z)
      (triangleTargetShearPullbackPair W x y z ≫ prod.snd)) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst,
          prod.lift_fst_assoc, triangleTargetRecoveredFirst_fst]
      · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd, prod.lift_snd_assoc]
        exact triangleTargetShearPullback_last W x y z)

@[reassoc]
private theorem targetFromPullback_projection (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    targetFromPullback W x y z ≫ triangleProjection W x y z =
      triangleTargetShearPullbackProjection W x y z := pullback.lift_fst _ _ _

@[reassoc]
private theorem targetFromPullback_comparison (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    targetFromPullback W x y z ≫ triangleComparison W x y z =
      prod.lift (triangleTargetRecoveredFirst W x y z)
        (triangleTargetShearPullbackPair W x y z ≫ prod.snd) := pullback.lift_snd _ _ _

@[reassoc]
private theorem targetFromPullback_first (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    targetFromPullback W x y z ≫ triangleComparison W x y z ≫ prod.fst =
      triangleTargetRecoveredFirst W x y z := by
  rw [← Category.assoc, targetFromPullback_comparison, prod.lift_fst]

@[reassoc]
private theorem targetFromPullback_last (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    targetFromPullback W x y z ≫ triangleComparison W x y z ≫ prod.snd =
      triangleTargetShearPullbackPair W x y z ≫ prod.snd := by
  rw [← Category.assoc, targetFromPullback_comparison, prod.lift_snd]

private theorem targetToPullback_recoveredFirst (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    targetToPullback W x y z ≫ triangleTargetRecoveredFirst W x y z =
      triangleComparison W x y z ≫ prod.fst := by
  apply pullback.hom_ext (f := mappingEndpoint W) (g := mappingPointPair W x y)
  · change targetToPullback W x y z ≫ triangleTargetRecoveredFirst W x y z ≫
      mappingFibre.fst W x y =
      triangleComparison W x y z ≫ prod.fst ≫ mappingFibre.fst W x y
    rw [triangleTargetRecoveredFirst_fst, targetToPullback_projection_assoc,
        triangleProjection_first]
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem targetFromPullback_middle (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    targetFromPullback W x y z ≫ triangleMiddle W x y z =
      triangleTargetShearPullbackPair W x y z ≫ prod.fst := by
  apply pullback.hom_ext (f := mappingEndpoint W) (g := mappingPointPair W x z)
  · change targetFromPullback W x y z ≫ triangleMiddle W x y z ≫ mappingFibre.fst W x z =
      triangleTargetShearPullbackPair W x y z ≫ prod.fst ≫ mappingFibre.fst W x z
    rw [triangleMiddle_fst, targetFromPullback_projection_assoc]
    exact triangleTargetShearPullback_first W x y z
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The whole original T and target pullback are actually isomorphic for ANY W. -/
def triangleTargetShearIso (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleSpace W x y z ≅ triangleTargetShearPullback W x y z where
  hom := targetToPullback W x y z
  inv := targetFromPullback W x y z
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, targetFromPullback_projection,
        targetToPullback_projection, Category.id_comp]
    · apply prod.hom_ext
      · simp only [Category.assoc, targetFromPullback_first,
          targetToPullback_recoveredFirst, Category.id_comp]
      · simp only [Category.assoc, targetFromPullback_last,
          targetToPullback_pair_assoc, triangleTargetShear_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, targetToPullback_projection,
        targetFromPullback_projection, Category.id_comp]
    · apply prod.hom_ext
      · simp only [Category.assoc, targetToPullback_pair, triangleTargetShear_fst,
          targetFromPullback_middle, Category.id_comp]
      · simp only [Category.assoc, targetToPullback_pair, triangleTargetShear_snd,
          targetFromPullback_last, Category.id_comp]

/-- The forward isomorphism retains the ENTIRE original W2 simplex. -/
@[reassoc]
theorem triangleTargetShearIso_hom_projection (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    (triangleTargetShearIso W x y z).hom ≫ triangleTargetShearPullbackProjection W x y z =
      triangleProjection W x y z := targetToPullback_projection W x y z

/-- Its whole product projection is precisely the original middle-last shear. -/
@[reassoc]
theorem triangleTargetShearIso_hom_pair (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    (triangleTargetShearIso W x y z).hom ≫ triangleTargetShearPullbackPair W x y z =
      triangleTargetShear W x y z := targetToPullback_pair W x y z

/-- The inverse isomorphism retains the same ENTIRE original W2 simplex. -/
@[reassoc]
theorem triangleTargetShearIso_inv_projection (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    (triangleTargetShearIso W x y z).inv ≫ triangleProjection W x y z =
      triangleTargetShearPullbackProjection W x y z := targetFromPullback_projection W x y z

/-- The inverse recovers the missing original first01 mapping fibre. -/
@[reassoc]
theorem triangleTargetShearIso_inv_first (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    (triangleTargetShearIso W x y z).inv ≫ triangleComparison W x y z ≫ prod.fst =
      triangleTargetRecoveredFirst W x y z := targetFromPullback_first W x y z

/-- The inverse retains the prescribed original last12 mapping fibre. -/
@[reassoc]
theorem triangleTargetShearIso_inv_last (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    (triangleTargetShearIso W x y z).inv ≫ triangleComparison W x y z ≫ prod.snd =
      triangleTargetShearPullbackPair W x y z ≫ prod.snd := targetFromPullback_last W x y z

/-- The inverse retains the prescribed original middle02 mapping fibre. -/
@[reassoc]
theorem triangleTargetShearIso_inv_middle (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    (triangleTargetShearIso W x y z).inv ≫ triangleMiddle W x y z =
      triangleTargetShearPullbackPair W x y z ≫ prod.fst := targetFromPullback_middle W x y z


private def targetTriangleMatchingMap {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    twoEdgePullback W ⟶ twoEdgePullback V :=
  pullback.map _ _ _ _ (q.hom.app (op ⦋1⦌)) (q.hom.app (op ⦋1⦌))
    (q.hom.app (op ⦋0⦌))
    (q.hom.naturality (SimplexCategory.δ (0 : Fin 2)).op)
    (q.hom.naturality (SimplexCategory.δ (1 : Fin 2)).op)

@[reassoc]
private theorem targetTriangleMatchingMap_fst {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    targetTriangleMatchingMap q ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ q.hom.app (op ⦋1⦌) := pullback.lift_fst _ _ _

@[reassoc]
private theorem targetTriangleMatchingMap_snd {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    targetTriangleMatchingMap q ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ q.hom.app (op ⦋1⦌) := pullback.lift_snd _ _ _

private theorem targetTriangleComparison_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    twoEdgeComparison W ≫ targetTriangleMatchingMap q =
      q.hom.app (op ⦋2⦌) ≫ twoEdgeComparison V := by
  apply pullback.hom_ext
  · simp only [Category.assoc, targetTriangleMatchingMap_fst, twoEdgeComparison_fst,
      twoEdgeComparison_fst_assoc]
    exact q.hom.naturality (SimplexCategory.δ (2 : Fin 3)).op
  · simp only [Category.assoc, targetTriangleMatchingMap_snd, twoEdgeComparison_snd,
      twoEdgeComparison_snd_assoc]
    exact q.hom.naturality (SimplexCategory.δ (0 : Fin 3)).op

section Transport
variable {W V : SimplicialSpace.{u}} (q : W ⟶ V)
  {x y z : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' z' : (V.diagram _⦋0⦌) _⦋0⦌}

private theorem targetTrianglePair_natural (hx : mappingVertexMap q x = x')
    (hy : mappingVertexMap q y = y') (hz : mappingVertexMap q z = z') :
    twoEdgePair W x y z ≫ targetTriangleMatchingMap q =
      prod.map (mappingFibre.map q hx hy) (mappingFibre.map q hy hz) ≫ twoEdgePair V x' y' z' := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, targetTriangleMatchingMap_fst, targetTriangleMatchingMap_snd,
      twoEdgePair_fst, twoEdgePair_snd, twoEdgePair_fst_assoc, twoEdgePair_snd_assoc,
      prod.map_fst_assoc, prod.map_snd_assoc, mappingFibre.map_fst]

/-- OWN whole original triangle transport, with explicitly prescribed target vertices. -/
def triangleTargetTransport (hx : mappingVertexMap q x = x')
    (hy : mappingVertexMap q y = y') (hz : mappingVertexMap q z = z') :
    triangleSpace W x y z ⟶ triangleSpace V x' y' z' :=
  pullback.map _ _ _ _ (q.hom.app (op ⦋2⦌))
    (prod.map (mappingFibre.map q hx hy) (mappingFibre.map q hy hz)) (targetTriangleMatchingMap q)
    (targetTriangleComparison_natural q) (targetTrianglePair_natural q hx hy hz)

/-- The public triangle transport retains its ENTIRE original W2 projection. -/
@[reassoc]
theorem triangleTargetTransport_projection (hx : mappingVertexMap q x = x')
    (hy : mappingVertexMap q y = y') (hz : mappingVertexMap q z = z') :
    triangleTargetTransport q hx hy hz ≫ triangleProjection V x' y' z' =
      triangleProjection W x y z ≫ q.hom.app (op ⦋2⦌) := pullback.lift_fst _ _ _

/-- The public triangle transport retains BOTH original consecutive mapping fibres. -/
@[reassoc]
theorem triangleTargetTransport_comparison (hx : mappingVertexMap q x = x')
    (hy : mappingVertexMap q y = y') (hz : mappingVertexMap q z = z') :
    triangleTargetTransport q hx hy hz ≫ triangleComparison V x' y' z' =
      triangleComparison W x y z ≫
        prod.map (mappingFibre.map q hx hy) (mappingFibre.map q hy hz) := pullback.lift_snd _ _ _

/-- OWN original middle-face naturality, without a private triangle provider. -/
@[reassoc]
theorem triangleTargetTransport_middle (hx : mappingVertexMap q x = x')
    (hy : mappingVertexMap q y = y') (hz : mappingVertexMap q z = z') :
    triangleTargetTransport q hx hy hz ≫ triangleMiddle V x' y' z' =
      triangleMiddle W x y z ≫ mappingFibre.map q hx hz := by
  apply pullback.hom_ext (f := mappingEndpoint V) (g := mappingPointPair V x' z')
  · change triangleTargetTransport q hx hy hz ≫ triangleMiddle V x' y' z' ≫
        mappingFibre.fst V x' z' = triangleMiddle W x y z ≫ mappingFibre.map q hx hz ≫
          mappingFibre.fst V x' z'
    rw [triangleMiddle_fst, triangleTargetTransport_projection_assoc,
      mappingFibre.map_fst, triangleMiddle_fst_assoc]
    exact congrArg (fun f => triangleProjection W x y z ≫ f)
      (q.hom.naturality (SimplexCategory.δ (1 : Fin 3)).op).symm
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The original target pair is natural in BOTH explicitly moved mapping fibres. -/
@[reassoc]
theorem triangleTargetShearPair_natural (hx : mappingVertexMap q x = x')
    (hy : mappingVertexMap q y = y') (hz : mappingVertexMap q z = z') :
    triangleTargetShearPair W x y z ≫ outerHornTargetForkMap q =
      prod.map (mappingFibre.map q hx hz) (mappingFibre.map q hy hz) ≫
        triangleTargetShearPair V x' y' z' := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, outerHornTargetForkMap_fst, outerHornTargetForkMap_snd,
      triangleTargetShearPair_fst, triangleTargetShearPair_snd,
      triangleTargetShearPair_fst_assoc, triangleTargetShearPair_snd_assoc,
      prod.map_fst_assoc, prod.map_snd_assoc, mappingFibre.map_fst]

/-- OWN whole original Rlast transport, retaining W2 and its02/12 pair. -/
def triangleTargetShearPullbackMap (hx : mappingVertexMap q x = x')
    (hy : mappingVertexMap q y = y') (hz : mappingVertexMap q z = z') :
    triangleTargetShearPullback W x y z ⟶ triangleTargetShearPullback V x' y' z' :=
  pullback.map _ _ _ _ (q.hom.app (op ⦋2⦌))
    (prod.map (mappingFibre.map q hx hz) (mappingFibre.map q hy hz)) (outerHornTargetForkMap q)
    (outerHornTargetComparison_natural q) (triangleTargetShearPair_natural q hx hy hz)

/-- The public Rlast map retains the ENTIRE original W2 simplex. -/
@[reassoc]
theorem triangleTargetShearPullbackMap_projection (hx : mappingVertexMap q x = x')
    (hy : mappingVertexMap q y = y') (hz : mappingVertexMap q z = z') :
    triangleTargetShearPullbackMap q hx hy hz ≫ triangleTargetShearPullbackProjection V x' y' z' =
      triangleTargetShearPullbackProjection W x y z ≫ q.hom.app (op ⦋2⦌) := pullback.lift_fst _ _ _

/-- The public Rlast map retains BOTH original prescribed02/12 fibres. -/
@[reassoc]
theorem triangleTargetShearPullbackMap_pair (hx : mappingVertexMap q x = x')
    (hy : mappingVertexMap q y = y') (hz : mappingVertexMap q z = z') :
    triangleTargetShearPullbackMap q hx hy hz ≫ triangleTargetShearPullbackPair V x' y' z' =
      triangleTargetShearPullbackPair W x y z ≫
        prod.map (mappingFibre.map q hx hz) (mappingFibre.map q hy hz) := pullback.lift_snd _ _ _

/-- The SAME raw middle-last map preserves every original moved-vertex square. -/
@[reassoc]
theorem triangleTargetShear_natural (hx : mappingVertexMap q x = x')
    (hy : mappingVertexMap q y = y') (hz : mappingVertexMap q z = z') :
    triangleTargetTransport q hx hy hz ≫ triangleTargetShear V x' y' z' =
      triangleTargetShear W x y z ≫ prod.map (mappingFibre.map q hx hz)
          (mappingFibre.map q hy hz) := by
  apply prod.hom_ext
  · simp only [Category.assoc, triangleTargetShear_fst, triangleTargetTransport_middle,
      prod.map_fst, triangleTargetShear_fst_assoc]
  · simp only [Category.assoc, triangleTargetShear_snd, triangleTargetTransport_comparison_assoc,
      prod.map_snd, triangleTargetShear_snd_assoc]

/-- The WHOLE raw T/Rlast isomorphism is natural on both original projections. -/
@[reassoc]
theorem triangleTargetShearIso_natural (hx : mappingVertexMap q x = x')
    (hy : mappingVertexMap q y = y') (hz : mappingVertexMap q z = z') :
    triangleTargetTransport q hx hy hz ≫ (triangleTargetShearIso V x' y' z').hom =
      (triangleTargetShearIso W x y z).hom ≫ triangleTargetShearPullbackMap q hx hy hz := by
  apply pullback.hom_ext
  · change triangleTargetTransport q hx hy hz ≫ (triangleTargetShearIso V x' y' z').hom ≫
        triangleTargetShearPullbackProjection V x' y' z' =
      (triangleTargetShearIso W x y z).hom ≫ triangleTargetShearPullbackMap q hx hy hz ≫
        triangleTargetShearPullbackProjection V x' y' z'
    simp only [triangleTargetShearIso_hom_projection, triangleTargetTransport_projection,
      triangleTargetShearPullbackMap_projection, triangleTargetShearIso_hom_projection_assoc]
  · change triangleTargetTransport q hx hy hz ≫ (triangleTargetShearIso V x' y' z').hom ≫
        triangleTargetShearPullbackPair V x' y' z' =
      (triangleTargetShearIso W x y z).hom ≫ triangleTargetShearPullbackMap q hx hy hz ≫
        triangleTargetShearPullbackPair V x' y' z'
    simp only [triangleTargetShearIso_hom_pair, triangleTargetShearPullbackMap_pair,
      triangleTargetShearIso_hom_pair_assoc, triangleTargetShear_natural]

/-- The WHOLE inverse naturality retains those SAME original moved vertices. -/
@[reassoc]
theorem triangleTargetShearIso_inv_natural (hx : mappingVertexMap q x = x')
    (hy : mappingVertexMap q y = y') (hz : mappingVertexMap q z = z') :
    triangleTargetShearPullbackMap q hx hy hz ≫ (triangleTargetShearIso V x' y' z').inv =
      (triangleTargetShearIso W x y z).inv ≫ triangleTargetTransport q hx hy hz := by
  apply (cancel_mono (triangleTargetShearIso V x' y' z').hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    triangleTargetShearIso_natural, Iso.inv_hom_id_assoc]

end Transport

/-- Every original inner operator is retained by the actual whole target isomorphism. -/
theorem triangleTargetShearIso_operator (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    (triangleSpace W x y z).map α ≫ (triangleTargetShearIso W x y z).hom.app m =
      (triangleTargetShearIso W x y z).hom.app n ≫ (triangleTargetShearPullback W x y z).map α :=
  (triangleTargetShearIso W x y z).hom.naturality α

/-- Every original inner operator is retained by its SAME whole inverse. -/
theorem triangleTargetShearIso_inv_operator (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    (triangleTargetShearPullback W x y z).map α ≫ (triangleTargetShearIso W x y z).inv.app m =
      (triangleTargetShearIso W x y z).inv.app n ≫ (triangleSpace W x y z).map α :=
  (triangleTargetShearIso W x y z).inv.naturality α

end SimplicialSpace.SegalHomotopy
