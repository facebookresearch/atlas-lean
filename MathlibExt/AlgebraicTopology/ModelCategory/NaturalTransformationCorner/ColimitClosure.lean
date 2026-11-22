/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.NaturalTransformationCorner.Stability
public import MathlibExt.AlgebraicTopology.ModelCategory.WeakArrowColimits
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Colimit closure of natural-transformation corners

Colimits of a natural transformation are represented by colimits in the
arrow category using both source and target cocones. If the corner functor
preserves the diagram shape and weak equivalences are stable under its
colimits, objectwise weak corners give a weak corner on the colimit comparison
map. Adding h-cofibration conditions on both mapped source arrows gives a
guarded property closed under composition, cobase change and suitable
connected or filtered colimits under the stated preservation and properness
hypotheses. Weak corners also pass along source-arrow retracts, and the guarded
property is stable under transfinite composition.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC uD vD w w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty HomotopicalAlgebra

namespace HomotopicalAlgebra.NaturalTransformationCorner

variable {D : Type uD} [Category.{vD} D]
  {J : Type w} [Category.{w'} J]

/-- The whole original comparison diagram, before selecting either colimit. -/
def arrowDiagram {F G : J ⥤ D} (η : F ⟶ G) : J ⥤ Arrow D where
  obj j := Arrow.mk (η.app j)
  map f := Arrow.homMk (F.map f) (G.map f) (η.naturality f)
  map_id j := by
    apply Arrow.hom_ext
    · change F.map (𝟙 j) = 𝟙 (F.obj j)
      exact F.map_id j
    · change G.map (𝟙 j) = 𝟙 (G.obj j)
      exact G.map_id j
  map_comp f g := by
    apply Arrow.hom_ext
    · change F.map (f ≫ g) = F.map f ≫ F.map g
      exact F.map_comp f g
    · change G.map (f ≫ g) = G.map f ≫ G.map g
      exact G.map_comp f g

/-- The original source and target cocones retain their entire comparison map. -/
def arrowCocone {F G : J ⥤ D} (η : F ⟶ G) (cF : Cocone F) (cG : Cocone G)
    (f : cF.pt ⟶ cG.pt) (hf : ∀ j, cF.ι.app j ≫ f = η.app j ≫ cG.ι.app j) :
    Cocone (arrowDiagram η) where
  pt := Arrow.mk f
  ι :=
    { app j := Arrow.homMk (cF.ι.app j) (cG.ι.app j) (hf j)
      naturality i j u := by
        apply Arrow.hom_ext
        · change F.map u ≫ cF.ι.app j = cF.ι.app i ≫ 𝟙 cF.pt
          exact cF.ι.naturality u
        · change G.map u ≫ cG.ι.app j = cG.ι.app i ≫ 𝟙 cG.pt
          exact cG.ι.naturality u }

/-- Both actual projected colimit proofs give the full original Arrow colimit. -/
def arrowCoconeIsColimit {F G : J ⥤ D} (η : F ⟶ G) (cF : Cocone F) (cG : Cocone G)
    (hcF : IsColimit cF) (hcG : IsColimit cG)
    (f : cF.pt ⟶ cG.pt) (hf : ∀ j, cF.ι.app j ≫ f = η.app j ≫ cG.ι.app j) :
    IsColimit (arrowCocone η cF cG f hf) := by
  apply Comma.fstSndJointlyReflectColimit (L := 𝟭 D) (R := 𝟭 D)
  · exact hcF
  · exact hcG

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [HasPushouts C] {P Q : D ⥤ C} (α : P ⟶ Q)

/-- The actual corner at the original colimit is weak under the source weak-comparison closure. -/
theorem corner_weak_of_actual_colimit
    [HasColimitsOfShape J C]
    [(weakEquivalences C).IsStableUnderColimitsOfShape J]
    [PreservesColimitsOfShape J (functor α)]
    {F G : J ⥤ D} (η : F ⟶ G) (cF : Cocone F) (cG : Cocone G)
    (hcF : IsColimit cF) (hcG : IsColimit cG)
    (f : cF.pt ⟶ cG.pt) (hf : ∀ j, cF.ι.app j ≫ f = η.app j ≫ cG.ι.app j)
    (hη : ∀ j, weakEquivalences C (corner α (Arrow.mk (η.app j)))) :
    weakEquivalences C (corner α (Arrow.mk f)) := by
  let c := arrowCocone η cF cG f hf
  let K := arrowDiagram η ⋙ functor α
  let d := (functor α).mapCocone c
  have hd : IsColimit d :=
    isColimitOfPreserves (functor α) (arrowCoconeIsColimit η cF cG hcF hcG f hf)
  exact HomotopicalAlgebra.WeakArrowColimits.of_actual_colimit (weakEquivalences C) K d hd hη

/-- The literal source morphism property whose value is weakness of its actual corner. -/
def weakProperty : MorphismProperty D := fun _ _ i => weakEquivalences C (corner α (Arrow.mk i))

/-- An isomorphism of entire source Arrows maps to the entire original corner Arrow isomorphism. -/
theorem weakProperty_respectsIso : (weakProperty α).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    intro a b e ha
    change weakEquivalences C ((functor α).obj a).hom at ha
    change weakEquivalences C ((functor α).obj b).hom
    exact ((weakEquivalences C).arrow_mk_iso_iff ((functor α).mapIso e)).mp ha)

/-- Base weak comparison closure is transported through the actual corner functor on Arrow colimits. -/
theorem weakProperty_isStableUnderColimitsOfShape
    [HasColimitsOfShape J C]
    [(weakEquivalences C).IsStableUnderColimitsOfShape J]
    [PreservesColimitsOfShape J (functor α)] :
    (weakProperty α).IsStableUnderColimitsOfShape J where
  condition F G cF cG hcF hcG η hη f hf :=
    corner_weak_of_actual_colimit α (F := F) (G := G) η cF cG hcF hcG f hf hη

/-- The initial identity corner is invertible through its actual pushout inclusion. -/
theorem corner_weak_identity (X : D) :
    weakEquivalences C (corner α (Arrow.mk (𝟙 X))) := by
  let : IsIso (P.map (𝟙 X)) := inferInstance
  let : IsIso (pushout.inl (α.app X) (P.map (𝟙 X))) :=
    (IsPushout.of_hasPushout (α.app X) (P.map (𝟙 X))).isIso_inl_of_isIso
  apply (weakEquivalences C).of_precomp
    (pushout.inl (α.app X) (P.map (𝟙 X))) (corner α (Arrow.mk (𝟙 X)))
    ((weakEquivalences C).of_isIso _)
  rw [inl_corner_mk α (𝟙 X)]
  exact (weakEquivalences C).of_isIso _

/-- Weak corner flatness retains both genuine mapped h-cofibration guards. -/
def guardedProperty : MorphismProperty D :=
  weakProperty α ⊓ ((hCofibrations C).inverseImage P ⊓ (hCofibrations C).inverseImage Q)

/-- All original source Arrow isomorphisms retain the complete weak/guarded corner property. -/
theorem guardedProperty_respectsIso : (guardedProperty α).RespectsIso := by
  let : (weakProperty α).RespectsIso := weakProperty_respectsIso α
  unfold guardedProperty
  infer_instance

/-- The actual corner factorization and mapped source composition prove the full guarded class law. -/
theorem guardedProperty_isMultiplicative [(hCofibrations C).IsMultiplicative] :
    (guardedProperty α).IsMultiplicative where
  id_mem X := by
    refine ⟨corner_weak_identity α X, ?_, ?_⟩
    · change hCofibrations C (P.map (𝟙 X))
      rw [P.map_id]
      exact (hCofibrations C).id_mem _
    · change hCofibrations C (Q.map (𝟙 X))
      rw [Q.map_id]
      exact (hCofibrations C).id_mem _
  comp_mem i j hi hj := by
    refine ⟨corner_weak_composition α i j hi.1 hj.1 hj.2.1, ?_, ?_⟩
    · change hCofibrations C (P.map (i ≫ j))
      rw [P.map_comp]
      exact (hCofibrations C).comp_mem _ _ hi.2.1 hj.2.1
    · change hCofibrations C (Q.map (i ≫ j))
      rw [Q.map_comp]
      exact (hCofibrations C).comp_mem _ _ hi.2.2 hj.2.2

/-- Actual source cobase changes preserve the weak corner and both mapped h-cofibration guards. -/
theorem guardedProperty_isStableUnderCobaseChange [IsLeftProper C]
    [PreservesColimitsOfShape WalkingSpan P] [PreservesColimitsOfShape WalkingSpan Q] :
    (guardedProperty α).IsStableUnderCobaseChange where
  of_isPushout sq hi :=
    ⟨corner_weak_cobase α sq.flip hi.1 hi.2.1 hi.2.2,
      (hCofibrations C).of_isPushout (sq.map P) hi.2.1,
      (hCofibrations C).of_isPushout (sq.map Q) hi.2.2⟩

/-- Both mapped original cocones retain the guarded corner class through controlled colimits. -/
theorem guardedProperty_isStableUnderColimitsOfShape
    [IsConnected J] [HasColimitsOfShape J C]
    [(weakEquivalences C).IsStableUnderColimitsOfShape J]
    [PreservesColimitsOfShape J P] [PreservesColimitsOfShape J Q]
    [PreservesColimitsOfShape J (functor α)] :
    (guardedProperty α).IsStableUnderColimitsOfShape J := by
  let : (hCofibrations C).IsStableUnderColimitsOfShape J :=
    HomotopicalAlgebra.HCofibrationFilteredColimits.hCof_isStableUnderColimitsOfShape (J := J)
  constructor
  intro F G cF cG hcF hcG η hη f hf
  refine ⟨corner_weak_of_actual_colimit α η cF cG hcF hcG f hf (fun j => (hη j).1), ?_, ?_⟩
  · exact MorphismProperty.IsStableUnderColimitsOfShape.condition
      (W := hCofibrations C) (J := J) (F ⋙ P) (G ⋙ P)
      (P.mapCocone cF) (P.mapCocone cG)
      (isColimitOfPreserves P hcF) (isColimitOfPreserves P hcG)
      (Functor.whiskerRight η P) (fun j => (hη j).2.1) (P.map f) (fun j => by
        change P.map (cF.ι.app j) ≫ P.map f = P.map (η.app j) ≫ P.map (cG.ι.app j)
        rw [← P.map_comp, ← P.map_comp]
        exact congrArg P.map (hf j))
  · exact MorphismProperty.IsStableUnderColimitsOfShape.condition
      (W := hCofibrations C) (J := J) (F ⋙ Q) (G ⋙ Q)
      (Q.mapCocone cF) (Q.mapCocone cG)
      (isColimitOfPreserves Q hcF) (isColimitOfPreserves Q hcG)
      (Functor.whiskerRight η Q) (fun j => (hη j).2.2) (Q.map f) (fun j => by
        change Q.map (cF.ι.app j) ≫ Q.map f = Q.map (η.app j) ≫ Q.map (cG.ι.app j)
        rw [← Q.map_comp, ← Q.map_comp]
        exact congrArg Q.map (hf j))

/-- The original base filtered weak comparison class supplies the entire guarded filtered class. -/
theorem guardedProperty_isStableUnderFilteredColimits
    [HasColimitsOfSize.{w, w} C]
    [(weakEquivalences C).IsStableUnderFilteredColimits.{w, w}]
    [PreservesColimitsOfSize.{w, w} P] [PreservesColimitsOfSize.{w, w} Q]
    [PreservesColimitsOfSize.{w, w} (functor α)] :
    (guardedProperty α).IsStableUnderFilteredColimits.{w, w} where
  isStableUnderColimitsOfShape K _ _ := by
    let : IsConnected K := IsFiltered.isConnected K
    exact guardedProperty_isStableUnderColimitsOfShape α

/-- Multiplication plus genuine filtered weak comparisons give the full source-universe transfinite class. -/
theorem guardedProperty_isStableUnderTransfiniteComposition
    [HasColimitsOfSize.{w, w} C]
    [(weakEquivalences C).IsStableUnderFilteredColimits.{w, w}]
    [(hCofibrations C).IsMultiplicative]
    [PreservesColimitsOfSize.{w, w} P] [PreservesColimitsOfSize.{w, w} Q]
    [PreservesColimitsOfSize.{w, w} (functor α)] :
    (guardedProperty α).IsStableUnderTransfiniteComposition.{w} := by
  let : (guardedProperty α).RespectsIso := guardedProperty_respectsIso α
  let : (guardedProperty α).IsMultiplicative := guardedProperty_isMultiplicative α
  let : (guardedProperty α).IsStableUnderFilteredColimits.{w, w} :=
    guardedProperty_isStableUnderFilteredColimits α
  infer_instance

/-- The complete source Arrow retract maps through the actual corner functor. -/
def cornerArrowRetract {X Y X' Y' : D} {i : X ⟶ Y} {j : X' ⟶ Y'}
    (r : RetractArrow i j) :
    RetractArrow (corner α (Arrow.mk i)) (corner α (Arrow.mk j)) where
  i := (functor α).map r.i
  r := (functor α).map r.r
  retract := by
    change (functor α).map r.i ≫ (functor α).map r.r = 𝟙 ((functor α).obj (Arrow.mk i))
    rw [← (functor α).map_comp, r.retract, (functor α).map_id]

/-- Weakness passes through the original whole source Arrow retract without h-cofibration retract premises. -/
theorem corner_weak_of_sourceRetract {X Y X' Y' : D} {i : X ⟶ Y} {j : X' ⟶ Y'}
    (r : RetractArrow i j) (hj : weakEquivalences C (corner α (Arrow.mk j))) :
    weakEquivalences C (corner α (Arrow.mk i)) :=
  (weakEquivalences C).of_retract (cornerArrowRetract α r) hj

end HomotopicalAlgebra.NaturalTransformationCorner
