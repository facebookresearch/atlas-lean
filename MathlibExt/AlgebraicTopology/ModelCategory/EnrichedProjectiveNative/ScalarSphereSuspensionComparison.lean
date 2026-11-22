/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.OriginalISuspensionComparison
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.IntervalModel
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSphereOne

/-!
# Sphere tensors and suspension of native enriched diagrams

Identifies tensoring by the pointed one-sphere with the disk-span pushout, retaining its
quotient maps and naturality. The weak disk-collapse and homotopy-pushout comparisons use
cofibrant diagrams and the supplied generator-cardinal bottom.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat MonoidalCategory
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.ScalarSphereSuspension

private abbrev S0 : PointedCGWH.{u, v} := (Arrow.mk PointedCGWH.diskBoundary.{u, v}).left

set_option backward.isDefEq.respectTransparency false in
private def sourceUnitIso : (𝟙_ PointedCGWH.{u, v}) ≅ S0.{u, v} := by
  change PointedCGWH.sphereZero.{u, v} ≅
    Under.mk (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ CGWH.point.{u, v})
  exact Under.isoMk (Iso.refl _) (by
    dsimp [PointedCGWH.sphereZero, CategoryTheory.Pointed.smashUnit]
    simp [Under.costar_obj_hom])

private theorem source_isCofibrant : IsCofibrant S0.{u, v} := by
  let _ : IsCofibrant (𝟙_ PointedCGWH.{u, v}) :=
    PointedCGWH.modelCategory.smashUnit_isCofibrant
  let _ : Cofibration sourceUnitIso.{u, v}.hom := by infer_instance
  exact isCofibrant_of_cofibration sourceUnitIso.{u, v}.hom

private theorem disk_isCofibrant : IsCofibrant PointedCGWH.diskOne.{u, v} := by
  let _ : IsCofibrant S0.{u, v} := source_isCofibrant
  let _ : Cofibration PointedCGWH.diskBoundary.{u, v} :=
    PointedCGWH.modelCategory.diskBoundary_cofibration
  exact isCofibrant_of_cofibration (X := S0.{u, v}) PointedCGWH.diskBoundary

private theorem terminal_isCofibrant : IsCofibrant (⊤_ PointedCGWH.{u, v}) := by
  rw [isCofibrant_iff_of_isInitial (𝟙 (⊤_ PointedCGWH.{u, v}))
    (((isZero_zero PointedCGWH.{u, v}).of_iso HasZeroObject.zeroIsoTerminal.symm).isInitial)]
  infer_instance

/-- The original disk quotient map to the pointed one-sphere, with its chosen cofiber leg. -/
def quotient : PointedCGWH.diskOne.{u, v} ⟶ PointedCGWH.sphereOne.{u, v} :=
  colimit.ι ((cofiberSpan (C := PointedCGWH.{u, v})).obj (Arrow.mk PointedCGWH.diskBoundary))
      WalkingSpan.left ≫
    PointedCGWH.diskCofiberIsoSphereOne.hom

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

private abbrev D := EnrichedFunctorCat PointedCGWH.{u, v} I
attribute [local instance] Native.modelCategory

private instance nativeFactorization :
    CategoryTheory.MorphismProperty.HasFunctorialFactorization
      (cofibrations (D (I := I))) (trivialFibrations (D (I := I))) :=
  (Native.functorialFactorizations (B := B) (A := I)).1

omit B in
private instance scalarPreservesColimits (X : D (I := I)) :
    PreservesColimits (WeightedEndVariance.tensorBifunctor.flip.obj X) :=
  (PointedCGWH.EnrichedFunctorMapping.tensorMappingAdjunction X).leftAdjoint_preservesColimits

omit B in
private def scalarUnitNatIso : EnrichedFunctorCat.tensorLeft (𝟙_ PointedCGWH.{u, v}) ≅
    𝟭 (D (I := I)) :=
  NatIso.ofComponents scalarUnitIso (by
    intro X Y f
    exact scalarUnitIso_naturality f)

omit B in
/-- Tensoring with the original disk-boundary source is naturally the identity functor. -/
def sourceTensorUnitIso : EnrichedFunctorCat.tensorLeft S0.{u, v} ≅ 𝟭 (D (I := I)) :=
  (EnrichedFunctorCat.tensorBifunctor (V := PointedCGWH.{u, v}) (A := I)).mapIso
      sourceUnitIso.symm ≪≫ scalarUnitNatIso

omit B in
/-- Tensoring the terminal coefficient yields the original native zero diagram. -/
def coefficientZeroIso (X : D (I := I)) :
    (WeightedEndVariance.tensorBifunctor.flip.obj X).obj (⊤_ PointedCGWH.{u, v}) ≅
      Diagrams.zeroDiagram := by
  apply IsZero.iso _ Diagrams.zeroDiagram_isZero
  apply EnrichedZeroCompletion.diagram_isZero_of_obj_isZero
  intro a
  exact EnrichedZeroCompletion.tensor_isZero_left
    ((isZero_zero PointedCGWH.{u, v}).of_iso HasZeroObject.zeroIsoTerminal.symm)
    (X.toEnrichedFunctor.obj a)

omit B in
/-- The scalar disk-boundary span with its original disk leg and map to native zero. -/
def diskSpan : D (I := I) ⥤ (WalkingSpan ⥤ D (I := I)) where
  obj X := span (scalarTensorMap PointedCGWH.diskBoundary X)
    (Diagrams.toZero (tensorLeftObject S0 X))
  map f := spanHomMk
    ((EnrichedFunctorCat.tensorLeft S0).map f)
    ((EnrichedFunctorCat.tensorLeft PointedCGWH.diskOne).map f)
    (𝟙 Diagrams.zeroDiagram)
    (scalarTensorMap_diagram_naturality PointedCGWH.diskBoundary f).symm
    (by
      change Diagrams.toZero _ ≫ 𝟙 Diagrams.zeroDiagram = _ ≫ Diagrams.toZero _
      rw [Category.comp_id]
      exact (Diagrams.toZero_naturality ((EnrichedFunctorCat.tensorLeft S0).map f)).symm)
  map_id X := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · exact (EnrichedFunctorCat.tensorLeft S0).map_id X
    · exact (EnrichedFunctorCat.tensorLeft PointedCGWH.diskOne).map_id X
    · rfl
  map_comp f g := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · exact (EnrichedFunctorCat.tensorLeft S0).map_comp f g
    · exact (EnrichedFunctorCat.tensorLeft PointedCGWH.diskOne).map_comp f g
    · exact (Category.id_comp _).symm

omit B in
/-- The scalar disk quotient and original zero leg form the actual one-sphere pushout. -/
theorem sphereScalarIsPushout (X : D (I := I)) :
    IsPushout (scalarTensorMap PointedCGWH.diskBoundary X)
      (Diagrams.toZero (tensorLeftObject S0 X))
      (scalarTensorMap quotient X)
      (Diagrams.zeroTo (tensorLeftObject PointedCGWH.sphereOne X)) := by
  let F := WeightedEndVariance.tensorBifunctor.flip.obj X
  let hBase := IsPushout.of_isColimit_cocone
    (colimit.isColimit ((cofiberSpan (C := PointedCGWH.{u, v})).obj
      (Arrow.mk PointedCGWH.diskBoundary)))
  let h := hBase.map F
  let eZ := coefficientZeroIso X
  let eC := F.mapIso PointedCGWH.diskCofiberIsoSphereOne
  apply h.of_iso (Iso.refl _) (Iso.refl _) eZ eC
  · change scalarTensorMap PointedCGWH.diskBoundary X ≫
        𝟙 (tensorLeftObject PointedCGWH.diskOne X) =
      𝟙 (tensorLeftObject S0 X) ≫ scalarTensorMap PointedCGWH.diskBoundary X
    rw [Category.id_comp, Category.comp_id]
  · exact Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  · change F.map (colimit.ι
        ((cofiberSpan (C := PointedCGWH.{u, v})).obj (Arrow.mk PointedCGWH.diskBoundary))
        WalkingSpan.left) ≫
        F.map PointedCGWH.diskCofiberIsoSphereOne.hom =
      𝟙 (tensorLeftObject PointedCGWH.diskOne X) ≫ scalarTensorMap quotient X
    rw [Category.id_comp]
    exact (F.map_comp _ _).symm
  · exact (Diagrams.zeroDiagram_isZero.of_iso eZ).isInitial.hom_ext _ _

omit B in
/-- The scalar disk-span colimit is canonically the scalar tensor with the one-sphere. -/
def sphereScalarColimitIso (X : D (I := I)) :
    colimit ((diskSpan (I := I)).obj X) ≅ tensorLeftObject PointedCGWH.sphereOne X :=
  (IsPushout.of_isColimit_cocone (colimit.isColimit ((diskSpan (I := I)).obj X))).isoIsPushout
    _ _ (sphereScalarIsPushout X)

omit B in
/-- The colimit comparison retains the original scalar disk quotient leg. -/
theorem sphereScalarColimitIso_inl (X : D (I := I)) :
    colimit.ι ((diskSpan (I := I)).obj X) WalkingSpan.left ≫
      (sphereScalarColimitIso X).hom = scalarTensorMap quotient X :=
  (IsPushout.of_isColimit_cocone
    (colimit.isColimit ((diskSpan (I := I)).obj X))).inl_isoIsPushout_hom
    _ _ (sphereScalarIsPushout X)

omit B in
/-- The colimit comparison retains the original native zero leg. -/
theorem sphereScalarColimitIso_inr (X : D (I := I)) :
    colimit.ι ((diskSpan (I := I)).obj X) WalkingSpan.right ≫
      (sphereScalarColimitIso X).hom = Diagrams.zeroTo (tensorLeftObject PointedCGWH.sphereOne X) :=
  (IsPushout.of_isColimit_cocone
    (colimit.isColimit ((diskSpan (I := I)).obj X))).inr_isoIsPushout_hom
    _ _ (sphereScalarIsPushout X)

omit B in
/-- The entire scalar colimit comparison is natural in the original diagram arrow. -/
theorem sphereScalarColimitIso_naturality {X Y : D (I := I)} (f : X ⟶ Y) :
    colim.map ((diskSpan (I := I)).map f) ≫ (sphereScalarColimitIso Y).hom =
      (sphereScalarColimitIso X).hom ≫
        tensorLeftMap PointedCGWH.sphereOne f := by
  apply (IsPushout.of_isColimit_cocone (colimit.isColimit ((diskSpan (I := I)).obj X))).hom_ext
  · have hm := ι_colimMap ((diskSpan (I := I)).map f) WalkingSpan.left
    change colimit.ι ((diskSpan (I := I)).obj X) WalkingSpan.left ≫
        colim.map ((diskSpan (I := I)).map f) =
      tensorLeftMap PointedCGWH.diskOne f ≫
        colimit.ι ((diskSpan (I := I)).obj Y) WalkingSpan.left at hm
    change colimit.ι ((diskSpan (I := I)).obj X) WalkingSpan.left ≫
        (colim.map ((diskSpan (I := I)).map f) ≫ (sphereScalarColimitIso Y).hom) =
      colimit.ι ((diskSpan (I := I)).obj X) WalkingSpan.left ≫
        ((sphereScalarColimitIso X).hom ≫ tensorLeftMap PointedCGWH.sphereOne f)
    rw [← Category.assoc, hm]
    have hy := Category.assoc (tensorLeftMap PointedCGWH.diskOne f)
      (colimit.ι ((diskSpan (I := I)).obj Y) WalkingSpan.left) (sphereScalarColimitIso Y).hom
    have hn := scalarTensorMap_diagram_naturality quotient f
    have hx := Category.assoc (colimit.ι ((diskSpan (I := I)).obj X) WalkingSpan.left)
      (sphereScalarColimitIso X).hom (tensorLeftMap PointedCGWH.sphereOne f)
    exact hy.trans
      ((congrArg (fun t => tensorLeftMap PointedCGWH.diskOne f ≫ t)
        (sphereScalarColimitIso_inl Y)).trans
        (hn.trans
          ((congrArg (fun t => t ≫ tensorLeftMap PointedCGWH.sphereOne f)
            (sphereScalarColimitIso_inl X).symm).trans hx)))
  · exact Diagrams.zeroDiagramIsInitial.hom_ext _ _

omit B in
/-- The actual scalar disk-span colimit agrees naturally with one-sphere tensor. -/
def sphereScalarNatIso : diskSpan (I := I) ⋙ colim ≅
    EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne :=
  NatIso.ofComponents sphereScalarColimitIso (by
    intro X Y f
    exact sphereScalarColimitIso_naturality f)

omit B in
/-- Contract the scalar disk leg while keeping the original source and zero endpoint. -/
def diskToZeroSpan : diskSpan (I := I) ⟶
    EnrichedFunctorCat.tensorLeft S0 ⋙ OriginalISuspension.zeroSpan (I := I) where
  app X := spanHomMk (𝟙 (tensorLeftObject S0 X))
    (Diagrams.toZero (tensorLeftObject PointedCGWH.diskOne X)) (𝟙 Diagrams.zeroDiagram)
    (Diagrams.zeroDiagramIsTerminal.hom_ext _ _)
    (Diagrams.zeroDiagramIsTerminal.hom_ext _ _)
  naturality X Y f := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · change (EnrichedFunctorCat.tensorLeft S0).map f ≫ 𝟙 _ =
        𝟙 _ ≫ (EnrichedFunctorCat.tensorLeft S0).map f
      simp
    · exact Diagrams.zeroDiagramIsTerminal.hom_ext _ _
    · rfl

/-- For a cofibrant diagram, the scalar disk collapse to original native zero is weak. -/
theorem diskCollapse_weak (X : D (I := I)) [IsCofibrant X] :
    WeakEquivalence (Diagrams.toZero (tensorLeftObject PointedCGWH.diskOne X)) := by
  let F := WeightedEndVariance.tensorBifunctor.flip.obj X
  let _ : IsCofibrant PointedCGWH.diskOne.{u, v} := disk_isCofibrant
  let _ : IsCofibrant (⊤_ PointedCGWH.{u, v}) := terminal_isCofibrant
  let _ : (PointedCGWH.EnrichedFunctorMapping.tensorMappingAdjunction X).IsQuillenAdjunction :=
    PointedCGWH.EnrichedIntervalCylinderModel.coefficient_isQuillen X
  let _ : WeakEquivalence PointedCGWH.diskAugmentation.{u, v} :=
    PointedCGWH.modelCategory.diskAugmentation_weakEquivalence
  have hMap : WeakEquivalence (F.map PointedCGWH.diskAugmentation) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := PointedCGWH.EnrichedFunctorMapping.tensorMappingAdjunction X)
      PointedCGWH.diskAugmentation
  have hComp : weakEquivalences (D (I := I))
      (F.map PointedCGWH.diskAugmentation ≫ (coefficientZeroIso X).hom) :=
    (weakEquivalences (D (I := I))).comp_mem _ _ hMap.mem
      (mem_weakEquivalences (coefficientZeroIso X).hom)
  have h : F.map PointedCGWH.diskAugmentation ≫ (coefficientZeroIso X).hom =
      Diagrams.toZero (tensorLeftObject PointedCGWH.diskOne X) :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  exact (weakEquivalence_iff _).mpr (h ▸ hComp)

/-- Comparison from the scalar disk-span homotopy pushout to one-sphere tensor. -/
def toSpherePushout : diskSpan (I := I) ⋙ homotopyPushout ⟶
    EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne :=
  Functor.whiskerLeft (diskSpan (I := I)) homotopyPushoutComparison ≫ sphereScalarNatIso.hom

/-- The homotopy pushout map induced by the original scalar disk collapse. -/
def toZeroPushout : diskSpan (I := I) ⋙ homotopyPushout ⟶
    (EnrichedFunctorCat.tensorLeft S0 ⋙ OriginalISuspension.zeroSpan (I := I)) ⋙
      homotopyPushout :=
  Functor.whiskerRight (diskToZeroSpan (I := I)) homotopyPushout

/-- For a cofibrant diagram, contracting the scalar disk induces a weak pushout map. -/
theorem toZeroPushout_weak (X : D (I := I)) [IsCofibrant X] :
    WeakEquivalence ((toZeroPushout (B := B)).app X) := by
  apply homotopyPushout_map_weakEquivalence ((diskToZeroSpan (I := I)).app X)
  intro j
  rcases j with (_ | _ | _)
  · change WeakEquivalence (𝟙 (tensorLeftObject S0 X))
    infer_instance
  · change WeakEquivalence (Diagrams.toZero (tensorLeftObject PointedCGWH.diskOne X))
    exact diskCollapse_weak X
  · change WeakEquivalence (𝟙 Diagrams.zeroDiagram)
    infer_instance

/-- For a cofibrant diagram, the comparison to the actual scalar one-sphere is weak. -/
theorem toSpherePushout_weak (X : D (I := I)) [IsCofibrant X] :
    WeakEquivalence ((toSpherePushout (B := B)).app X) := by
  let _ : (PointedCGWH.EnrichedFunctorMapping.tensorMappingAdjunction X).IsQuillenAdjunction :=
    PointedCGWH.EnrichedIntervalCylinderModel.coefficient_isQuillen X
  let _ : IsCofibrant S0.{u, v} := source_isCofibrant
  let _ : IsCofibrant ((diskSpan (I := I)).obj X |>.obj WalkingSpan.zero) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := PointedCGWH.EnrichedFunctorMapping.tensorMappingAdjunction X) source_isCofibrant
  let _ : IsCofibrant ((diskSpan (I := I)).obj X |>.obj WalkingSpan.right) := by
    change IsCofibrant (Diagrams.zeroDiagram (A := I))
    rw [isCofibrant_iff_of_isInitial (𝟙 Diagrams.zeroDiagram) Diagrams.zeroDiagramIsInitial]
    infer_instance
  let _ : Cofibration ((diskSpan (I := I)).obj X |>.map WalkingSpan.Hom.fst) :=
    (cofibration_iff _).mpr
      ((PointedCGWH.EnrichedIntervalCylinderModel.coefficient_isQuillen X).preservesCofibrations
        PointedCGWH.diskBoundary
        ((cofibration_iff _).mp PointedCGWH.modelCategory.diskBoundary_cofibration))
  let _ : WeakEquivalence
      ((homotopyPushoutComparison (C := D (I := I))).app ((diskSpan (I := I)).obj X)) :=
    weakEquivalence_homotopyPushoutComparison_of_fst ((diskSpan (I := I)).obj X)
  change WeakEquivalence
    ((homotopyPushoutComparison (C := D (I := I))).app ((diskSpan (I := I)).obj X) ≫
      (sphereScalarNatIso (I := I)).hom.app X)
  let _ : WeakEquivalence ((sphereScalarNatIso (I := I)).hom.app X) := by infer_instance
  infer_instance

/-- After original Q, the zero-span homotopy pushout of the disk source is naturally
isomorphic to scalar one-sphere tensor in the level homotopy category. -/
def zeroSourceQIsoSphereQ :
    (Replacement.cofibrantReplacement (B := B) (A := I) ⋙
      ((EnrichedFunctorCat.tensorLeft S0 ⋙ OriginalISuspension.zeroSpan (I := I)) ⋙
        homotopyPushout)) ⋙ toHomotopyCategory (D (I := I)) ≅
    (Replacement.cofibrantReplacement (B := B) (A := I) ⋙
      EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne) ⋙ toHomotopyCategory (D (I := I)) := by
  let Q := Replacement.cofibrantReplacement (B := B) (A := I)
  let H := toHomotopyCategory (D (I := I))
  let a := Functor.whiskerRight (Functor.whiskerLeft Q (toSpherePushout (B := B))) H
  let b := Functor.whiskerRight (Functor.whiskerLeft Q (toZeroPushout (B := B))) H
  let _ : ∀ X, IsIso (a.app X) := fun X => by
    let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := I) X
    change IsIso (H.map ((toSpherePushout (B := B)).app (Q.obj X)))
    exact (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp
      (toSpherePushout_weak (Q.obj X)).mem
  let _ : ∀ X, IsIso (b.app X) := fun X => by
    let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := I) X
    change IsIso (H.map ((toZeroPushout (B := B)).app (Q.obj X)))
    exact (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp
      (toZeroPushout_weak (Q.obj X)).mem
  let _ : IsIso a := NatIso.isIso_of_isIso_app a
  let _ : IsIso b := NatIso.isIso_of_isIso_app b
  exact (asIso b).symm ≪≫ asIso a

/-- After original Q, chosen I-cone suspension is naturally isomorphic to scalar
one-sphere tensor in the original level homotopy category. -/
def originalISuspensionQIsoSphereQ :
    (Replacement.cofibrantReplacement (B := B) (A := I) ⋙ OriginalISuspension.suspension (B := B)) ⋙
        toHomotopyCategory (D (I := I)) ≅
      (Replacement.cofibrantReplacement (B := B) (A := I) ⋙
        EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne) ⋙ toHomotopyCategory (D (I := I)) := by
  let Q := Replacement.cofibrantReplacement (B := B) (A := I)
  let H := toHomotopyCategory (D (I := I))
  let u := Functor.isoWhiskerRight
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (Functor.isoWhiskerLeft Q (sourceTensorUnitIso (I := I)))
        (OriginalISuspension.zeroSpan (I := I))) homotopyPushout) H
  exact OriginalISuspension.suspensionQIsoZeroPushoutQ (B := B) ≪≫
    u.symm ≪≫ zeroSourceQIsoSphereQ (B := B)

/-- The forward suspension comparison retains the entire original Q source arrow. -/
theorem originalISuspensionQIsoSphereQ_hom_naturality
    {X Y : D (I := I)} (f : X ⟶ Y) :
    (toHomotopyCategory (D (I := I))).map
        (OriginalISuspension.suspension (B := B) |>.map
          ((Replacement.cofibrantReplacement (B := B)).map f)) ≫
      (originalISuspensionQIsoSphereQ (B := B)).hom.app Y =
    (originalISuspensionQIsoSphereQ (B := B)).hom.app X ≫
      (toHomotopyCategory (D (I := I))).map
        ((EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne).map
          ((Replacement.cofibrantReplacement (B := B)).map f)) :=
  (originalISuspensionQIsoSphereQ (B := B)).hom.naturality f

/-- The inverse suspension comparison retains the same entire original Q source arrow. -/
theorem originalISuspensionQIsoSphereQ_inv_naturality
    {X Y : D (I := I)} (f : X ⟶ Y) :
    (toHomotopyCategory (D (I := I))).map
        ((EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne).map
          ((Replacement.cofibrantReplacement (B := B)).map f)) ≫
      (originalISuspensionQIsoSphereQ (B := B)).inv.app Y =
    (originalISuspensionQIsoSphereQ (B := B)).inv.app X ≫
      (toHomotopyCategory (D (I := I))).map
        (OriginalISuspension.suspension (B := B) |>.map
          ((Replacement.cofibrantReplacement (B := B)).map f)) :=
  (originalISuspensionQIsoSphereQ (B := B)).inv.naturality f

end HomotopicalAlgebra.EnrichedProjective.Native.ScalarSphereSuspension
