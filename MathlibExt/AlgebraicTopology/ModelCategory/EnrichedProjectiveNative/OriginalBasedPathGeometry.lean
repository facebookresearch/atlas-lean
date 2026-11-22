/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.OriginalFiberCofiberConeGeometry
import MathlibExt.CategoryTheory.Enriched.ScalarCotensorUnit
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHNativeDerivedLoopComparison

/-!
# Original fiber and cofiber geometry on enriched native diagrams

The index is an arbitrary category enriched over the actual pointed CGWH
coefficient category. Every construction uses the original native I replacement,
I cone and I suspension, at the caller's realized-generator bottom. The published
coefficient disk maximum is reused with its actual selected time-one point.
No stable model or Omega hypothesis is part of this geometry.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat MonoidalCategory
open PointedCGWH.DiskMaximumGeometry
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OriginalFiberCofiberGeometry

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

variable {J : Type} [EnrichedCategory PointedCGWH.{u, v} J]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] Native.modelCategory Native.allObjectsFibrant
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} J
private abbrev H := toHomotopyCategory (Carrier (J := J))
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := J)
private abbrev S := OriginalISuspension.suspension (B := B) (I := J)

variable (a : ∀ F : Arrow (Carrier (J := J)),
  PullbackCone F.hom (Diagrams.zeroTo F.right)) (ha : ∀ F, IsLimit (a F))

private abbrev P := OrdinaryHoChosenFiberMaps.fibrantFibrationProperty (C := Carrier (J := J))

/-- Every native level fibration keeps its entire arrow and actual fibrant target. -/
abbrev Eligible := (P (J := J)).FullSubcategory

/-- The actual scalar sphere tensor is the native suspension functor. -/
abbrev scalarSuspension : Carrier (J := J) ⥤ Carrier (J := J) :=
  EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne

/-- The actual scalar sphere cotensor is the native loop functor. -/
abbrev scalarLoop : Carrier (J := J) ⥤ Carrier (J := J) :=
  EnrichedFunctorCat.cotensor PointedCGWH.sphereOne

/-- Both scalar maps belong to the original full scalar adjunction. -/
abbrev scalarCounit : scalarLoop (J := J) ⋙ scalarSuspension ⟶ 𝟭 (Carrier (J := J)) :=
  (ScalarLeibniz.adjunction PointedCGWH.sphereOne).counit

omit B in
/-- Every actual scalar loop component is the original pointed one-sphere internal Hom. -/
theorem scalarLoop_obj_component (Y : Carrier (J := J)) (r : J) :
    (scalarLoop.obj Y).toEnrichedFunctor.obj r =
      PointedCGWH.loop.obj (Y.toEnrichedFunctor.obj r) := rfl

omit B in
/-- Full scalar loop maps retain each original coefficient map. -/
theorem scalarLoop_map_component {X Y : Carrier (J := J)} (f : X ⟶ Y) (r : J) :
    component (scalarLoop.map f) r = PointedCGWH.loop.map (component f r) :=
  cotensorMap_component PointedCGWH.sphereOne f r

omit B in
/-- The full scalar suspension retains its actual one-sphere tensor object. -/
theorem scalarSuspension_obj_component (Y : Carrier (J := J)) (r : J) :
    (scalarSuspension.obj Y).toEnrichedFunctor.obj r =
      PointedCGWH.sphereOne ⊗ Y.toEnrichedFunctor.obj r := rfl

omit B in
/-- The whole scalar suspension arrow is the original whiskered coefficient map. -/
theorem scalarSuspension_map_component {X Y : Carrier (J := J)} (f : X ⟶ Y) (r : J) :
    component (scalarSuspension.map f) r = PointedCGWH.sphereOne ◁ component f r :=
  tensorLeftMap_component PointedCGWH.sphereOne f r


namespace NativeBasedPathGeometry

open CategoryTheory.EnrichedFunctorCat MonoidalCategory
open scoped MonoidalClosed

private abbrev disk := PointedCGWH.diskOne.{u, v}
private abbrev L := EnrichedFunctorCat.tensorLeft (A := J) disk.{u, v}
private abbrev R := EnrichedFunctorCat.cotensor (I := J) disk.{u, v}
private abbrev adj := ScalarLeibniz.adjunction (A := J) disk.{u, v}

section StrictScalar

omit B

/-- The full actual coefficient precomposition has the same uncurried enriched diagram map. -/
theorem unadjunct_coefficient_pre {M N : PointedCGWH.{u, v}} (i : M ⟶ N)
    (A Y : (Carrier (J := J))) (t : A ⟶ cotensorObject N Y) :
    ScalarLeibniz.unadjunct M A Y (t ≫ cotensorScalarMap i Y) =
      scalarTensorMap i A ≫ ScalarLeibniz.unadjunct N A Y t := by
  apply EnrichedFunctorCat.hom_ext
  intro r
  rw [ScalarLeibniz.unadjunct_component, component_comp, cotensorScalarMap_component,
    component_comp, scalarTensorMap_component, ScalarLeibniz.unadjunct_component,
    MonoidalClosed.uncurry_pre_app]
  rfl

/-- Native based paths are the actual full disk cotensor on the original enriched carrier. -/
abbrev basedPath : (Carrier (J := J)) ⥤ (Carrier (J := J)) := R

/-- The actual time-zero scalar boundary keeps the original native disk unit map. -/
def scalarBoundary (A : (Carrier (J := J))) : A ⟶ L.obj A :=
  (scalarUnitIso A).inv ≫ scalarTensorMap diskFreeEndpoint A

/-- The actual free disk endpoint acts on the entire original diagram family. -/
def scalarBoundaryNatTrans : 𝟭 (Carrier (J := J)) ⟶ L :=
  (NatIso.ofComponents scalarUnitIso (fun f => scalarUnitIso_naturality f) :
      EnrichedFunctorCat.tensorLeft (𝟙_ PointedCGWH.{u, v}) ≅ 𝟭 (Carrier (J := J))).inv ≫
    (EnrichedFunctorCat.tensorBifunctor
      (V := PointedCGWH.{u, v}) (A := J)).map diskFreeEndpoint

/-- The whole transformation retains the same actual source-unit component. -/
theorem scalarBoundaryNatTrans_app (A : (Carrier (J := J))) :
    scalarBoundaryNatTrans.app A = scalarBoundary A := rfl

/-- Every original diagram map preserves the complete native disk boundary word. -/
theorem scalarBoundary_naturality {A A' : (Carrier (J := J))} (f : A ⟶ A') :
    f ≫ scalarBoundary A' = scalarBoundary A ≫ L.map f :=
  scalarBoundaryNatTrans.naturality f

/--
The free endpoint is the original coefficient precomposition followed by closed unit evaluation.
-/
def basedPathEndpoint : basedPath (J := J) ⟶ 𝟭 (Carrier (J := J)) :=
  (ScalarLeibniz.cotensorBifunctor (V := PointedCGWH.{u, v}) (A := J)).map
      diskFreeEndpoint.op ≫
    NativeOmegaRecovery.OriginalCotensorUnit.comparison.hom

/-- The whole cotensor-bifunctor endpoint retains its exact original coefficient and unit maps. -/
theorem basedPathEndpoint_app (Y : (Carrier (J := J))) : basedPathEndpoint.app Y =
    cotensorScalarMap diskFreeEndpoint Y ≫
      NativeOmegaRecovery.OriginalCotensorUnit.comparison.hom.app Y := rfl

/-- Evaluation at every original index is the actual pointed disk internal Hom. -/
theorem basedPath_obj_component (Y : Carrier (J := J)) (r : J) :
    (basedPath.obj Y).toEnrichedFunctor.obj r =
      PointedCGWH.basedPath.obj (Y.toEnrichedFunctor.obj r) := rfl

/-- Every whole native map retains its complete pointed based-path component. -/
theorem basedPath_map_component {X Y : Carrier (J := J)} (f : X ⟶ Y) (r : J) :
    component (basedPath.map f) r = PointedCGWH.basedPath.map (component f r) :=
  cotensorMap_component disk f r

/-- Every endpoint keeps the original coefficient precomposition and unit evaluation. -/
theorem basedPathEndpoint_component_word (Y : Carrier (J := J)) (r : J) :
    component (basedPathEndpoint.app Y) r =
      (MonoidalClosed.pre
        diskFreeEndpoint).app
          (Y.toEnrichedFunctor.obj r) ≫
        MonoidalClosed.unitNatIso.inv.app (Y.toEnrichedFunctor.obj r) := by
  change component
    (cotensorScalarMap
      diskFreeEndpoint Y ≫
        NativeOmegaRecovery.OriginalCotensorUnit.counitMap Y) r = _
  rw [component_comp, cotensorScalarMap_component,
    NativeOmegaRecovery.OriginalCotensorUnit.counitMap_component]
  rfl

/-- The original endpoint is the full actual pointed path endpoint at every index. -/
theorem basedPathEndpoint_component (Y : Carrier (J := J)) (r : J) :
    component (basedPathEndpoint.app Y) r =
      PointedCGWH.basedPathEndpoint.app (Y.toEnrichedFunctor.obj r) := by
  rw [basedPathEndpoint_component_word]
  let e :=
    diskBoundarySourceIso.{u, v}
  change (MonoidalClosed.pre (e.hom ≫ PointedCGWH.diskBoundary.{u, v})).app
      (Y.toEnrichedFunctor.obj r) ≫ MonoidalClosed.unitNatIso.inv.app (Y.toEnrichedFunctor.obj r) =
    (MonoidalClosed.pre PointedCGWH.diskBoundary.{u, v}).app (Y.toEnrichedFunctor.obj r) ≫
      (MonoidalClosed.pre e.hom).app (Y.toEnrichedFunctor.obj r) ≫
        MonoidalClosed.unitNatIso.inv.app (Y.toEnrichedFunctor.obj r)
  have h := congr_app (MonoidalClosed.pre_map e.hom PointedCGWH.diskBoundary.{u, v})
    (Y.toEnrichedFunctor.obj r)
  simpa only [NatTrans.comp_app, Category.assoc] using
    congrArg (fun f => f ≫ MonoidalClosed.unitNatIso.inv.app (Y.toEnrichedFunctor.obj r)) h

/-- The unresolved actual endpoint retains both original Arrow components on every map. -/
def basedPathUnresolvedArrowFunctor : (Carrier (J := J)) ⥤ Arrow (Carrier (J := J)) where
  obj Y := Arrow.mk (basedPathEndpoint.app Y)
  map {X Y} f := Arrow.homMk (basedPath.map f) f (basedPathEndpoint.naturality f)
  map_id Y := by
    apply Arrow.hom_ext
    · exact basedPath.map_id Y
    · rfl
  map_comp f g := by
    apply Arrow.hom_ext
    · exact basedPath.map_comp f g
    · rfl

end StrictScalar

omit B in
/-- Every actual enriched evaluation of the free endpoint is a native fibration. -/
theorem basedPathEndpoint_component_fibration (Y : Carrier (J := J)) (r : J) :
    fibrations PointedCGWH.{u, v} (component (basedPathEndpoint.app Y) r) := by
  rw [basedPathEndpoint_component]
  exact (PointedCGWH.modelCategory.basedPathEndpoint_fibration
    (Y.toEnrichedFunctor.obj r)).mem

/-- The full native path endpoint is a level fibration for every arbitrary base. -/
theorem basedPathEndpoint_fibration (Y : Carrier (J := J)) :
    Fibration (basedPathEndpoint.app Y) := by
  apply (HomotopicalAlgebra.fibration_iff _).mpr
  rw [Native.fibrations_eq]
  apply (EvaluationTransfer.evaluationProperty_iff
    (fun r : J => EnrichedFunctorCat.evaluation r) (fibrations PointedCGWH.{u, v}) _).mpr
  intro r
  exact basedPathEndpoint_component_fibration Y r

/-- The actual constant based path is weak at every native enriched evaluation. -/
theorem basedPathPoint_weak (Y : Carrier (J := J)) :
    weakEquivalences (Carrier (J := J)) (Diagrams.zeroTo (basedPath.obj Y)) := by
  rw [Native.weakEquivalences_eq]
  apply (EvaluationTransfer.evaluationProperty_iff
    (fun r : J => EnrichedFunctorCat.evaluation r) (weakEquivalences PointedCGWH.{u, v}) _).mpr
  intro r
  let hZ := Diagrams.initialDiagram_component_isZero (A := J) r
  let eZ := IsZero.iso hZ (isZero_zero PointedCGWH.{u, v})
  have h : component (Diagrams.zeroTo (basedPath.obj Y)) r =
      eZ.hom ≫ PointedCGWH.basedPathPoint.app (Y.toEnrichedFunctor.obj r) :=
    hZ.isInitial.hom_ext _ _
  change weakEquivalences PointedCGWH.{u, v} (component (Diagrams.zeroTo (basedPath.obj Y)) r)
  rw [h]
  exact (weakEquivalences PointedCGWH.{u, v}).comp_mem _ _ (mem_weakEquivalences eZ.hom)
    (PointedCGWH.modelCategory.basedPathPoint_weakEquivalence (Y.toEnrichedFunctor.obj r)).mem

/-- The full original Q based-path family keeps its actual same native source. -/
abbrev basedPathQ : (Carrier (J := J)) ⥤ (Carrier (J := J)) := basedPath ⋙ Q

/-- The original Q counit and original free endpoint define the complete same path arrow. -/
def basedPathQEndpoint : basedPathQ (J := J) ⟶ 𝟭 (Carrier (J := J)) :=
  Functor.whiskerLeft basedPath Replacement.cofibrantReplacementCounit ≫
    (Functor.rightUnitor basedPath).hom ≫ basedPathEndpoint

/-- The full Q path endpoint retains the entire actual original counit and endpoint word. -/
theorem basedPathQEndpoint_app (Y : (Carrier (J := J))) :
    basedPathQEndpoint.app Y =
      Replacement.cofibrantReplacementCounit.app (basedPath.obj Y) ≫
        basedPathEndpoint.app Y := by
  simp only [basedPathQEndpoint, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app]
  exact congrArg (Replacement.cofibrantReplacementCounit.app (basedPath.obj Y) ≫ ·)
    (Category.id_comp (basedPathEndpoint.app Y))

/-- The actual Q path endpoint is a native fibration through the original trivial counit. -/
theorem basedPathQEndpoint_fibration (Y : (Carrier (J := J))) :
    Fibration (basedPathQEndpoint.app Y) := by
  rw [basedPathQEndpoint_app]
  let _ : Fibration (Replacement.cofibrantReplacementCounit.app (basedPath.obj Y)) :=
    (HomotopicalAlgebra.fibration_iff _).mpr
      (Replacement.cofibrantReplacementCounit_mem_trivialFibrations (basedPath.obj Y)).1
  let _ : Fibration (basedPathEndpoint.app Y) := basedPathEndpoint_fibration Y
  infer_instance

/-- The actual native Q path source is cofibrant on the same original enriched carrier. -/
theorem basedPathQ_cofibrant (Y : (Carrier (J := J))) : IsCofibrant (basedPathQ.obj Y) :=
  Replacement.isCofibrant_cofibrantReplacement _

/-- The original Q counit makes the actual constant Q based-path inclusion weak. -/
theorem basedPathQPoint_weak (Y : (Carrier (J := J))) :
    weakEquivalences (Carrier (J := J)) (Diagrams.zeroTo (basedPathQ.obj Y)) := by
  apply (weakEquivalences (Carrier (J := J))).of_postcomp _ _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (basedPath.obj Y))
  have h : Diagrams.zeroTo (basedPathQ.obj Y) ≫
      Replacement.cofibrantReplacementCounit.app (basedPath.obj Y) =
        Diagrams.zeroTo (basedPath.obj Y) := Diagrams.zeroDiagram_isZero.isInitial.hom_ext _ _
  rw [h]
  exact basedPathPoint_weak Y

/-- The same full original Q based-path total object has its actual weak zero collapse. -/
theorem basedPathQCollapse_weak (Y : (Carrier (J := J))) :
    weakEquivalences (Carrier (J := J)) (Diagrams.toZero (basedPathQ.obj Y)) := by
  apply (weakEquivalences (Carrier (J := J))).of_precomp _ _ (basedPathQPoint_weak Y)
  have h : Diagrams.zeroTo (basedPathQ.obj Y) ≫ Diagrams.toZero (basedPathQ.obj Y) =
      𝟙 Diagrams.zeroDiagram := Diagrams.zeroDiagram_isZero.isInitial.hom_ext _ _
  rw [h]
  exact mem_weakEquivalences _


/-- The complete original path arrow retains the actual Q source and original base on every map. -/
def basedPathArrowFunctor : (Carrier (J := J)) ⥤ Arrow (Carrier (J := J)) where
  obj Y := Arrow.mk (basedPathQEndpoint.app Y)
  map {X Y} f := Arrow.homMk (basedPathQ.map f) f (basedPathQEndpoint.naturality f)
  map_id Y := by
    apply Arrow.hom_ext
    · exact basedPathQ.map_id Y
    · rfl
  map_comp f g := by
    apply Arrow.hom_ext
    · exact basedPathQ.map_comp f g
    · rfl

/-- Every entire actual native path arrow belongs to the original all-fibration category. -/
def basedPathFibrationFunctor : (Carrier (J := J)) ⥤ Eligible (J := J) :=
  P.lift basedPathArrowFunctor (fun Y =>
    ⟨basedPathQEndpoint_fibration Y,
      HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant Y⟩)

/-- The original native path square has the entire original fibration base as its identity base. -/
theorem identityBaseSerreLiftSquare (F : Eligible (J := J)) :
    CommSq (Diagrams.zeroTo F.obj.left) (Diagrams.zeroTo (basedPathQ.obj F.obj.right))
      F.obj.hom (basedPathQEndpoint.app F.obj.right) :=
  ⟨Diagrams.zeroDiagram_isZero.isInitial.hom_ext _ _⟩

private instance identityBaseSerreLiftSquare_hasLift (F : Eligible (J := J)) :
    (identityBaseSerreLiftSquare F).HasLift := by
  let _ : IsCofibrant (basedPathQ.obj F.obj.right) := basedPathQ_cofibrant F.obj.right
  let _ : Cofibration (Diagrams.zeroTo (basedPathQ.obj F.obj.right)) :=
    (isCofibrant_iff_of_isInitial _ Diagrams.zeroDiagram_isZero.isInitial).mp inferInstance
  let _ : WeakEquivalence (Diagrams.zeroTo (basedPathQ.obj F.obj.right)) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (basedPathQPoint_weak F.obj.right)
  let _ : Fibration F.obj.hom := F.property.1
  infer_instance

/-- CM4 constructs a genuine whole native Serre lift over the original identity base. -/
def identityBaseSerreLift (F : Eligible (J := J)) : basedPathQ.obj F.obj.right ⟶ F.obj.left :=
  (identityBaseSerreLiftSquare F).lift

/-- The actual whole lift retains its complete original native zero-source equation. -/
theorem identityBaseSerreLift_zero (F : Eligible (J := J)) :
    Diagrams.zeroTo (basedPathQ.obj F.obj.right) ≫ identityBaseSerreLift F =
      Diagrams.zeroTo F.obj.left :=
  (identityBaseSerreLiftSquare F).fac_left

/-- The entire original fibration projection of the lift is the actual full native path endpoint. -/
theorem identityBaseSerreLift_over (F : Eligible (J := J)) :
    identityBaseSerreLift F ≫ F.obj.hom = basedPathQEndpoint.app F.obj.right :=
  (identityBaseSerreLiftSquare F).fac_right

/-- Both original Arrow components of the whole Serre lift keep the actual unchanged base. -/
def identityBaseSerreLiftArrow (F : Eligible (J := J)) :
    basedPathArrowFunctor.obj F.obj.right ⟶ F.obj :=
  Arrow.homMk (identityBaseSerreLift F) (𝟙 F.obj.right)
    ((identityBaseSerreLift_over F).trans
      (Category.comp_id (basedPathQEndpoint.app F.obj.right)).symm)

/-- Its full original source component is the same constructed whole native lift. -/
theorem identityBaseSerreLiftArrow_left (F : Eligible (J := J)) :
    (identityBaseSerreLiftArrow F).left = identityBaseSerreLift F := rfl

/-- Its full original target component is literally the original base identity. -/
theorem identityBaseSerreLiftArrow_right (F : Eligible (J := J)) :
    (identityBaseSerreLiftArrow F).right = 𝟙 F.obj.right := rfl

/-- The full original all-fibration inclusion carries the whole same identity-base lift Arrow. -/
def identityBaseSerreLiftMap (F : Eligible (J := J)) :
    basedPathFibrationFunctor.obj F.obj.right ⟶ F :=
  P.ι.preimage (identityBaseSerreLiftArrow F)

/-- Both components of the native lift remain the exact original Arrow under the full inclusion. -/
theorem identityBaseSerreLiftMap_ι (F : Eligible (J := J)) :
    P.ι.map (identityBaseSerreLiftMap F) = identityBaseSerreLiftArrow F :=
  P.ι.map_preimage (X := basedPathFibrationFunctor.obj F.obj.right) (Y := F)
    (identityBaseSerreLiftArrow F)

section StrictContraction

omit B

/-- The whole actual native unit cotensor evaluates by its original scalar-unit transpose. -/
theorem unitEvaluation (A Y : (Carrier (J := J)))
    (t : A ⟶ cotensorObject (𝟙_ PointedCGWH.{u, v}) Y) :
    t ≫ NativeOmegaRecovery.OriginalCotensorUnit.comparison.hom.app Y =
      (scalarUnitIso A).inv ≫ ScalarLeibniz.unadjunct (𝟙_ PointedCGWH.{u, v}) A Y t := by
  change t ≫ NativeOmegaRecovery.OriginalCotensorUnit.counitMap Y = _
  apply EnrichedFunctorCat.hom_ext
  intro r
  rw [component_comp, NativeOmegaRecovery.OriginalCotensorUnit.counitMap_component,
    component_comp, scalarUnitIso_inv_component, ScalarLeibniz.unadjunct_component]
  exact NativeOmegaRecovery.UnitCotensorEvaluation.map (component t r)

/-- Every entire native path map retains the same original boundary and disk-adjoint endpoint. -/
theorem basedPathEndpoint_after (A Y : (Carrier (J := J))) (t : A ⟶ basedPath.obj Y) :
    t ≫ basedPathEndpoint.app Y =
      scalarBoundary A ≫ ScalarLeibniz.unadjunct disk A Y t := by
  rw [basedPathEndpoint_app, ← Category.assoc, unitEvaluation,
    unadjunct_coefficient_pre, scalarBoundary]
  exact (Category.assoc _ _ _).symm

/-- The contraction is the whole actual disk adjunct of the original native maximum evaluation. -/
def basedPathContraction (Y : (Carrier (J := J))) : L.obj (basedPath.obj Y) ⟶ basedPath.obj Y :=
  ScalarLeibniz.adjunct disk (L.obj (basedPath.obj Y)) Y
    ((scalarAssociatorIso disk disk (basedPath.obj Y)).inv ≫
      scalarTensorMap diskMaximum (basedPath.obj Y) ≫ adj.counit.app Y)

/-- Its entire disk transpose retains the actual maximum and original scalar counit word. -/
theorem basedPathContraction_unadjunct (Y : (Carrier (J := J))) :
    ScalarLeibniz.unadjunct disk (L.obj (basedPath.obj Y)) Y (basedPathContraction Y) =
      (scalarAssociatorIso disk disk (basedPath.obj Y)).inv ≫
        scalarTensorMap diskMaximum (basedPath.obj Y) ≫ adj.counit.app Y :=
  ScalarLeibniz.unadjunct_adjunct disk _ _ _

private theorem iso_square_inverse {C : Type u} [Category.{v} C]
    {A B X Y : C} (a : A ≅ B) (b : X ≅ Y) (f : A ⟶ X) (g : B ⟶ Y)
    (h : f ≫ b.hom = a.hom ≫ g) : g ≫ b.inv = a.inv ≫ f := by
  apply (cancel_epi a.hom).mp
  calc
    a.hom ≫ (g ≫ b.inv) = (a.hom ≫ g) ≫ b.inv := (Category.assoc _ _ _).symm
    _ = (f ≫ b.hom) ≫ b.inv := congrArg (· ≫ b.inv) h.symm
    _ = f := (Category.assoc _ _ _).trans
      ((congrArg (f ≫ ·) b.hom_inv_id).trans (Category.comp_id _))
    _ = a.hom ≫ (a.inv ≫ f) :=
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f) a.hom_inv_id).trans (Category.id_comp _))).symm


/-- The full original disk maximum and scalar action preserve the right unit at every diagram. -/
private theorem scalarMaximum_right_unit (A : Carrier (J := J)) :
    L.map (scalarBoundary A) ≫ (scalarAssociatorIso disk disk A).inv ≫
      scalarTensorMap diskMaximum A = 𝟙 (L.obj A) := by
  let F := (EnrichedFunctorCat.tensorBifunctor
    (V := PointedCGWH.{u, v}) (A := J)).flip.obj A
  let aD1 : F.obj (disk ⊗ 𝟙_ PointedCGWH.{u, v}) ≅
      L.obj (tensorLeftObject (𝟙_ PointedCGWH.{u, v}) A) :=
    scalarAssociatorIso disk (𝟙_ PointedCGWH.{u, v}) A
  let aDD : F.obj (disk ⊗ disk) ≅ L.obj (L.obj A) := scalarAssociatorIso disk disk A
  have hUnit : aD1 ≪≫ L.mapIso (scalarUnitIso A) = F.mapIso (ρ_ disk) := by
    apply Iso.ext
    exact scalarAssociatorIso_unit_right disk A
  have hInv := congrArg (fun e => e.inv) hUnit
  simp only [Functor.mapIso_inv] at hInv
  let b : tensorLeftObject (𝟙_ PointedCGWH.{u, v}) A ⟶ L.obj A :=
    scalarTensorMap diskFreeEndpoint A
  let t : F.obj (disk ⊗ 𝟙_ PointedCGWH.{u, v}) ⟶ F.obj (disk ⊗ disk) :=
    scalarTensorMap (disk ◁ diskFreeEndpoint) A
  have hNat : L.map b ≫ aDD.inv = aD1.inv ≫ t := by
    have hScalar : scalarTensorMap (disk ◁ diskFreeEndpoint) A ≫
        aDD.hom = aD1.hom ≫
          L.map (scalarTensorMap diskFreeEndpoint A) :=
      scalarAssociatorIso_scalar_right disk diskFreeEndpoint A
    exact iso_square_inverse aD1 aDD
      (scalarTensorMap (disk ◁ diskFreeEndpoint) A)
      (L.map (scalarTensorMap diskFreeEndpoint A)) hScalar
  let unitInv : A ⟶ tensorLeftObject (𝟙_ PointedCGWH.{u, v}) A := (scalarUnitIso A).inv
  let boundary : tensorLeftObject (𝟙_ PointedCGWH.{u, v}) A ⟶ L.obj A := b
  have hBoundary : scalarBoundary A = unitInv ≫ boundary := rfl
  change L.map (scalarBoundary A) ≫ aDD.inv ≫ F.map diskMaximum = 𝟙 (L.obj A)
  rw [hBoundary, L.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hNat]
  have hInvTyped : L.map unitInv ≫ aD1.inv = F.map (ρ_ disk).inv := hInv
  rw [reassoc_of% hInvTyped]
  change F.map (ρ_ disk).inv ≫ F.map (disk ◁ diskFreeEndpoint) ≫ F.map diskMaximum = 𝟙 (F.obj disk)
  have hLaw : (ρ_ disk).inv ≫ (disk ◁ diskFreeEndpoint) ≫ diskMaximum = 𝟙 disk :=
    diskMaximum_right_unit
  have h := F.congr_map hLaw
  simpa only [Functor.map_comp, F.map_id] using h

/-- The full original disk maximum and scalar action preserve the left unit at every diagram. -/
private theorem scalarMaximum_left_unit (A : Carrier (J := J)) :
    scalarBoundary (L.obj A) ≫ (scalarAssociatorIso disk disk A).inv ≫
      scalarTensorMap diskMaximum A = 𝟙 (L.obj A) := by
  let F := (EnrichedFunctorCat.tensorBifunctor
    (V := PointedCGWH.{u, v}) (A := J)).flip.obj A
  let a1D : F.obj (𝟙_ PointedCGWH.{u, v} ⊗ disk) ≅
      tensorLeftObject (𝟙_ PointedCGWH.{u, v}) (L.obj A) :=
    scalarAssociatorIso (𝟙_ PointedCGWH.{u, v}) disk A
  let aDD : F.obj (disk ⊗ disk) ≅ L.obj (L.obj A) := scalarAssociatorIso disk disk A
  have hUnit : a1D ≪≫ scalarUnitIso (L.obj A) = F.mapIso (λ_ disk) := by
    apply Iso.ext
    exact scalarAssociatorIso_unit_left disk A
  have hInv := congrArg (fun e => e.inv) hUnit
  simp only [Functor.mapIso_inv] at hInv
  let b : tensorLeftObject (𝟙_ PointedCGWH.{u, v}) (L.obj A) ⟶ L.obj (L.obj A) :=
    scalarTensorMap diskFreeEndpoint (L.obj A)
  let t : F.obj (𝟙_ PointedCGWH.{u, v} ⊗ disk) ⟶ F.obj (disk ⊗ disk) :=
    scalarTensorMap (diskFreeEndpoint ▷ disk) A
  have hNat : b ≫ aDD.inv = a1D.inv ≫ t := by
    have hScalar : scalarTensorMap (diskFreeEndpoint ▷ disk) A ≫
        aDD.hom = a1D.hom ≫
          scalarTensorMap diskFreeEndpoint (L.obj A) :=
      scalarAssociatorIso_scalar_left diskFreeEndpoint disk A
    exact iso_square_inverse a1D aDD
      (scalarTensorMap (diskFreeEndpoint ▷ disk) A)
      (scalarTensorMap diskFreeEndpoint (L.obj A)) hScalar
  let unitInv : L.obj A ⟶ tensorLeftObject (𝟙_ PointedCGWH.{u, v}) (L.obj A) :=
    (scalarUnitIso (L.obj A)).inv
  let boundary : tensorLeftObject (𝟙_ PointedCGWH.{u, v}) (L.obj A) ⟶ L.obj (L.obj A) := b
  have hBoundary : scalarBoundary (L.obj A) = unitInv ≫ boundary := rfl
  change scalarBoundary (L.obj A) ≫ aDD.inv ≫ F.map diskMaximum = 𝟙 (L.obj A)
  rw [hBoundary]
  simp only [Category.assoc]
  rw [reassoc_of% hNat]
  have hInvTyped : unitInv ≫ a1D.inv = F.map (λ_ disk).inv := hInv
  rw [reassoc_of% hInvTyped]
  change F.map (λ_ disk).inv ≫ F.map (diskFreeEndpoint ▷ disk) ≫ F.map diskMaximum = 𝟙 (F.obj disk)
  have hLaw : (λ_ disk).inv ≫ (diskFreeEndpoint ▷ disk) ≫ diskMaximum = 𝟙 disk :=
    diskMaximum_left_unit
  have h := F.congr_map hLaw
  simpa only [Functor.map_comp, F.map_id] using h

private theorem unadjunct_path_identity (Y : Carrier (J := J)) :
    ScalarLeibniz.unadjunct disk (basedPath.obj Y) Y (𝟙 (basedPath.obj Y)) = adj.counit.app Y := by
  rfl

private theorem postcompose_three_eq {C : Type u} [Category.{v} C]
    {A B D E T : C} (a : A ⟶ B) (b : B ⟶ D) (m : D ⟶ E)
    (d : A ⟶ E) (hd : a ≫ b ≫ m = d) (c : E ⟶ T) :
    a ≫ (b ≫ m ≫ c) = d ≫ c := by
  exact (Category.assoc a b (m ≫ c)).symm.trans
    ((Category.assoc (a ≫ b) m c).symm.trans
      (congrArg (· ≫ c) ((Category.assoc a b m).trans hd)))

private theorem scalarMaximum_right_unit_after (A Y : Carrier (J := J))
    (c : L.obj A ⟶ Y) :
    L.map (scalarBoundary A) ≫
      ((scalarAssociatorIso disk disk A).inv ≫ scalarTensorMap diskMaximum A ≫ c) = c := by
  let j : L.obj (L.obj A) ⟶ tensorLeftObject (disk ⊗ disk) A :=
    (scalarAssociatorIso disk disk A).inv
  let m : tensorLeftObject (disk ⊗ disk) A ⟶ L.obj A := scalarTensorMap diskMaximum A
  exact (postcompose_three_eq (L.map (scalarBoundary A)) j m (𝟙 (L.obj A))
    (scalarMaximum_right_unit A) c).trans (Category.id_comp c)

private theorem scalarMaximum_left_unit_after (A Y : Carrier (J := J))
    (c : L.obj A ⟶ Y) :
    scalarBoundary (L.obj A) ≫
      ((scalarAssociatorIso disk disk A).inv ≫ scalarTensorMap diskMaximum A ≫ c) = c := by
  let j : L.obj (L.obj A) ⟶ tensorLeftObject (disk ⊗ disk) A :=
    (scalarAssociatorIso disk disk A).inv
  let m : tensorLeftObject (disk ⊗ disk) A ⟶ L.obj A := scalarTensorMap diskMaximum A
  exact (postcompose_three_eq (scalarBoundary (L.obj A)) j m (𝟙 (L.obj A))
    (scalarMaximum_left_unit A) c).trans (Category.id_comp c)

private theorem basedPathContraction_source_unadjunct (Y : Carrier (J := J)) :
    ScalarLeibniz.unadjunct disk (basedPath.obj Y) Y
      (scalarBoundary (basedPath.obj Y) ≫ basedPathContraction Y) = adj.counit.app Y := by
  have h := ScalarLeibniz.unadjunct_source disk (scalarBoundary (basedPath.obj Y))
    (basedPathContraction Y)
  have hBody := basedPathContraction_unadjunct Y
  exact h.trans ((congrArg (L.map (scalarBoundary (basedPath.obj Y)) ≫ ·) hBody).trans
    (scalarMaximum_right_unit_after (basedPath.obj Y) Y (adj.counit.app Y)))

/-- At the actual time-zero source, the whole native maximum contraction is the identity. -/
theorem basedPathContraction_source (Y : Carrier (J := J)) :
    scalarBoundary (basedPath.obj Y) ≫ basedPathContraction Y = 𝟙 (basedPath.obj Y) := by
  apply (ScalarLeibniz.homEquiv disk (basedPath.obj Y) Y).symm.injective
  exact (basedPathContraction_source_unadjunct Y).trans (unadjunct_path_identity Y).symm


/-- Projecting the whole maximum contraction is exactly the original native disk evaluation. -/
theorem basedPathContraction_endpoint (Y : Carrier (J := J)) :
    basedPathContraction Y ≫ basedPathEndpoint.app Y = adj.counit.app Y := by
  have h := basedPathEndpoint_after (L.obj (basedPath.obj Y)) Y (basedPathContraction Y)
  have hBody := basedPathContraction_unadjunct Y
  exact h.trans ((congrArg (scalarBoundary (L.obj (basedPath.obj Y)) ≫ ·) hBody).trans
    (scalarMaximum_left_unit_after (basedPath.obj Y) Y (adj.counit.app Y)))


/-- Inverse scalar transposition retains every full original target map. -/
theorem unadjunct_target (M : PointedCGWH.{u, v})
    {A X Y : Carrier (J := J)} (t : A ⟶ cotensorObject M X) (f : X ⟶ Y) :
    ScalarLeibniz.unadjunct M A Y (t ≫ cotensorMap M f) =
      ScalarLeibniz.unadjunct M A X t ≫ f := by
  apply EnrichedFunctorCat.hom_ext
  intro r
  rw [ScalarLeibniz.unadjunct_component, component_comp, cotensorMap_component,
    component_comp, ScalarLeibniz.unadjunct_component]
  exact MonoidalClosed.uncurry_natural_right (component t r) (component f r)

/-- The true maximum contraction is natural in the entire original base map. -/
theorem basedPathContraction_naturality {X Y : Carrier (J := J)} (f : X ⟶ Y) :
    L.map (basedPath.map f) ≫ basedPathContraction Y =
      basedPathContraction X ≫ basedPath.map f := by
  apply (ScalarLeibniz.homEquiv disk (L.obj (basedPath.obj X)) Y).symm.injective
  let p : basedPath.obj X ⟶ basedPath.obj Y := basedPath.map f
  let aX : tensorLeftObject (disk ⊗ disk) (basedPath.obj X) ≅ L.obj (L.obj (basedPath.obj X)) :=
    scalarAssociatorIso disk disk (basedPath.obj X)
  let aY : tensorLeftObject (disk ⊗ disk) (basedPath.obj Y) ≅ L.obj (L.obj (basedPath.obj Y)) :=
    scalarAssociatorIso disk disk (basedPath.obj Y)
  let t : tensorLeftObject (disk ⊗ disk) (basedPath.obj X) ⟶
      tensorLeftObject (disk ⊗ disk) (basedPath.obj Y) := tensorLeftMap (disk ⊗ disk) p
  let q : L.obj (L.obj (basedPath.obj X)) ⟶ L.obj (L.obj (basedPath.obj Y)) := L.map (L.map p)
  let mX : tensorLeftObject (disk ⊗ disk) (basedPath.obj X) ⟶ L.obj (basedPath.obj X) :=
    scalarTensorMap diskMaximum (basedPath.obj X)
  let mY : tensorLeftObject (disk ⊗ disk) (basedPath.obj Y) ⟶ L.obj (basedPath.obj Y) :=
    scalarTensorMap diskMaximum (basedPath.obj Y)
  let cX : L.obj (basedPath.obj X) ⟶ X := adj.counit.app X
  let cY : L.obj (basedPath.obj Y) ⟶ Y := adj.counit.app Y
  have hA : q ≫ aY.inv = aX.inv ≫ t :=
    iso_square_inverse aX aY t q (scalarAssociatorIso_naturality disk disk p)
  have hM : t ≫ mY = mX ≫ L.map p := scalarTensorMap_diagram_naturality diskMaximum p
  have hC : L.map p ≫ cY = cX ≫ f := adj.counit.naturality f
  have hLeft : ScalarLeibniz.unadjunct disk (L.obj (basedPath.obj X)) Y
      (L.map p ≫ basedPathContraction Y) = q ≫ (aY.inv ≫ mY ≫ cY) :=
    (ScalarLeibniz.unadjunct_source disk (L.map p) (basedPathContraction Y)).trans
      (congrArg (q ≫ ·) (basedPathContraction_unadjunct Y))
  have hRight : ScalarLeibniz.unadjunct disk (L.obj (basedPath.obj X)) Y
      (basedPathContraction X ≫ basedPath.map f) = (aX.inv ≫ mX ≫ cX) ≫ f :=
    (unadjunct_target disk (basedPathContraction X) f).trans
      (congrArg (· ≫ f) (basedPathContraction_unadjunct X))
  have hWord : q ≫ (aY.inv ≫ mY ≫ cY) = (aX.inv ≫ mX ≫ cX) ≫ f := by
    calc
      _ = (q ≫ aY.inv) ≫ (mY ≫ cY) := (Category.assoc _ _ _).symm
      _ = (aX.inv ≫ t) ≫ (mY ≫ cY) := congrArg (· ≫ (mY ≫ cY)) hA
      _ = aX.inv ≫ ((t ≫ mY) ≫ cY) :=
        (Category.assoc _ _ _).trans (congrArg (aX.inv ≫ ·) (Category.assoc _ _ _).symm)
      _ = aX.inv ≫ ((mX ≫ L.map p) ≫ cY) := congrArg (aX.inv ≫ ·) (congrArg (· ≫ cY) hM)
      _ = aX.inv ≫ (mX ≫ (cX ≫ f)) :=
        congrArg (aX.inv ≫ ·) ((Category.assoc _ _ _).trans (congrArg (mX ≫ ·) hC))
      _ = _ := (Category.assoc aX.inv mX (cX ≫ f)).symm.trans
        ((Category.assoc (aX.inv ≫ mX) cX f).symm.trans
          (congrArg (· ≫ f) (Category.assoc aX.inv mX cX)))
  exact hLeft.trans (hWord.trans hRight.symm)


/-- The true scalar source and evaluation remain natural together on every whole base map. -/
theorem basedPathContraction_faces_naturality {X Y : Carrier (J := J)} (f : X ⟶ Y) :
    L.map (basedPath.map f) ≫ basedPathContraction Y ≫ basedPathEndpoint.app Y =
      basedPathContraction X ≫ basedPathEndpoint.app X ≫ f := by
  have h := basedPathContraction_naturality f
  have he : basedPath.map f ≫ basedPathEndpoint.app Y = basedPathEndpoint.app X ≫ f :=
    basedPathEndpoint.naturality f
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ basedPathEndpoint.app Y) h).trans
      ((Category.assoc _ _ _).trans (congrArg (basedPathContraction X ≫ ·) he)))


end StrictContraction

namespace LoopFiberUniversalProperty

section StrictScalar
omit B

private abbrev boundarySource :=
  (Arrow.mk PointedCGWH.diskBoundary.{u, v}).left

/-- Reindex the original source by the PUBLIC actual ordered-boundary iso.
This does not identify or unfold the private source iso in the older supplier. -/
def boundarySourceIso (A : (Carrier (J := J))) :
    tensorLeftObject boundarySource A ≅ A :=
  (((EnrichedFunctorCat.tensorBifunctor
      (V := PointedCGWH.{u, v}) (A := J)).mapIso
      diskBoundarySourceIso.symm).app A) ≪≫ scalarUnitIso A

theorem boundarySourceIso_inv_boundary (A : (Carrier (J := J))) :
    (boundarySourceIso A).inv ≫
      scalarTensorMap PointedCGWH.diskBoundary A = scalarBoundary A := by
  change ((scalarUnitIso A).inv ≫
      scalarTensorMap diskBoundarySourceIso.hom A) ≫
      scalarTensorMap PointedCGWH.diskBoundary A =
    (scalarUnitIso A).inv ≫
      scalarTensorMap
        (diskBoundarySourceIso.hom ≫ PointedCGWH.diskBoundary) A
  rw [Category.assoc, ← scalarTensorMap_comp]

/-- The existing scalar sphere pushout has the ACTUAL native time-zero boundary.
The other three objects and the quotient map are unchanged. -/
theorem spherePushout (A : (Carrier (J := J))) :
    IsPushout (scalarBoundary A) (Diagrams.toZero A)
      (scalarTensorMap ScalarSphereSuspension.quotient A)
      (Diagrams.zeroTo (tensorLeftObject PointedCGWH.sphereOne A)) := by
  apply (ScalarSphereSuspension.sphereScalarIsPushout (I := J) A).of_iso
    (boundarySourceIso A) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · rw [Iso.refl_hom, Category.comp_id,
      ← boundarySourceIso_inv_boundary, Iso.hom_inv_id_assoc]
  · exact Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The actual full endpoint transpose is the previously proved same native disk equation. -/
theorem boundary_unadjunct {A Y : (Carrier (J := J))}
    (t : A ⟶ basedPath.obj Y) :
    scalarBoundary A ≫ ScalarLeibniz.unadjunct disk A Y t =
      t ≫ basedPathEndpoint.app Y :=
  (basedPathEndpoint_after A Y t).symm

/-- This is the already existing complete cotensor-bifunctor map. -/
def loopInclusionNat : scalarLoop (J := J) ⟶ basedPath (J := J) :=
  (ScalarLeibniz.cotensorBifunctor
    (V := PointedCGWH.{u, v}) (A := J)).map
      ScalarSphereSuspension.quotient.op

/-- The original scalar loop includes into its genuine native based-path diagram. -/
def loopInclusion (Y : (Carrier (J := J))) :
    scalarLoop.obj Y ⟶ basedPath.obj Y := loopInclusionNat.app Y

theorem loop_unadjunct {A Y : (Carrier (J := J))}
    (t : A ⟶ scalarLoop.obj Y) :
    ScalarLeibniz.unadjunct disk A Y (t ≫ loopInclusion Y) =
      scalarTensorMap ScalarSphereSuspension.quotient A ≫
        ScalarLeibniz.unadjunct PointedCGWH.sphereOne A Y t := by
  exact unadjunct_coefficient_pre ScalarSphereSuspension.quotient A Y t

/-- The quotient kills the actual native free endpoint, as a whole diagram map. -/
theorem loopInclusion_endpoint (Y : (Carrier (J := J))) :
    loopInclusion Y ≫ basedPathEndpoint.app Y =
      Diagrams.toZero (scalarLoop.obj Y) ≫ Diagrams.zeroTo Y := by
  let A := scalarLoop.obj Y
  let d : L.obj A ⟶ scalarSuspension.obj A := scalarTensorMap ScalarSphereSuspension.quotient A
  let t : scalarSuspension.obj A ⟶ Y :=
    ScalarLeibniz.unadjunct PointedCGWH.sphereOne A Y (𝟙 A)
  have hTranspose : ScalarLeibniz.unadjunct disk A Y (loopInclusion Y) = d ≫ t := by
    have h := loop_unadjunct (A := A) (Y := Y) (𝟙 A)
    exact (congrArg (fun m => ScalarLeibniz.unadjunct disk A Y m) (Category.id_comp _)).symm.trans h
  have hFace : scalarBoundary A ≫ d =
      Diagrams.toZero A ≫ Diagrams.zeroTo (scalarSuspension.obj A) :=
    (spherePushout A).w
  exact (boundary_unadjunct (loopInclusion Y)).symm.trans
    ((congrArg (scalarBoundary A ≫ ·) hTranspose).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ t) hFace).trans
          ((Category.assoc _ _ _).trans
            (congrArg (Diagrams.toZero A ≫ ·) (Diagrams.zeroDiagramIsInitial.hom_ext _ _))))))


/-- Both actual projections form the full native endpoint fiber cone on the scalar loop. -/
def loopFiberCone (Y : (Carrier (J := J))) :
    PullbackCone (basedPathEndpoint.app Y) (Diagrams.zeroTo Y) :=
  PullbackCone.mk (loopInclusion Y)
    (Diagrams.toZero (scalarLoop.obj Y)) (loopInclusion_endpoint Y)

private theorem cone_boundary (Y : (Carrier (J := J)))
    (s : PullbackCone (basedPathEndpoint.app Y) (Diagrams.zeroTo Y)) :
    scalarBoundary s.pt ≫ ScalarLeibniz.unadjunct disk s.pt Y s.fst =
      Diagrams.toZero s.pt ≫ Diagrams.zeroTo Y := by
  rw [boundary_unadjunct]
  have hz : s.snd = Diagrams.toZero s.pt :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  exact s.condition.trans (congrArg (fun k => k ≫ Diagrams.zeroTo Y) hz)

/-- Pushout descent followed by the ACTUAL sphere adjunction constructs the lift. -/
def loopFiberLift (Y : (Carrier (J := J)))
    (s : PullbackCone (basedPathEndpoint.app Y) (Diagrams.zeroTo Y)) :
    s.pt ⟶ scalarLoop.obj Y :=
  ScalarLeibniz.adjunct PointedCGWH.sphereOne s.pt Y
    ((spherePushout s.pt).desc
      (ScalarLeibniz.unadjunct disk s.pt Y s.fst)
      (Diagrams.zeroTo Y) (cone_boundary Y s))

theorem loopFiberLift_fst (Y : (Carrier (J := J)))
    (s : PullbackCone (basedPathEndpoint.app Y) (Diagrams.zeroTo Y)) :
    loopFiberLift Y s ≫ loopInclusion Y = s.fst := by
  apply (ScalarLeibniz.homEquiv disk s.pt Y).symm.injective
  change ScalarLeibniz.unadjunct disk s.pt Y (loopFiberLift Y s ≫ loopInclusion Y) =
    ScalarLeibniz.unadjunct disk s.pt Y s.fst
  rw [loop_unadjunct, loopFiberLift, ScalarLeibniz.unadjunct_adjunct]
  exact (spherePushout s.pt).inl_desc _ _ _

theorem loopFiberLift_snd (Y : (Carrier (J := J)))
    (s : PullbackCone (basedPathEndpoint.app Y) (Diagrams.zeroTo Y)) :
    loopFiberLift Y s ≫ Diagrams.toZero (scalarLoop.obj Y) = s.snd :=
  Diagrams.zeroDiagramIsTerminal.hom_ext _ _

theorem loopFiberLift_unique (Y : (Carrier (J := J)))
    (s : PullbackCone (basedPathEndpoint.app Y) (Diagrams.zeroTo Y))
    (m : s.pt ⟶ scalarLoop.obj Y)
    (hFst : m ≫ loopInclusion Y = s.fst)
    (_hSnd : m ≫ Diagrams.toZero (scalarLoop.obj Y) = s.snd) :
    m = loopFiberLift Y s := by
  apply (ScalarLeibniz.homEquiv PointedCGWH.sphereOne s.pt Y).symm.injective
  apply (spherePushout s.pt).hom_ext
  · calc
      scalarTensorMap ScalarSphereSuspension.quotient s.pt ≫
          ScalarLeibniz.unadjunct PointedCGWH.sphereOne s.pt Y m =
        ScalarLeibniz.unadjunct disk s.pt Y (m ≫ loopInclusion Y) :=
          (loop_unadjunct m).symm
      _ = ScalarLeibniz.unadjunct disk s.pt Y s.fst :=
        congrArg (fun t => ScalarLeibniz.unadjunct disk s.pt Y t) hFst
      _ = scalarTensorMap ScalarSphereSuspension.quotient s.pt ≫
          ScalarLeibniz.unadjunct PointedCGWH.sphereOne s.pt Y (loopFiberLift Y s) := by
        rw [loopFiberLift, ScalarLeibniz.unadjunct_adjunct]
        exact ((spherePushout s.pt).inl_desc _ _ _).symm
  · exact Diagrams.zeroDiagramIsInitial.hom_ext _ _

/-- The sphere pushout and original adjunction supply the complete native loop-fiber limit data. -/
def loopFiberConeIsLimit (Y : (Carrier (J := J))) :
    IsLimit (loopFiberCone Y) :=
  PullbackCone.IsLimit.mk (loopInclusion_endpoint Y) (loopFiberLift Y)
    (loopFiberLift_fst Y) (loopFiberLift_snd Y) (loopFiberLift_unique Y)

/-- The actual native loop and every caller-chosen endpoint fiber have their strict limit Iso. -/
def chosenLoopFiberIso (Y : (Carrier (J := J))) :
    scalarLoop.obj Y ≅
      (a (basedPathUnresolvedArrowFunctor.obj Y)).pt :=
  (loopFiberConeIsLimit Y).conePointUniqueUpToIso
    (ha (basedPathUnresolvedArrowFunctor.obj Y))

/-- Its forward first projection is precisely the original sphere-quotient loop inclusion. -/
theorem chosenLoopFiberIso_hom_fst (Y : (Carrier (J := J))) :
    (chosenLoopFiberIso a ha Y).hom ≫
        (a (basedPathUnresolvedArrowFunctor.obj Y)).fst = loopInclusion Y :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left

/-- The forward zero projection retains the caller's whole original zero leg. -/
theorem chosenLoopFiberIso_hom_snd (Y : (Carrier (J := J))) :
    (chosenLoopFiberIso a ha Y).hom ≫
        (a (basedPathUnresolvedArrowFunctor.obj Y)).snd =
      Diagrams.toZero (scalarLoop.obj Y) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right

/-- The inverse keeps the complete first projection of the chosen original fiber. -/
theorem chosenLoopFiberIso_inv_fst (Y : (Carrier (J := J))) :
    (chosenLoopFiberIso a ha Y).inv ≫ loopInclusion Y =
      (a (basedPathUnresolvedArrowFunctor.obj Y)).fst :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.left

/-- The inverse also keeps the complete second projection. -/
theorem chosenLoopFiberIso_inv_snd (Y : (Carrier (J := J))) :
    (chosenLoopFiberIso a ha Y).inv ≫
        Diagrams.toZero (scalarLoop.obj Y) =
      (a (basedPathUnresolvedArrowFunctor.obj Y)).snd :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.right

/-- Full original maps preserve the strict loop-fiber Iso through both pullback projections. -/
theorem chosenLoopFiberIso_naturality {X Y : (Carrier (J := J))} (f : X ⟶ Y) :
    scalarLoop.map f ≫ (chosenLoopFiberIso a ha Y).hom =
      (chosenLoopFiberIso a ha X).hom ≫
        Diagrams.FiberGeometry.chosenFiberMap (basedPathUnresolvedArrowFunctor.map f)
          (a (basedPathUnresolvedArrowFunctor.obj X))
          (a (basedPathUnresolvedArrowFunctor.obj Y))
          (ha (basedPathUnresolvedArrowFunctor.obj Y)) := by
  apply PullbackCone.IsLimit.hom_ext (ha (basedPathUnresolvedArrowFunctor.obj Y))
  · rw [Category.assoc, chosenLoopFiberIso_hom_fst, Category.assoc,
      Diagrams.FiberGeometry.chosenFiberMap_fst, ← Category.assoc,
      chosenLoopFiberIso_hom_fst]
    exact loopInclusionNat.naturality f
  · exact Diagrams.zeroDiagramIsTerminal.hom_ext _ _

/-- The strict identification is natural on the entire original base family. -/
def chosenLoopFiberNatIso : scalarLoop ≅
    basedPathUnresolvedArrowFunctor ⋙ Diagrams.FiberGeometry.chosenFiberFunctor a ha :=
  NatIso.ofComponents (chosenLoopFiberIso a ha) (fun f =>
    chosenLoopFiberIso_naturality a ha f)

/-- The full loop-fiber inclusion preserves the original quotient under every input map. -/
theorem loopInclusion_naturality {X Y : Carrier (J := J)} (f : X ⟶ Y) :
    scalarLoop.map f ≫ loopInclusion Y = loopInclusion X ≫ basedPath.map f :=
  loopInclusionNat.naturality f

/-- Both actual chosen loop-fiber inverse maps are natural in the whole original base. -/
theorem chosenLoopFiberIso_inv_naturality {X Y : Carrier (J := J)} (f : X ⟶ Y) :
    Diagrams.FiberGeometry.chosenFiberMap (basedPathUnresolvedArrowFunctor.map f)
      (a (basedPathUnresolvedArrowFunctor.obj X))
      (a (basedPathUnresolvedArrowFunctor.obj Y))
      (ha (basedPathUnresolvedArrowFunctor.obj Y)) ≫
        (chosenLoopFiberIso a ha Y).inv =
      (chosenLoopFiberIso a ha X).inv ≫ scalarLoop.map f := by
  exact (chosenLoopFiberNatIso a ha).inv.naturality f

end StrictScalar
end LoopFiberUniversalProperty

end NativeBasedPathGeometry

end HomotopicalAlgebra.EnrichedProjective.Native.OriginalFiberCofiberGeometry
