/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarSphereSuspensionComparison
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarCompatibility
import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant

/-!
# Original I-cone suspension and scalar suspension on cofibrant diagrams

The comparison uses the same original cone-span and scalar disk-span weak
legs, joined through the original source-tensor unit and zero-span homotopy
pushout. All source objects and arrows remain the actual native enriched
diagrams. The component after the original Q replacement agrees with the
existing Q comparison; no new suspension or replacement choice is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OriginalISuspensionCofibrantComparison

/-- The coefficient source is exactly the original disk-boundary source. -/
abbrev coefficientSource : PointedCGWH.{u, v} :=
  (Arrow.mk PointedCGWH.diskBoundary.{u, v}).left

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

private abbrev D := EnrichedFunctorCat PointedCGWH.{u, v} I
attribute [local instance] Native.modelCategory

private instance nativeFactorization :
    CategoryTheory.MorphismProperty.HasFunctorialFactorization
      (cofibrations (D (I := I))) (trivialFibrations (D (I := I))) :=
  (Native.functorialFactorizations (B := B) (A := I)).1

private abbrev H := toHomotopyCategory (D (I := I))
private abbrev cι : CofibrantObject (D (I := I)) ⥤ D (I := I) := CofibrantObject.ι
private abbrev S := OriginalISuspension.suspension (B := B) (I := I)
private abbrev T := EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne.{u, v} (A := I)
private abbrev conePushout := OriginalISuspension.coneSpan (B := B) (I := I) ⋙ homotopyPushout
private abbrev zeroPushout := OriginalISuspension.zeroSpan (I := I) ⋙ homotopyPushout
private abbrev diskPushout := ScalarSphereSuspension.diskSpan (I := I) ⋙ homotopyPushout
private abbrev sourceZeroPushout :=
  (EnrichedFunctorCat.tensorLeft coefficientSource.{u, v} (A := I) ⋙
    OriginalISuspension.zeroSpan (I := I)) ⋙ homotopyPushout

private def weakMapIso {X Y : D (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (D (I := I)) f) : H.obj X ≅ H.obj Y := by
  let _ : IsIso (H.map f) := Localization.inverts H
    (weakEquivalences (D (I := I))) f hf
  exact asIso (H.map f)

/-- The first comparison is the original weak cone-span leg. -/
def coneSuspensionIso (X : D (I := I)) [IsCofibrant X] :
    H.obj (conePushout.obj X) ≅ H.obj (S.obj X) :=
  weakMapIso ((OriginalISuspension.toSuspension (B := B)).app X)
    (OriginalISuspension.toSuspension_weak X).mem

/-- The second comparison is the original cone collapse to the unchanged zero span. -/
def coneZeroIso (X : D (I := I)) :
    H.obj (conePushout.obj X) ≅ H.obj (zeroPushout.obj X) :=
  weakMapIso ((OriginalISuspension.toZeroPushout (B := B)).app X)
    (OriginalISuspension.toZeroPushout_weak X).mem

/-- The fourth comparison is the original scalar disk collapse. -/
def diskZeroIso (X : D (I := I)) [IsCofibrant X] :
    H.obj (diskPushout.obj X) ≅ H.obj (sourceZeroPushout.obj X) :=
  weakMapIso ((ScalarSphereSuspension.toZeroPushout (B := B)).app X)
    (ScalarSphereSuspension.toZeroPushout_weak X).mem

/-- The fifth comparison is the original scalar disk-to-sphere pushout leg. -/
def diskSphereIso (X : D (I := I)) [IsCofibrant X] :
    H.obj (diskPushout.obj X) ≅ H.obj (T.obj X) :=
  weakMapIso ((ScalarSphereSuspension.toSpherePushout (B := B)).app X)
    (ScalarSphereSuspension.toSpherePushout_weak X).mem

/-- The middle comparison retains the actual disk-source tensor unit and whole zero span. -/
def sourceZeroPushoutUnitNatIso :
    sourceZeroPushout (I := I) ⋙ H (I := I) ≅ zeroPushout (I := I) ⋙ H (I := I) :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (ScalarSphereSuspension.sourceTensorUnitIso (I := I))
        (OriginalISuspension.zeroSpan (I := I))) homotopyPushout) (H (I := I))

/-- The original cone-span map is a natural isomorphism on the actual cofibrant subcategory. -/
def coneSuspensionCofibrantNatIso :
    cι (I := I) ⋙ (conePushout (I := I) ⋙ H (I := I)) ≅
      cι (I := I) ⋙ (S (I := I) ⋙ H (I := I)) :=
  NatIso.ofComponents (fun X => coneSuspensionIso X.obj) (by
    intro X Y f
    exact (Functor.whiskerRight (OriginalISuspension.toSuspension (B := B)) H).naturality
      f.hom)

/-- The original cone collapse retains every cofibrant source arrow. -/
def coneZeroCofibrantNatIso :
    cι (I := I) ⋙ (conePushout (I := I) ⋙ H (I := I)) ≅
      cι (I := I) ⋙ (zeroPushout (I := I) ⋙ H (I := I)) :=
  NatIso.ofComponents (fun X => coneZeroIso X.obj) (by
    intro X Y f
    exact (Functor.whiskerRight (OriginalISuspension.toZeroPushout (B := B)) H).naturality
      f.hom)

/-- The scalar disk collapse retains every cofibrant source arrow. -/
def diskZeroCofibrantNatIso :
    cι (I := I) ⋙ (diskPushout (I := I) ⋙ H (I := I)) ≅
      cι (I := I) ⋙ (sourceZeroPushout (I := I) ⋙ H (I := I)) :=
  NatIso.ofComponents (fun X => diskZeroIso X.obj) (by
    intro X Y f
    exact (Functor.whiskerRight (ScalarSphereSuspension.toZeroPushout (B := B)) H).naturality
      f.hom)

/-- The scalar sphere comparison retains every cofibrant source arrow. -/
def diskSphereCofibrantNatIso :
    cι (I := I) ⋙ (diskPushout (I := I) ⋙ H (I := I)) ≅
      cι (I := I) ⋙ (T (I := I) ⋙ H (I := I)) :=
  NatIso.ofComponents (fun X => diskSphereIso X.obj) (by
    intro X Y f
    exact (Functor.whiskerRight (ScalarSphereSuspension.toSpherePushout (B := B)) H).naturality
      f.hom)

/-- The complete comparison on cofibrant diagrams uses exactly the original five legs. -/
def cofibrantNatIso : cι (I := I) ⋙ (S (I := I) ⋙ H (I := I)) ≅
    cι (I := I) ⋙ (T (I := I) ⋙ H (I := I)) :=
  (coneSuspensionCofibrantNatIso (I := I)).symm ≪≫ coneZeroCofibrantNatIso (I := I) ≪≫
    (Functor.isoWhiskerLeft (cι (I := I)) (sourceZeroPushoutUnitNatIso (I := I))).symm ≪≫
      (diskZeroCofibrantNatIso (I := I)).symm ≪≫ diskSphereCofibrantNatIso (I := I)

/-- The actual original I-cone suspension agrees with scalar suspension for every cofibrant X. -/
def comparison (X : D (I := I)) [IsCofibrant X] : H.obj (S.obj X) ≅ H.obj (T.obj X) :=
  (cofibrantNatIso (B := B)).app (CofibrantObject.mk X)

/-- The forward map retains all four original weak maps and the source-tensor-unit component. -/
theorem comparison_hom (X : D (I := I)) [IsCofibrant X] :
    (comparison X).hom =
      (coneSuspensionIso X).inv ≫ (coneZeroIso X).hom ≫
        (sourceZeroPushoutUnitNatIso (B := B)).inv.app X ≫
          (diskZeroIso X).inv ≫ (diskSphereIso X).hom := rfl

/-- The inverse map reverses the same original five comparison legs. -/
theorem comparison_inv (X : D (I := I)) [IsCofibrant X] :
    (comparison X).inv =
      (diskSphereIso X).inv ≫ (diskZeroIso X).hom ≫
        (sourceZeroPushoutUnitNatIso (B := B)).hom.app X ≫
          (coneZeroIso X).inv ≫ (coneSuspensionIso X).hom := by
  dsimp [comparison, cofibrantNatIso, coneSuspensionCofibrantNatIso,
    coneZeroCofibrantNatIso, diskZeroCofibrantNatIso, diskSphereCofibrantNatIso]
  simp only [Category.assoc]

/-- Every cofibrant source map keeps the complete forward comparison square. -/
theorem comparison_hom_naturality {X Y : D (I := I)} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) :
    H.map (S.map f) ≫ (comparison Y).hom = (comparison X).hom ≫ H.map (T.map f) :=
  (cofibrantNatIso (B := B)).hom.naturality (CofibrantObject.homMk f)

/-- Every cofibrant source map keeps the complete inverse comparison square. -/
theorem comparison_inv_naturality {X Y : D (I := I)} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) :
    H.map (T.map f) ≫ (comparison Y).inv = (comparison X).inv ≫ H.map (S.map f) :=
  (cofibrantNatIso (B := B)).inv.naturality (CofibrantObject.homMk f)

/-- Both complete comparison functions retain the first actual quotient triangle. -/
theorem comparison_hom_inv (X : D (I := I)) [IsCofibrant X] :
    (comparison X).hom ≫ (comparison X).inv = 𝟙 (H.obj (S.obj X)) :=
  (comparison X).hom_inv_id

/-- Both complete comparison functions retain the second actual quotient triangle. -/
theorem comparison_inv_hom (X : D (I := I)) [IsCofibrant X] :
    (comparison X).inv ≫ (comparison X).hom = 𝟙 (H.obj (T.obj X)) :=
  (comparison X).inv_hom_id

private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := I)

/-- Evaluate the same cofibrant comparison at the original Q object. -/
def comparisonQ (X : D (I := I)) : H.obj (S.obj (Q.obj X)) ≅ H.obj (T.obj (Q.obj X)) := by
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := I) X
  exact comparison (Q.obj X)

/-- The forward Q component is the existing original natural comparison component. -/
theorem comparisonQ_hom_eq_original (X : D (I := I)) :
    (comparisonQ X).hom =
      (ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B)).hom.app X := by
  dsimp [comparisonQ, comparison, cofibrantNatIso, coneSuspensionCofibrantNatIso,
    coneZeroCofibrantNatIso, diskZeroCofibrantNatIso, diskSphereCofibrantNatIso,
    ScalarSphereSuspension.originalISuspensionQIsoSphereQ,
    OriginalISuspension.suspensionQIsoZeroPushoutQ,
    ScalarSphereSuspension.zeroSourceQIsoSphereQ, sourceZeroPushoutUnitNatIso,
    coneSuspensionIso, coneZeroIso, diskZeroIso, diskSphereIso, weakMapIso]
  simp only [NatIso.isIso_inv_app]
  dsimp only [Functor.whiskerRight, Functor.whiskerLeft]
  simp only [Category.assoc]

/-- Both Q comparison functions are exactly the existing original comparison isomorphism. -/
theorem comparisonQ_eq_original (X : D (I := I)) :
    comparisonQ X = (ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B)).app X := by
  apply Iso.ext
  exact comparisonQ_hom_eq_original X

/-- The full inverse Q component is the existing original inverse component. -/
theorem comparisonQ_inv_eq_original (X : D (I := I)) :
    (comparisonQ X).inv =
      (ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B)).inv.app X :=
  congrArg (fun e => e.inv) (comparisonQ_eq_original X)

/-- The source arrow of Q remains the same original factorization map in the forward square. -/
theorem comparisonQ_hom_naturality {X Y : D (I := I)} (f : X ⟶ Y) :
    H.map (S.map (Q.map f)) ≫ (comparisonQ Y).hom =
      (comparisonQ X).hom ≫ H.map (T.map (Q.map f)) := by
  rw [comparisonQ_hom_eq_original, comparisonQ_hom_eq_original]
  exact ScalarSphereSuspension.originalISuspensionQIsoSphereQ_hom_naturality f

/-- The inverse Q square retains the same entire original factorization map. -/
theorem comparisonQ_inv_naturality {X Y : D (I := I)} (f : X ⟶ Y) :
    H.map (T.map (Q.map f)) ≫ (comparisonQ Y).inv =
      (comparisonQ X).inv ≫ H.map (S.map (Q.map f)) := by
  rw [comparisonQ_inv_eq_original, comparisonQ_inv_eq_original]
  exact ScalarSphereSuspension.originalISuspensionQIsoSphereQ_inv_naturality f

/-- Transport the original I-suspended cofibrant map through both complete comparison functions. -/
theorem comparison_transport_map {X Y : D (I := I)} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) :
    (comparison X).inv ≫ H.map (S.map f) ≫ (comparison Y).hom = H.map (T.map f) := by
  rw [comparison_hom_naturality, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := I)

/-- Scalar suspension sends the original Q counit of a cofibrant object to a level weak map. -/
theorem scalarCounit_weak (X : D (I := I)) [IsCofibrant X] :
    WeakEquivalence (T.map (ε.app X)) := by
  let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
    PointedCGWH.modelCategory.sphereOne_isCofibrant
  let _ : (EnrichedFunctorCat.ScalarLeibniz.adjunction (A := I)
      PointedCGWH.sphereOne).IsQuillenAdjunction :=
    ScalarCompatibility.scalar_isQuillen PointedCGWH.sphereOne
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := I) X
  let _ : IsCofibrant ((𝟭 (D (I := I))).obj X) := inferInstanceAs (IsCofibrant X)
  let _ : WeakEquivalence (ε.app X) := (weakEquivalence_iff _).mpr
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) X)
  exact Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
    (adj := EnrichedFunctorCat.ScalarLeibniz.adjunction PointedCGWH.sphereOne) (ε.app X)

/-- The scalar image of the actual Q counit has both original localization functions. -/
def scalarCounitIso (X : D (I := I)) [IsCofibrant X] :
    H.obj (T.obj (Q.obj X)) ≅ H.obj (T.obj X) :=
  weakMapIso (T.map (ε.app X)) (scalarCounit_weak X).mem

/-- The complete forward scalar-counit function is its unchanged original image map. -/
theorem scalarCounitIso_hom (X : D (I := I)) [IsCofibrant X] :
    (scalarCounitIso X).hom = H.map (T.map (ε.app X)) := rfl

/-- Both scalar-counit functions agree with the original weak-arrow localization Iso. -/
theorem scalarCounitIso_eq_wIso (X : D (I := I)) [IsCofibrant X] :
    scalarCounitIso X =
      Localization.Construction.wIso (T.map (ε.app X)) (scalarCounit_weak X).mem := by
  apply Iso.ext
  rfl

/-- Scalar suspension retains every cofibrant source map in the actual counit square. -/
theorem scalarCounitIso_hom_naturality {X Y : D (I := I)}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    H.map (T.map (Q.map f)) ≫ (scalarCounitIso Y).hom =
      (scalarCounitIso X).hom ≫ H.map (T.map f) := by
  simp only [scalarCounitIso_hom, ← Functor.map_comp]
  exact H.congr_map (T.congr_map (ε.naturality f))

/-- The original I-Q suspension compares with the scalar suspension of every cofibrant X. -/
def comparisonWithCounit (X : D (I := I)) [IsCofibrant X] :
    H.obj (S.obj (Q.obj X)) ≅ H.obj (T.obj X) :=
  comparisonQ X ≪≫ scalarCounitIso X

/-- The full comparison with the counit is natural on the actual cofibrant source category. -/
def comparisonWithCounitNatIso :
    cι (I := I) ⋙ ((Q (I := I) ⋙ S (I := I)) ⋙ H (I := I)) ≅
      cι (I := I) ⋙ (T (I := I) ⋙ H (I := I)) :=
  NatIso.ofComponents (fun X => comparisonWithCounit X.obj) (by
    intro X Y f
    change H.map (S.map (Q.map f.hom)) ≫
        ((comparisonQ Y.obj).hom ≫ (scalarCounitIso Y.obj).hom) =
      ((comparisonQ X.obj).hom ≫ (scalarCounitIso X.obj).hom) ≫ H.map (T.map f.hom)
    rw [← Category.assoc, comparisonQ_hom_naturality, Category.assoc,
      scalarCounitIso_hom_naturality, ← Category.assoc])

/-- Every cofibrant source map preserves the entire forward I-Q/scalar counit comparison. -/
theorem comparisonWithCounit_hom_naturality {X Y : D (I := I)}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    H.map (S.map (Q.map f)) ≫ (comparisonWithCounit Y).hom =
      (comparisonWithCounit X).hom ≫ H.map (T.map f) :=
  (comparisonWithCounitNatIso (B := B)).hom.naturality (CofibrantObject.homMk f)

/-- Every cofibrant source map preserves the entire inverse I-Q/scalar counit comparison. -/
theorem comparisonWithCounit_inv_naturality {X Y : D (I := I)}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    H.map (T.map f) ≫ (comparisonWithCounit Y).inv =
      (comparisonWithCounit X).inv ≫ H.map (S.map (Q.map f)) :=
  (comparisonWithCounitNatIso (B := B)).inv.naturality (CofibrantObject.homMk f)

/-- An arbitrary map after the original counit is normalized through the actual scalar counit. -/
theorem comparisonWithCounit_transport {X Y : D (I := I)} [IsCofibrant X]
    (g : X ⟶ Q.obj Y) :
    (comparisonWithCounit X).inv ≫ H.map (S.map (ε.app X ≫ g)) ≫
      (comparisonQ Y).hom = H.map (T.map g) := by
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := I) X
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := I) Y
  have h := comparison_transport_map (ε.app X ≫ g)
  change (comparisonQ X).inv ≫ H.map (S.map (ε.app X ≫ g)) ≫
      (comparisonQ Y).hom = H.map (T.map (ε.app X ≫ g)) at h
  change ((scalarCounitIso X).inv ≫ (comparisonQ X).inv) ≫
    H.map (S.map (ε.app X ≫ g)) ≫ (comparisonQ Y).hom = _
  rw [Category.assoc, h, Functor.map_comp, Functor.map_comp,
    ← scalarCounitIso_hom, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- A caller's actual scalar coefficient Iso extends the same I-Q comparison. -/
def comparisonWithCounitToIso (X : D (I := I)) [IsCofibrant X]
    {Z : D (I := I)} (e : T.obj X ≅ Z) : H.obj (S.obj (Q.obj X)) ≅ H.obj Z :=
  comparisonWithCounit X ≪≫ H.mapIso e

/-- The inverse caller comparison retains its actual coefficient inverse and original counit. -/
theorem comparisonWithCounitToIso_transport {X Y Z : D (I := I)} [IsCofibrant X]
    (e : T.obj X ≅ Z) (g : X ⟶ Q.obj Y) :
    (comparisonWithCounitToIso X e).inv ≫ H.map (S.map (ε.app X ≫ g)) ≫
      (comparisonQ Y).hom = H.map e.inv ≫ H.map (T.map g) := by
  change (H.map e.inv ≫ (comparisonWithCounit X).inv) ≫
    H.map (S.map (ε.app X ≫ g)) ≫ (comparisonQ Y).hom = _
  rw [Category.assoc, comparisonWithCounit_transport]

/-- The suspension cocone is the actual original I inclusion against the original zero endpoint. -/
abbrev originalSuspensionCocone (X : D (I := I)) :
    PushoutCocone ((OriginalICone.inclusion (B := B)).app X) (Diagrams.toZero X) :=
  OriginalISuspension.cocone (B := B) (Arrow.mk (Diagrams.toZero X))

/-- The original suspension cocone has its actual chosen colimit property. -/
def originalSuspensionCoconeIsColimit (X : D (I := I)) :
    IsColimit (originalSuspensionCocone X) :=
  OriginalISuspension.coconeIsColimit (B := B) (Arrow.mk (Diagrams.toZero X))

/-- The original suspension map retains its complete original cone-source leg. -/
theorem originalSuspensionMap_cone {X Y : D (I := I)} (f : X ⟶ Y) :
    (originalSuspensionCocone X).inl ≫ S.map f =
      (OriginalICone.cone (B := B)).map f ≫ (originalSuspensionCocone Y).inl :=
  OrdinaryHoChosenPuppe.suspensionMap_cone
    (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B))
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero f

/-- The original suspension map retains its complete unchanged native zero leg. -/
theorem originalSuspensionMap_zero {X Y : D (I := I)} (f : X ⟶ Y) :
    (originalSuspensionCocone X).inr ≫ S.map f = (originalSuspensionCocone Y).inr :=
  OrdinaryHoChosenPuppe.suspensionMap_zero
    (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B))
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero f

section CallerSuspension

variable (s : ∀ X : D (I := I),
    PushoutCocone ((OriginalICone.inclusion (B := B)).app X) (Diagrams.toZero X))
  (hs : ∀ X, IsColimit (s X))

/-- A caller's suspension map is the actual colimit desc on the same original I span. -/
def callerSuspensionMap {X Y : D (I := I)} (f : X ⟶ Y) : (s X).pt ⟶ (s Y).pt :=
  PushoutCocone.IsColimit.desc (hs X)
    ((OriginalICone.cone (B := B)).map f ≫ (s Y).inl) (s Y).inr (by
      rw [← Category.assoc, ← (OriginalICone.inclusion (B := B)).naturality f,
        Category.assoc, (s Y).condition, ← Category.assoc]
      change (f ≫ Diagrams.toZero Y) ≫ (s Y).inr = Diagrams.toZero X ≫ (s Y).inr
      rw [Diagrams.toZero_naturality])

/-- The caller desc keeps the entire original cone functor map and chosen cone leg. -/
theorem callerSuspensionMap_cone {X Y : D (I := I)} (f : X ⟶ Y) :
    (s X).inl ≫ callerSuspensionMap s hs f =
      (OriginalICone.cone (B := B)).map f ≫ (s Y).inl :=
  PushoutCocone.IsColimit.inl_desc (hs X) _ _ _

/-- The caller desc keeps its complete original zero endpoint leg. -/
theorem callerSuspensionMap_zero {X Y : D (I := I)} (f : X ⟶ Y) :
    (s X).inr ≫ callerSuspensionMap s hs f = (s Y).inr :=
  PushoutCocone.IsColimit.inr_desc (hs X) _ _ _

/-- Every identity uses the same original source and target functions of the caller desc. -/
theorem callerSuspensionMap_id (X : D (I := I)) :
    callerSuspensionMap s hs (𝟙 X) = 𝟙 (s X).pt := by
  apply PushoutCocone.IsColimit.hom_ext (hs X)
  · rw [callerSuspensionMap_cone, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id]
  · rw [callerSuspensionMap_zero, Category.comp_id]

/-- Every caller suspension composite retains the two same entire original span maps. -/
theorem callerSuspensionMap_comp {X Y Z : D (I := I)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    callerSuspensionMap s hs (f ≫ g) =
      callerSuspensionMap s hs f ≫ callerSuspensionMap s hs g := by
  apply PushoutCocone.IsColimit.hom_ext (hs X)
  · rw [callerSuspensionMap_cone, ← Category.assoc, callerSuspensionMap_cone,
      Category.assoc, callerSuspensionMap_cone, Functor.map_comp, Category.assoc]
  · rw [callerSuspensionMap_zero, ← Category.assoc, callerSuspensionMap_zero,
      callerSuspensionMap_zero]

/-- Independent caller suspension choices form a functor through their actual original descs. -/
def callerSuspensionFunctor : D (I := I) ⥤ D (I := I) where
  obj X := (s X).pt
  map := callerSuspensionMap s hs
  map_id := callerSuspensionMap_id s hs
  map_comp := callerSuspensionMap_comp s hs

/-- Actual colimit uniqueness compares the original suspension to each caller's chosen cocone. -/
def callerSuspensionIso (X : D (I := I)) : S.obj X ≅ (s X).pt :=
  (originalSuspensionCoconeIsColimit X).coconePointUniqueUpToIso (hs X)

/-- The forward choice comparison preserves the entire original cone leg. -/
theorem callerSuspensionIso_hom_cone (X : D (I := I)) :
    (originalSuspensionCocone X).inl ≫ (callerSuspensionIso s hs X).hom = (s X).inl :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (originalSuspensionCoconeIsColimit X) (hs X) WalkingSpan.left

/-- The forward choice comparison preserves the entire original zero leg. -/
theorem callerSuspensionIso_hom_zero (X : D (I := I)) :
    (originalSuspensionCocone X).inr ≫ (callerSuspensionIso s hs X).hom = (s X).inr :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (originalSuspensionCoconeIsColimit X) (hs X) WalkingSpan.right

/-- The inverse choice comparison preserves the same complete cone-source leg. -/
theorem callerSuspensionIso_inv_cone (X : D (I := I)) :
    (s X).inl ≫ (callerSuspensionIso s hs X).inv = (originalSuspensionCocone X).inl :=
  IsColimit.comp_coconePointUniqueUpToIso_inv
    (originalSuspensionCoconeIsColimit X) (hs X) WalkingSpan.left

/-- The inverse choice comparison preserves the same complete original zero leg. -/
theorem callerSuspensionIso_inv_zero (X : D (I := I)) :
    (s X).inr ≫ (callerSuspensionIso s hs X).inv = (originalSuspensionCocone X).inr :=
  IsColimit.comp_coconePointUniqueUpToIso_inv
    (originalSuspensionCoconeIsColimit X) (hs X) WalkingSpan.right

/-- Every caller choice compares naturally with the entire original I suspension. -/
def callerSuspensionNatIso : S (I := I) ≅ callerSuspensionFunctor s hs :=
  NatIso.ofComponents (callerSuspensionIso s hs) (by
    intro X Y f
    change S.map f ≫ (callerSuspensionIso s hs Y).hom =
      (callerSuspensionIso s hs X).hom ≫ callerSuspensionMap s hs f
    apply PushoutCocone.IsColimit.hom_ext (originalSuspensionCoconeIsColimit X)
    · rw [← Category.assoc, originalSuspensionMap_cone, Category.assoc,
        callerSuspensionIso_hom_cone, ← Category.assoc, callerSuspensionIso_hom_cone,
        callerSuspensionMap_cone]
    · rw [← Category.assoc, originalSuspensionMap_zero, callerSuspensionIso_hom_zero,
        ← Category.assoc, callerSuspensionIso_hom_zero, callerSuspensionMap_zero])

/-- Every actual caller source map retains the full forward colimit-choice square. -/
theorem callerSuspensionIso_hom_naturality {X Y : D (I := I)} (f : X ⟶ Y) :
    S.map f ≫ (callerSuspensionIso s hs Y).hom =
      (callerSuspensionIso s hs X).hom ≫ (callerSuspensionFunctor s hs).map f :=
  (callerSuspensionNatIso s hs).hom.naturality f

/-- Every actual caller source map retains the full inverse colimit-choice square. -/
theorem callerSuspensionIso_inv_naturality {X Y : D (I := I)} (f : X ⟶ Y) :
    (callerSuspensionFunctor s hs).map f ≫ (callerSuspensionIso s hs Y).inv =
      (callerSuspensionIso s hs X).inv ≫ S.map f :=
  (callerSuspensionNatIso s hs).inv.naturality f

/-- The caller's chosen suspension has the same full scalar comparison on cofibrant objects. -/
def callerCofibrantNatIso :
    cι (I := I) ⋙ (callerSuspensionFunctor s hs ⋙ H (I := I)) ≅
      cι (I := I) ⋙ (T (I := I) ⋙ H (I := I)) :=
  (Functor.isoWhiskerLeft (cι (I := I))
    (Functor.isoWhiskerRight (callerSuspensionNatIso s hs) (H (I := I)))).symm ≪≫
      cofibrantNatIso (B := B)

/-- Each cofibrant caller comparison uses actual colimit uniqueness and the original weak span. -/
def callerComparison (X : D (I := I)) [IsCofibrant X] :
    H.obj ((s X).pt) ≅ H.obj (T.obj X) :=
  (callerCofibrantNatIso s hs).app (CofibrantObject.mk X)

/-- The entire caller forward function keeps its choice inverse and original five-leg comparison. -/
theorem callerComparison_hom (X : D (I := I)) [IsCofibrant X] :
    (callerComparison s hs X).hom = H.map (callerSuspensionIso s hs X).inv ≫
      (comparison X).hom := rfl

/-- The entire caller inverse keeps the original five-leg inverse and actual choice forward map. -/
theorem callerComparison_inv (X : D (I := I)) [IsCofibrant X] :
    (callerComparison s hs X).inv = (comparison X).inv ≫
      H.map (callerSuspensionIso s hs X).hom := rfl

/-- All cofibrant caller source arrows preserve both actual comparison endpoints. -/
theorem callerComparison_hom_naturality {X Y : D (I := I)}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    H.map ((callerSuspensionFunctor s hs).map f) ≫ (callerComparison s hs Y).hom =
      (callerComparison s hs X).hom ≫ H.map (T.map f) :=
  (callerCofibrantNatIso s hs).hom.naturality (CofibrantObject.homMk f)

/-- All cofibrant caller source arrows preserve the entire inverse comparison square. -/
theorem callerComparison_inv_naturality {X Y : D (I := I)}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    H.map (T.map f) ≫ (callerComparison s hs Y).inv =
      (callerComparison s hs X).inv ≫ H.map ((callerSuspensionFunctor s hs).map f) :=
  (callerCofibrantNatIso s hs).inv.naturality (CofibrantObject.homMk f)

/-- Caller choices retain the same original whole Q map before suspension. -/
def callerISuspensionQNatIso : Q (I := I) ⋙ S (I := I) ≅
    Q (I := I) ⋙ callerSuspensionFunctor s hs :=
  Functor.isoWhiskerLeft Q (callerSuspensionNatIso s hs)

/-- The full caller I-Q/scalar-Q comparison keeps the original Q weak span unchanged. -/
def callerIQScalarNatIso : (Q (I := I) ⋙ callerSuspensionFunctor s hs) ⋙ H (I := I) ≅
    (Q (I := I) ⋙ T (I := I)) ⋙ H (I := I) :=
  (Functor.isoWhiskerRight (callerISuspensionQNatIso s hs) H).symm ≪≫
    ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B)

/-- The original Q evaluation of the caller's cofibrant comparison is the whole caller Q Iso. -/
theorem callerComparisonQ_eq_original (X : D (I := I)) :
    letI := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := I) X
    callerComparison s hs (Q.obj X) = (callerIQScalarNatIso s hs).app X := by
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := I) X
  apply Iso.ext
  rw [callerComparison_hom]
  change H.map (callerSuspensionIso s hs (Q.obj X)).inv ≫ (comparisonQ X).hom = _
  rw [comparisonQ_hom_eq_original]
  rfl

end CallerSuspension

end HomotopicalAlgebra.EnrichedProjective.Native.OriginalISuspensionCofibrantComparison
