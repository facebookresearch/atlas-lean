/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeIdentityComplexesStack
import Mathlib.CategoryTheory.ObjectProperty.Equivalence


/-!
# Classical identity source transport equivalence

The actual projection inverse image induces an equivalence between the
classical complexes fibre and the native identity-situation complexes fibre.
The proof uses normalized module pullbacks and their total left derivations.

References: Toën--Vaquié math/0503269v5 §3.1 pp36--37 and p8;
Stacks 03G8, 06YY, 0D6D, 0DLD/0DLE. The native ordinary-stack source
is ComplexesStack.lean at AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b; its general algebraic-space
algebraicity theorem is not re-requested here.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.EtaleComplexesPullbackCoherence
open MathlibExt.AlgebraicGeometry.NativeIdentityComplexesStack
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
noncomputable section

private def baseId (X : Scheme.{u}) : EtaleBaseChangeUnitSource X where
  iso := NatIso.ofComponents
    (fun (U : X.Etale) => MorphismProperty.Over.isoMk (asIso (pullback.fst U.hom (𝟙 X)))
      (by simpa [etaleBaseChange, MorphismProperty.Over.pullback] using
        (pullback.condition (f := U.hom) (g := 𝟙 X))))
    (by
      intro U V a
      apply MorphismProperty.Over.Hom.ext
      change pullback.lift _ _ _ ≫ pullback.fst V.hom (𝟙 X) =
        pullback.fst U.hom (𝟙 X) ≫ a.left
      simp)
  normalized U := rfl

private theorem ringId (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) (X : Scheme.{u}) :
    letI := (L.ringed (𝟙 X)).continuous
    (𝟙 (etaleStructureRing O X)) ≫
      (Functor.sheafPushforwardContinuousNatTrans (baseId X).iso.hom _ _ _).app
        (etaleStructureRing O X) = (L.ringed (𝟙 X)).ringMap := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  obtain ⟨U⟩ := U
  change (forget₂ CommRingCat RingCat).map
      (Scheme.Γ.map (op ((baseId X).iso.hom.app U).left)) =
        (L.ringed (𝟙 X)).ringMap.hom.app (op U)
  rw [(L.ringed (𝟙 X)).ringMap_eq]
  rfl

private theorem ringIdInv (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) (X : Scheme.{u}) :
    letI := (L.ringed (𝟙 X)).continuous
    (L.ringed (𝟙 X)).ringMap ≫
      (Functor.sheafPushforwardContinuousNatTrans (baseId X).iso.inv _ _ _).app
        (etaleStructureRing O X) = 𝟙 (etaleStructureRing O X) := by
  let := (L.ringed (𝟙 X)).continuous
  rw [← ringId O L X]
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  obtain ⟨U⟩ := U
  change (etaleStructureRing O X).obj.map ((baseId X).iso.hom.app U).op ≫
    (etaleStructureRing O X).obj.map ((baseId X).iso.inv.app U).op = 𝟙 _
  simp [← Functor.map_comp, ← op_comp]

private def rawId (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) (X : Scheme.{u}) :
    etaleModulePushforward (L.ringed (𝟙 X)) ≅ 𝟭 (EtaleModules O X) := by
  letI := (L.ringed (𝟙 X)).continuous
  let e := SheafOfModules.pushforwardNatIso (L.ringed (𝟙 X)).ringMap (baseId X).iso.symm
  let e' := SheafOfModules.pushforwardCongr.{u} (ringIdInv O L X)
  exact e ≪≫ e' ≪≫ SheafOfModules.pushforwardId (etaleStructureRing O X)

private def rawComp (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleModulePushforward (L.ringed (f ≫ g)) ≅
      etaleModulePushforward (L.ringed f) ⋙ etaleModulePushforward (L.ringed g) := by
  letI := (L.ringed f).continuous
  letI := (L.ringed g).continuous
  letI := (L.ringed (f ≫ g)).continuous
  letI := Functor.isContinuous_comp (etaleBaseChange g) (etaleBaseChange f)
    Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology
  have h : (L.ringed (f ≫ g)).ringMap ≫
      (Functor.sheafPushforwardContinuousNatTrans (etaleBaseChangeComp f g).inv _ _ _).app
        (etaleStructureRing O X) = (L.ringed g).ringMap ≫
          ((etaleBaseChange g).sheafPushforwardContinuous _ _ _).map (L.ringed f).ringMap := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    obtain ⟨U⟩ := U
    change (L.ringed (f ≫ g)).ringMap.hom.app (op U) ≫ _ =
      (L.ringed g).ringMap.hom.app (op U) ≫
        (L.ringed f).ringMap.hom.app (op ((etaleBaseChange g).obj U))
    rw [(L.ringed (f ≫ g)).ringMap_eq, (L.ringed g).ringMap_eq,
      (L.ringed f).ringMap_eq]
    change (forget₂ CommRingCat RingCat).map
        (Scheme.Γ.map (pullback.fst U.hom (f ≫ g)).op) ≫
      (forget₂ CommRingCat RingCat).map
        (Scheme.Γ.map ((etaleBaseChangeComp f g).inv.app U).left.op) =
      (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (pullback.fst U.hom g).op) ≫
        (forget₂ CommRingCat RingCat).map
          (Scheme.Γ.map (pullback.fst (pullback.snd U.hom g) f).op)
    simp only [← Functor.map_comp, ← op_comp]
    simp [etaleBaseChangeComp, MorphismProperty.Over.pullbackComp]
  exact SheafOfModules.pushforwardCongr₂ (φ := (L.ringed (f ≫ g)).ringMap)
    (etaleBaseChangeComp f g).symm h ≪≫
      (SheafOfModules.pushforwardComp (L.ringed g).ringMap (L.ringed f).ringMap).symm

private def coherence (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) : EtalePushforwardCoherence L where
  baseId := baseId
  idIso := rawId O L
  id_eq X M U := by
    ext x
    rfl
  compIso := rawComp O L
  comp_eq f g M U := by
    ext x
    rfl

private def rawEquivalence (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) {X Y : Scheme.{u}} (e : X ≅ Y) :
    EtaleModules O X ≌ EtaleModules O Y :=
  CategoryTheory.Equivalence.mk (etaleModulePushforward (L.ringed e.hom))
    (etaleModulePushforward (L.ringed e.inv))
    ((rawId O L X).symm ≪≫
      (eqToIso (congrArg (fun f : X ⟶ X => etaleModulePushforward (L.ringed f))
        e.hom_inv_id)).symm ≪≫ rawComp O L e.hom e.inv)
    ((rawComp O L e.inv e.hom).symm ≪≫
      eqToIso (congrArg (fun f : Y ⟶ Y => etaleModulePushforward (L.ringed f))
        e.inv_hom_id) ≪≫ rawId O L Y)

private theorem rawPullback_equivalence (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    (etaleModulePullback (L.ringed f)).IsEquivalence := by
  have : (etaleModulePushforward (L.ringed f)).IsEquivalence :=
    (rawEquivalence O L (asIso f)).isEquivalence_functor
  exact (etalePullPushAdjunction (L.ringed f)).isEquivalence_left_of_isEquivalence_right
attribute [local instance] HasDerivedCategory.standard

private def derivedIso (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    letI := rawPullback_equivalence O L f
    etaleDerivedPullback (L.derived f) ≅ (etaleModulePullback (L.ringed f)).mapDerivedCategory := by
  letI := rawPullback_equivalence O L f
  let := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (EtaleModules O Y) (.up ℤ))
    (etaleModulePullback (L.ringed f)).mapDerivedCategory
    (etaleModulePullback (L.ringed f)).mapDerivedCategoryFactors
  exact Functor.leftDerivedUnique (etaleModulePullback (L.ringed f)).mapDerivedCategory
    (etaleDerivedPullback (L.derived f)) (etaleDerivedPullbackCounit (L.derived f))
    (etaleModulePullback (L.ringed f)).mapDerivedCategoryFactors.hom
    (HomologicalComplex.quasiIso (EtaleModules O Y) (.up ℤ))

private theorem mapDerived_equivalence (C D : Type*) [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence] : F.mapDerivedCategory.IsEquivalence := by
  let Φ := F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)
  have : Φ.functor.IsEquivalence :=
    (F.asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  have : Φ.IsInduced := by
    constructor
    ext K L f
    exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology f F
  have := Φ.isLocalizedEquivalence_of_isInduced
  exact Φ.localizedFunctor_isEquivalence DerivedCategory.Q DerivedCategory.Q

private theorem derived_equivalence (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    (etaleDerivedPullback (L.derived f)).IsEquivalence := by
  let := rawPullback_equivalence O L f
  have := mapDerived_equivalence _ _ (etaleModulePullback (L.ringed f))
  exact Functor.isEquivalence_of_iso (derivedIso O L f).symm

private def derivedCompIso (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIso g] : etaleDerivedPullback (L.derived (f ≫ g)) ≅
      etaleDerivedPullback (L.derived g) ⋙ etaleDerivedPullback (L.derived f) := by
  letI := rawPullback_equivalence O L g
  let G := (etaleModulePullback (L.ringed g)).mapHomologicalComplex (.up ℤ)
  let G' := (etaleModulePullback (L.ringed g)).mapDerivedCategory
  have : G.IsEquivalence :=
    ((etaleModulePullback (L.ringed g)).asEquivalence.mapHomologicalComplex
      (.up ℤ)).isEquivalence_functor
  have : G'.IsEquivalence := mapDerived_equivalence _ _ (etaleModulePullback (L.ringed g))
  let e : etalePullbackBeforeDeriving (L.ringed (f ≫ g)) ≅
      G ⋙ etalePullbackBeforeDeriving (L.ringed f) :=
    Functor.isoWhiskerRight (etaleRawComplexComp (coherence O L) f g).symm DerivedCategory.Q ≪≫
      Functor.associator _ _ _
  let α : DerivedCategory.Q ⋙ (G' ⋙ etaleDerivedPullback (L.derived f)) ⟶
      etalePullbackBeforeDeriving (L.ringed (f ≫ g)) :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (etaleModulePullback (L.ringed g)).mapDerivedCategoryFactors.hom _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft G (etaleDerivedPullbackCounit (L.derived f)) ≫ e.inv
  have : (G' ⋙ etaleDerivedPullback (L.derived f)).IsRightKanExtension α := by
    apply (Functor.isRightKanExtension_iff_precomp_equivalence α
      (etaleDerivedPullbackCounit (L.derived f))
      (etaleModulePullback (L.ringed g)).mapDerivedCategoryFactors.symm e (Iso.refl _)
      (by ext E; simp [α, G, G'])).mp
    exact Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomologicalComplex.quasiIso (EtaleModules O Y) (.up ℤ))
  have : (G' ⋙ etaleDerivedPullback (L.derived f)).IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (EtaleModules O Z) (.up ℤ)) := ⟨this⟩
  exact Functor.leftDerivedUnique (G' ⋙ etaleDerivedPullback (L.derived f))
    (etaleDerivedPullback (L.derived (f ≫ g)))
    (etaleDerivedPullbackCounit (L.derived (f ≫ g))) α
    (HomologicalComplex.quasiIso (EtaleModules O Z) (.up ℤ)) ≪≫
      Functor.isoWhiskerRight (derivedIso O L g).symm (etaleDerivedPullback (L.derived f))

private theorem derivedCounit_isIso (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    IsIso (etaleDerivedPullbackCounit (L.derived f)) := by
  let := rawPullback_equivalence O L f
  exact Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    (etaleDerivedPullback (L.derived f)) (etaleDerivedPullbackCounit (L.derived f))
    (((etaleModulePullback (L.ringed f)).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (.up ℤ)).inverts DerivedCategory.Q)

private def derivedCompIsoLeft (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIso f] : etaleDerivedPullback (L.derived (f ≫ g)) ≅
      etaleDerivedPullback (L.derived g) ⋙ etaleDerivedPullback (L.derived f) := by
  have := derived_equivalence O L f
  have := derivedCounit_isIso O L f
  let e : etalePullbackBeforeDeriving (L.ringed g) ⋙ etaleDerivedPullback (L.derived f) ≅
      etalePullbackBeforeDeriving (L.ringed (f ≫ g)) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((etaleModulePullback (L.ringed g)).mapHomologicalComplex (.up ℤ))
        (asIso (etaleDerivedPullbackCounit (L.derived f))) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (etaleRawComplexComp (coherence O L) f g) DerivedCategory.Q
  let α := (Functor.associator DerivedCategory.Q (etaleDerivedPullback (L.derived g))
    (etaleDerivedPullback (L.derived f))).inv ≫
      Functor.whiskerRight (etaleDerivedPullbackCounit (L.derived g))
        (etaleDerivedPullback (L.derived f))
  have : (etaleDerivedPullback (L.derived g) ⋙
      etaleDerivedPullback (L.derived f)).IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (EtaleModules O Z) (.up ℤ)) := inferInstance
  have : (etaleDerivedPullback (L.derived g) ⋙
      etaleDerivedPullback (L.derived f)).IsRightKanExtension α :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomologicalComplex.quasiIso (EtaleModules O Z) (.up ℤ))
  have : (etaleDerivedPullback (L.derived g) ⋙
      etaleDerivedPullback (L.derived f)).IsLeftDerivedFunctor
      (α ≫ e.hom) (HomologicalComplex.quasiIso (EtaleModules O Z) (.up ℤ)) := ⟨inferInstance⟩
  exact Functor.leftDerivedUnique
    (etaleDerivedPullback (L.derived g) ⋙ etaleDerivedPullback (L.derived f))
    (etaleDerivedPullback (L.derived (f ≫ g)))
    (etaleDerivedPullbackCounit (L.derived (f ≫ g))) (α ≫ e.hom)
    (HomologicalComplex.quasiIso (EtaleModules O Z) (.up ℤ))

private theorem negativeHom_of_iso (C : Type*) [Category* C] [HasShift C ℤ]
    {E E' : C} (e : E ≅ E') (i : ℤ) (h : Subsingleton (E' ⟶ E'⟦i⟧)) :
    Subsingleton (E ⟶ E⟦i⟧) := by
  let := h
  exact (Iso.homCongr e ((shiftFunctor C i).mapIso e)).injective.subsingleton

private theorem negativeHom_of_faithful (C D : Type*) [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.Faithful] [F.CommShift ℤ]
    (E : C) (i : ℤ) (h : Subsingleton (F.obj E ⟶ (F.obj E)⟦i⟧)) :
    Subsingleton (E ⟶ E⟦i⟧) := by
  let := h
  have : Subsingleton (F.obj E ⟶ F.obj (E⟦i⟧)) := by
    refine ⟨fun a b => ?_⟩
    apply (cancel_mono ((F.commShiftIso i).app E).hom).mp
    exact h.elim _ _
  exact F.map_injective.subsingleton

@[instance_reducible]
private def derived_commShift (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    (etaleDerivedPullback (L.derived f)).CommShift ℤ := by
  let := rawPullback_equivalence O L f
  exact Functor.CommShift.ofIso (derivedIso O L f).symm ℤ

private def projectionFieldIso (k : Type u) [CommRing k]
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    {A B : CommAlgCat.{u} k} (f : A ⟶ B) :
    etaleDerivedPullback (L.derived (identityProjection A)) ⋙
        etaleDerivedPullback (L.derived (identityBaseChangeMap f)) ≅
      etaleDerivedPullback (L.derived (Spec.map (CommRingCat.ofHom f.hom.toRingHom))) ⋙
        etaleDerivedPullback (L.derived (identityProjection B)) :=
  (derivedCompIso O L (identityBaseChangeMap f) (identityProjection A)).symm ≪≫
    eqToIso (congrArg (fun g => etaleDerivedPullback (L.derived g))
      (identityBaseChangeMap_projection f)) ≪≫
    derivedCompIsoLeft O L (identityProjection B)
      (Spec.map (CommRingCat.ofHom f.hom.toRingHom))

private theorem reflectsNegativeExt (k : Type u) [CommRing k]
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (A : CommAlgCat.{u} k) (E : EtaleDerived O (Spec (ordinaryRing A)))
    (h : NativeHasNoNegativeFibreExt L A
      ((etaleDerivedPullback (L.derived (identityProjection A))).obj E)) :
    HasNoNegativeFibreExt L (ordinaryRing A) E := by
  intro K _ f i hi
  let := (f.comp (algebraMap k A)).toAlgebra
  let B := CommAlgCat.of k K
  let a : A ⟶ B := CommAlgCat.ofHom
    { toRingHom := f
      commutes' := fun _ => rfl }
  have := derived_equivalence O L (identityProjection B)
  have := derived_commShift O L (identityProjection B)
  apply negativeHom_of_faithful _ _ (etaleDerivedPullback (L.derived (identityProjection B))) _ i
  apply negativeHom_of_iso _ ((projectionFieldIso k O L a).app E).symm i
  exact h B a i hi

private theorem nativeClosed (k : Type u) [CommRing k]
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (A : CommAlgCat.{u} k) (J : AffineEtaleModuleSource O (ordinaryRing A)) :
    (NativeComplexesProperty L A J).IsClosedUnderIsomorphisms where
  of_iso e h := by
    obtain ⟨⟨P, ⟨a⟩⟩, h⟩ := h
    refine ⟨⟨P, ⟨e.symm ≪≫ a⟩⟩, ?_⟩
    intro K _ f i hi
    exact negativeHom_of_iso _
      ((etaleDerivedPullback (L.derived (identityBaseChangeMap f))).mapIso e.symm) i (h K f i hi)

private theorem reflectsProperty (k : Type u) [CommRing k]
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (A : CommAlgCat.{u} k) (J : AffineEtaleModuleSource O (ordinaryRing A))
    (E : EtaleDerived O (Spec (ordinaryRing A)))
    (h : NativeComplexesProperty L A J
      ((etaleDerivedPullback (L.derived (identityProjection A))).obj E)) :
    ComplexesProperty L J E := by
  have := derived_equivalence O L (identityProjection A)
  obtain ⟨⟨P, ⟨a⟩⟩, h⟩ := h
  exact ⟨⟨P, ⟨(etaleDerivedPullback (L.derived (identityProjection A))).preimageIso a⟩⟩,
    reflectsNegativeExt k O L A E h⟩

private def fibreEquivalence (k : Type u) [CommRing k]
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (A : CommAlgCat.{u} k) (J : AffineEtaleModuleSource O (ordinaryRing A))
    (H : IdentityComplexesTransportSource L A J) :
    ComplexesFibre L J ≌ NativeComplexesFibre L A J := by
  have := derived_equivalence O L (identityProjection A)
  have := nativeClosed k O L A J
  let e := (etaleDerivedPullback (L.derived (identityProjection A))).asEquivalence
  refine (e.congrFullSubcategory (P := ComplexesProperty L J)
    (Q := NativeComplexesProperty L A J) ?_).core
  funext E
  apply propext
  exact ⟨reflectsProperty k O L A J E, H.preserves E⟩

/-- The actual projection inverse image identifies the two presentations of the native source
fibre. -/
public theorem classical_identity_source_transport_equivalence (k : Type u) [CommRing k]
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (A : CommAlgCat.{u} k) (J : AffineEtaleModuleSource O (ordinaryRing A))
    (H : IdentityComplexesTransportSource L A J) :
  (identityComplexesTransport H).IsEquivalence
    := by
  exact (fibreEquivalence k O L A J H).isEquivalence_functor
