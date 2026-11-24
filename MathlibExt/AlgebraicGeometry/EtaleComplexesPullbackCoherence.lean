/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-!
# Native unit and composition comparisons for the classical complexes source

The ordinary direct-image comparisons are fixed on every module and
every étale test by the native base-change unit/composition isomorphisms.
Inverse-image comparisons are their actual adjunction mates. Derived
comparisons are then the native uniqueness maps for the prescribed
total left derived functors and their native comparison transformations.
They cannot be replaced by independently chosen identity or composition
isomorphisms of derived module categories.

Existence of the composite derivation and its coherence is a separate
source proof request. References: Stacks 03G8, 06YY and 0D6D; the native
Comparisons/Coherences of ComplexesStack.lean at
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EtaleComplexesPullbackCoherence

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The source base-change unit is fixed by the actual first pullback projection at every test. -/
structure EtaleBaseChangeUnitSource (X : Scheme.{u}) where
  iso : etaleBaseChange (𝟙 X) ≅ 𝟭 X.Etale
  normalized : ∀ U : X.Etale, (iso.hom.app U).left = pullback.fst U.hom (𝟙 X)

/-- The composition comparison is the actual native pullback-pasting isomorphism. -/
def etaleBaseChangeComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleBaseChange (f ≫ g) ≅ etaleBaseChange g ⋙ etaleBaseChange f :=
  MorphismProperty.Over.pullbackComp f g

/-- Literal native module direct image for the fixed ringed-site source map. -/
def etaleModulePushforward {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (D : EtaleRingedMapSource O f) :
    EtaleModules O X ⥤ EtaleModules O Y :=
  letI := D.continuous
  SheafOfModules.pushforward D.ringMap

instance {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (D : EtaleRingedMapSource O f) :
    (etaleModulePushforward D).Additive where
  map_add {M M'} a b := by
    apply SheafOfModules.hom_ext
    ext U x
    rfl

/-- The original native module inverse/direct-image adjunction is retained. -/
def etalePullPushAdjunction {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (D : EtaleRingedMapSource O f) :
    etaleModulePullback D ⊣ etaleModulePushforward D :=
  letI := D.continuous
  letI := D.rightAdjoint
  SheafOfModules.pullbackPushforwardAdjunction D.ringMap

/-- Direct-image source comparisons are fixed on all test-section maps. -/
structure EtalePushforwardCoherence {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (L : EtalePullbackSystem O) where
  baseId : ∀ X : Scheme.{u}, EtaleBaseChangeUnitSource X
  idIso : ∀ X : Scheme.{u}, etaleModulePushforward (L.ringed (𝟙 X)) ≅ 𝟭 (EtaleModules O X)
  id_eq : ∀ (X : Scheme.{u}) (M : EtaleModules O X) (U : X.Etale),
    ((SheafOfModules.toSheaf (etaleStructureRing O X)).map ((idIso X).hom.app M)).hom.app
      (op U) = M.val.presheaf.map ((((baseId X).iso).inv.app U).op)
  compIso : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    etaleModulePushforward (L.ringed (f ≫ g)) ≅
      etaleModulePushforward (L.ringed f) ⋙ etaleModulePushforward (L.ringed g)
  comp_eq : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : EtaleModules O X) (U : Z.Etale),
    ((SheafOfModules.toSheaf (etaleStructureRing O Z)).map
      ((compIso f g).hom.app M)).hom.app (op U) =
        M.val.presheaf.map (((etaleBaseChangeComp f g).inv.app U).op)

/-- Native inverse-image unit, as the actual adjunction mate of the fixed source unit. -/
def etaleRawPullbackId {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} (C : EtalePushforwardCoherence L) (X : Scheme.{u}) :
    etaleModulePullback (L.ringed (𝟙 X)) ≅ 𝟭 (EtaleModules O X) :=
  (etalePullPushAdjunction (L.ringed (𝟙 X))).leftAdjointIdIso (C.idIso X)

/-- Native inverse-image composition, as the mate of the fixed direct-image comparison. -/
def etaleRawPullbackComp {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} (C : EtalePushforwardCoherence L)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleModulePullback (L.ringed g) ⋙ etaleModulePullback (L.ringed f) ≅
      etaleModulePullback (L.ringed (f ≫ g)) :=
  Adjunction.leftAdjointCompIso
    (etalePullPushAdjunction (L.ringed g)) (etalePullPushAdjunction (L.ringed f))
    (etalePullPushAdjunction (L.ringed (f ≫ g))) (C.compIso f g).symm

/-- The same native mate acts on every cochain term and differential. -/
def etaleRawComplexId {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} (C : EtalePushforwardCoherence L) (X : Scheme.{u}) :
    (etaleModulePullback (L.ringed (𝟙 X))).mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex (EtaleModules O X) ℤ) :=
  NatIso.mapHomologicalComplex (etaleRawPullbackId C X) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)

/-- The same native composition mate acts on all cochain degrees. -/
def etaleRawComplexComp {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} (C : EtalePushforwardCoherence L)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (etaleModulePullback (L.ringed g)).mapHomologicalComplex (.up ℤ) ⋙
      (etaleModulePullback (L.ringed f)).mapHomologicalComplex (.up ℤ) ≅
        (etaleModulePullback (L.ringed (f ≫ g))).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (etaleRawPullbackComp C f g) (.up ℤ)

/-- The ordinary unit comparison before deriving is prescribed by the native mate. -/
def etaleBeforeDerivedId {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} (C : EtalePushforwardCoherence L) (X : Scheme.{u}) :
    DerivedCategory.Q ⋙ 𝟭 (EtaleDerived O X) ≅ etalePullbackBeforeDeriving (L.ringed (𝟙 X)) :=
  Functor.rightUnitor DerivedCategory.Q ≪≫
    (Functor.leftUnitor DerivedCategory.Q).symm ≪≫
      Functor.isoWhiskerRight (etaleRawComplexId C X).symm DerivedCategory.Q

/-- The derived unit is the native uniqueness comparison for that prescribed transformation. -/
def etaleDerivedId {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} (C : EtalePushforwardCoherence L) (X : Scheme.{u}) :
    etaleDerivedPullback (L.derived (𝟙 X)) ≅ 𝟭 (EtaleDerived O X) := by
  letI := (L.derived (𝟙 X)).hasLeftDerived
  letI := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (EtaleModules O X) (.up ℤ))
    (𝟭 (EtaleDerived O X)) (etaleBeforeDerivedId C X)
  exact Functor.leftDerivedUnique (𝟭 (EtaleDerived O X))
    (etaleDerivedPullback (L.derived (𝟙 X)))
    (etaleDerivedPullbackCounit (L.derived (𝟙 X))) (etaleBeforeDerivedId C X).hom
    (HomologicalComplex.quasiIso (EtaleModules O X) (.up ℤ))

/-- The composite comparison is literal derivation-counit composition followed by the native mate. -/
def etaleCompositeDerivedComparison {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} (C : EtalePushforwardCoherence L)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    DerivedCategory.Q ⋙
      (etaleDerivedPullback (L.derived g) ⋙ etaleDerivedPullback (L.derived f)) ⟶
        etalePullbackBeforeDeriving (L.ringed (f ≫ g)) :=
  (Functor.associator DerivedCategory.Q (etaleDerivedPullback (L.derived g))
    (etaleDerivedPullback (L.derived f))).inv ≫
  Functor.whiskerRight (etaleDerivedPullbackCounit (L.derived g))
    (etaleDerivedPullback (L.derived f)) ≫
  (Functor.associator ((etaleModulePullback (L.ringed g)).mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q (etaleDerivedPullback (L.derived f))).hom ≫
  Functor.whiskerLeft ((etaleModulePullback (L.ringed g)).mapHomologicalComplex (.up ℤ))
    (etaleDerivedPullbackCounit (L.derived f)) ≫
  (Functor.associator ((etaleModulePullback (L.ringed g)).mapHomologicalComplex (.up ℤ))
    ((etaleModulePullback (L.ringed f)).mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q).inv ≫
  Functor.whiskerRight (etaleRawComplexComp C f g).hom DerivedCategory.Q

/-- Composition of these particular inverse images is a left derived functor of the fixed source. -/
structure EtaleCompositeDerivationSource {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} (C : EtalePushforwardCoherence L)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : Prop where
  isLeftDerived :
    (etaleDerivedPullback (L.derived g) ⋙ etaleDerivedPullback (L.derived f)).IsLeftDerivedFunctor
      (etaleCompositeDerivedComparison C f g)
      (HomologicalComplex.quasiIso (EtaleModules O Z) (.up ℤ))

/-- The derived composition is the native uniqueness map, with no independent iso input. -/
def etaleDerivedComp {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} {C : EtalePushforwardCoherence L}
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (H : EtaleCompositeDerivationSource C f g) :
    etaleDerivedPullback (L.derived (f ≫ g)) ≅
      etaleDerivedPullback (L.derived g) ⋙ etaleDerivedPullback (L.derived f) := by
  letI := (L.derived (f ≫ g)).hasLeftDerived
  letI := H.isLeftDerived
  exact Functor.leftDerivedUnique
    (etaleDerivedPullback (L.derived g) ⋙ etaleDerivedPullback (L.derived f))
    (etaleDerivedPullback (L.derived (f ≫ g)))
    (etaleDerivedPullbackCounit (L.derived (f ≫ g)))
    (etaleCompositeDerivedComparison C f g)
    (HomologicalComplex.quasiIso (EtaleModules O Z) (.up ℤ))

end MathlibExt.AlgebraicGeometry.EtaleComplexesPullbackCoherence
