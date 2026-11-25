/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedClassicalComplexComparisonModels
public import MathlibExt.AlgebraicGeometry.EtaleComplexesPullbackCoherence

/-!
# Coefficient and small étale pullback maps of the actual complexes comparison

The coefficient scalar map is normalized on 1 tensor x in every degree
to the unit of the same StrictPerfectSystem realization. B-linearity
then fixes its value on every b tensor x. Tilde inverse image is fixed
by the native scheme pullback adjunction unit and that same tensor unit.

The small étale pullback map is normalized after adjunction at every
étale test and every degree to the native scheme pullback-pasting map
of that tilde arrow. The derived comparison is literally the native
total-left-derived counit followed by Q of this prescribed cochain map.
An isomorphism assertion about that map is a separate proof request.

References: Toën--Vaquié math/0503269v5 §3.1 pp36--37;
Stacks 06YY, 0D6D, 0DLD/0DLE. General T-actions are retained by the
existing vertexBimodule; the ordinary plain-complex comparison uses
only the actual scalar-category specialization.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ClassicalComplexCoefficientMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
  _root_.Opposite _root_.AlgebraicGeometry
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
open MathlibExt.AlgebraicGeometry.DerivedClassicalComplexComparisonModels
open MathlibExt.AlgebraicGeometry.EtaleComplexesPullbackCoherence
open scoped AlgebraicGeometry Simplicial

universe u

variable {k : Type u} [CommRing k]

attribute [local instance] HasDerivedCategory.standard

/-- The coefficient unit evaluated at the actual unique coefficient object. -/
def restrictedCoefficientValueIso {N : ShuffleAlgebraFunctor k} (S : AffineScalarSystem N)
    {A B : CommAlgCat.{u} k} (f : A ⟶ B)
    (M : RightModule k (coefficientCategory N (ordinaryAlgebras.obj B))) :
    ((S.restriction (ordinaryAlgebras.obj A) (ordinaryAlgebras.obj B)
      (ordinaryAlgebras.map f)).functor.obj M).toEnrichedFunctor.obj (op PUnit.unit) ≅
        M.toEnrichedFunctor.obj (op PUnit.unit) :=
  eqToIso (by
    rw [(S.restriction (ordinaryAlgebras.obj A) (ordinaryAlgebras.obj B)
      (ordinaryAlgebras.map f)).object_eq]
    rfl)

/-- The actual scalar-change cochain map is fixed by the native module adjunction unit. -/
structure OrdinaryCoefficientMap {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    (r : ScalarFramePoint R) (P : StrictPerfectSystem N S)
    {A B : CommAlgCat.{u} k} (f : A ⟶ B)
    {C : OrdinaryCoefficientSource N A} {C' : OrdinaryCoefficientSource N B}
    (V : OrdinaryModuleSource C) (V' : OrdinaryModuleSource C')
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌) where
  map : ((ModuleCat.extendScalars f.hom.toRingHom).mapHomologicalComplex (.up ℤ)).obj
      (vertexOrdinaryComplex r P A V E) ⟶
    vertexOrdinaryComplex r P B V'
      (((underivedModuliFunctor R P).map f).app (op ⦋0⦌) E)
  unit_eq : ∀ (n : ℤ) (x : (vertexOrdinaryComplex r P A V E).X n),
    (((V'.underlyingIso.hom.app
      (vertexModule r P B (((underivedModuliFunctor R P).map f).app (op ⦋0⦌) E))).f n).hom
        ((map.f n).hom ((ModuleCat.ExtendRestrictScalarsAdj.Unit.map f.hom.toRingHom).hom x))) =
      ((restrictedCoefficientValueIso S f
        (vertexModule r P B (((underivedModuliFunctor R P).map f).app (op ⦋0⦌) E))).hom.f n).hom
          (cochainEval k
            (((V.underlyingIso.hom.app (vertexModule r P A E)).f n).hom x) 0 n (by omega)
            (DGFunctor.dgApp k
              (C := (coefficientCategory N (ordinaryAlgebras.obj A))ᵒᵖ)
              0 (op PUnit.unit)
              (P.unit (ordinaryAlgebras.obj A) (ordinaryAlgebras.obj B)
                (ordinaryAlgebras.map f) (E.obj r.point))))

/-- The actual global-section map of a native scheme pullback adjunction unit. -/
def globalPullbackUnit {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    Γ(M, ⊤) ⟶ Γ((Scheme.Modules.pullback f).obj M, ⊤) := by
  let N := (Scheme.Modules.pullback f).obj M
  let unit := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M
  let topIso : Γ((Scheme.Modules.pushforward f).obj N, ⊤) ≅ Γ(N, ⊤) :=
    eqToIso (congrArg (fun W : X.Opens => N.presheaf.obj (op W)) (by simp))
  exact unit.app ⊤ ≫ topIso.hom

/-- The affine tilde comparison is fixed by the actual adjunction unit 1 tensor x. -/
structure TildeAffinePullbackSource {A B : CommRingCat.{u}} (f : A ⟶ B) where
  iso : tilde.functor A ⋙ Scheme.Modules.pullback (Spec.map f) ≅
    ModuleCat.extendScalars f.hom ⋙ tilde.functor B
  unit_eq : ∀ (M : ModuleCat.{u} A) (x : M),
    (tilde.isoTop ((ModuleCat.extendScalars f.hom).obj M)).inv.hom
      (((iso.hom.app M).app ⊤)
        ((globalPullbackUnit (Spec.map f) ((tilde.functor A).obj M))
          ((tilde.isoTop M).hom.hom x))) = (ModuleCat.ExtendRestrictScalarsAdj.Unit.map f.hom).hom x

/-- The ordinary scalar map gives its literal tilde pullback map in every cochain degree. -/
def tildeCoefficientMap {A B : CommRingCat.{u}} {f : A ⟶ B}
    (T : TildeAffinePullbackSource f)
    {K : CochainComplex (ModuleCat.{u} A) ℤ} {K' : CochainComplex (ModuleCat.{u} B) ℤ}
    (a : ((ModuleCat.extendScalars f.hom).mapHomologicalComplex (.up ℤ)).obj K ⟶ K') :
    ((Scheme.Modules.pullback (Spec.map f)).mapHomologicalComplex (.up ℤ)).obj
      (((tilde.functor A).mapHomologicalComplex (.up ℤ)).obj K) ⟶
        ((tilde.functor B).mapHomologicalComplex (.up ℤ)).obj K' :=
  ((Functor.mapHomologicalComplexCompIso (Iso.refl
    (tilde.functor A ⋙ Scheme.Modules.pullback (Spec.map f))) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex T.iso (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.extendScalars f.hom ⋙ tilde.functor B)) (.up ℤ)).symm).hom.app K) ≫
    ((tilde.functor B).mapHomologicalComplex (.up ℤ)).map a

/-- At each actual étale test, use the native pullback unit and the actual pullback-pasting square. -/
def tildeCoefficientMapAtTest {A B : CommRingCat.{u}} {f : A ⟶ B}
    {K : CochainComplex (ModuleCat.{u} A) ℤ} {K' : CochainComplex (ModuleCat.{u} B) ℤ}
    (a : ((Scheme.Modules.pullback (Spec.map f)).mapHomologicalComplex (.up ℤ)).obj
      (((tilde.functor A).mapHomologicalComplex (.up ℤ)).obj K) ⟶
        ((tilde.functor B).mapHomologicalComplex (.up ℤ)).obj K')
    (n : ℤ) (U : (Spec A).Etale) :
    Γ((Scheme.Modules.pullback U.hom).obj ((tilde.functor A).obj (K.X n)), ⊤) ⟶
      Γ((Scheme.Modules.pullback ((etaleBaseChange (Spec.map f)).obj U).hom).obj
        ((tilde.functor B).obj (K'.X n)), ⊤) := by
  let b := pullback.fst U.hom (Spec.map f)
  let c := pullback.snd U.hom (Spec.map f)
  let N := (Scheme.Modules.pullback U.hom).obj ((tilde.functor A).obj (K.X n))
  let comparison := Scheme.Modules.pullbackComp b U.hom ≪≫
    Scheme.Modules.pullbackCongr (pullback.condition (f := U.hom) (g := Spec.map f)) ≪≫
      (Scheme.Modules.pullbackComp c (Spec.map f)).symm
  exact globalPullbackUnit b N ≫
    (comparison.hom.app ((tilde.functor A).obj (K.X n))).app ⊤ ≫
      ((Scheme.Modules.pullback c).map (a.f n)).app ⊤

/-- The actual cochain adjunction mate of a small étale inverse-image map. -/
def etaleCoefficientMate {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} {A B : CommRingCat.{u}} (f : A ⟶ B)
    {K : CochainComplex (EtaleModules O (Spec A)) ℤ}
    {K' : CochainComplex (EtaleModules O (Spec B)) ℤ}
    (a : ((etaleModulePullback (L.ringed (Spec.map f))).mapHomologicalComplex (.up ℤ)).obj K ⟶ K') :
    K ⟶ ((etaleModulePushforward (L.ringed (Spec.map f))).mapHomologicalComplex (.up ℤ)).obj K' :=
  (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app K ≫
  (NatTrans.mapHomologicalComplex (etalePullPushAdjunction (L.ringed (Spec.map f))).unit
    (.up ℤ)).app K ≫
  (Functor.mapHomologicalComplexCompIso (Iso.refl
    (etaleModulePullback (L.ringed (Spec.map f)) ⋙
      etaleModulePushforward (L.ringed (Spec.map f)))) (.up ℤ)).inv.app K ≫
    ((etaleModulePushforward (L.ringed (Spec.map f))).mapHomologicalComplex (.up ℤ)).map a

/-- The small étale source map is fixed on every test and every coefficient degree. -/
structure EtaleCoefficientMapSource {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (L : EtalePullbackSystem O) {A B : CommRingCat.{u}} (f : A ⟶ B)
    (J : AffineEtaleModuleSource O A) (J' : AffineEtaleModuleSource O B)
    {K : CochainComplex (ModuleCat.{u} A) ℤ} {K' : CochainComplex (ModuleCat.{u} B) ℤ}
    (a : ((Scheme.Modules.pullback (Spec.map f)).mapHomologicalComplex (.up ℤ)).obj
      (((tilde.functor A).mapHomologicalComplex (.up ℤ)).obj K) ⟶
        ((tilde.functor B).mapHomologicalComplex (.up ℤ)).obj K') where
  map : ((etaleModulePullback (L.ringed (Spec.map f))).mapHomologicalComplex (.up ℤ)).obj
      (associatedEtaleComplex J K) ⟶ associatedEtaleComplex J' K'
  normalized : ∀ (n : ℤ) (U : (Spec A).Etale)
    (s : ((associatedEtaleComplex J K).X n).val.obj (op U)),
    (((J'.testIso ((etaleBaseChange (Spec.map f)).obj U)).hom.app (K'.X n)).hom
      ((((etaleCoefficientMate (L := L) f map).f n).val.app (op U)).hom s)) =
        (tildeCoefficientMapAtTest a n U)
          (((J.testIso U).hom.app (K.X n)).hom s)

/-- The derived source arrow is literally the native counit followed by Q of the normalized map. -/
def derivedEtaleCoefficientMap {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} {A B : CommRingCat.{u}} {f : A ⟶ B}
    {J : AffineEtaleModuleSource O A} {J' : AffineEtaleModuleSource O B}
    {K : CochainComplex (ModuleCat.{u} A) ℤ} {K' : CochainComplex (ModuleCat.{u} B) ℤ}
    {a : ((Scheme.Modules.pullback (Spec.map f)).mapHomologicalComplex (.up ℤ)).obj
      (((tilde.functor A).mapHomologicalComplex (.up ℤ)).obj K) ⟶
        ((tilde.functor B).mapHomologicalComplex (.up ℤ)).obj K'}
    (D : EtaleCoefficientMapSource L f J J' a) :
    (etaleDerivedPullback (L.derived (Spec.map f))).obj (associatedEtaleDerived J K) ⟶
      associatedEtaleDerived J' K' :=
  (etaleDerivedPullbackCounit (L.derived (Spec.map f))).app (associatedEtaleComplex J K) ≫
    DerivedCategory.Q.map D.map

/-- Preservation concerns the actual native derived inverse image and actual source condition. -/
structure ClassicalPullbackSource {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (L : EtalePullbackSystem O) {A B : CommRingCat.{u}} (f : A ⟶ B)
    (J : AffineEtaleModuleSource O A) (J' : AffineEtaleModuleSource O B) : Prop where
  preserves : ∀ E : EtaleDerived O (Spec A), ComplexesProperty L J E →
    ComplexesProperty L J' ((etaleDerivedPullback (L.derived (Spec.map f))).obj E)

/-- The classical pullback acts on the same source-derived objects and their actual arrows. -/
def classicalPullbackUnderlying {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} {A B : CommRingCat.{u}} {f : A ⟶ B}
    {J : AffineEtaleModuleSource O A} {J' : AffineEtaleModuleSource O B}
    (H : ClassicalPullbackSource L f J J') :
    (ComplexesProperty L J).FullSubcategory ⥤ (ComplexesProperty L J').FullSubcategory where
  obj E := ⟨(etaleDerivedPullback (L.derived (Spec.map f))).obj E.obj,
    H.preserves E.obj E.property⟩
  map a := ObjectProperty.homMk ((etaleDerivedPullback (L.derived (Spec.map f))).map a.hom)
  map_id E := by
    apply ObjectProperty.hom_ext
    exact (etaleDerivedPullback (L.derived (Spec.map f))).map_id E.obj
  map_comp a b := by
    apply ObjectProperty.hom_ext
    exact (etaleDerivedPullback (L.derived (Spec.map f))).map_comp a.hom b.hom

/-- On the groupoid fibre, the native derived pullback is applied to the actual isomorphisms. -/
def classicalPullback {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} {A B : CommRingCat.{u}} {f : A ⟶ B}
    {J : AffineEtaleModuleSource O A} {J' : AffineEtaleModuleSource O B}
    (H : ClassicalPullbackSource L f J J') : ComplexesFibre L J ⥤ ComplexesFibre L J' :=
  (classicalPullbackUnderlying H).core

/-- A family of coefficient maps retains the same native unit and test normalization for every algebra. -/
structure CoefficientMapSystem {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    {r : ScalarFramePoint R} {P : StrictPerfectSystem N S}
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X} {L : EtalePullbackSystem O}
    (Z : OrdinaryComplexSourceSystem r P O L) where
  tilde : ∀ {A B : CommAlgCat.{u} k} (f : A ⟶ B),
    TildeAffinePullbackSource (CommRingCat.ofHom f.hom.toRingHom)
  ordinary : ∀ {A B : CommAlgCat.{u} k} (f : A ⟶ B)
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌),
    OrdinaryCoefficientMap r P f (Z.module A) (Z.module B) E
  etale : ∀ {A B : CommAlgCat.{u} k} (f : A ⟶ B)
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌),
    EtaleCoefficientMapSource L (CommRingCat.ofHom f.hom.toRingHom) (Z.etale A) (Z.etale B)
      (tildeCoefficientMap (tilde f) (ordinary f E).map)

/-- The map of a coefficient family is still the literal native derived-comparison composite. -/
def coefficientFamilyMap {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    {r : ScalarFramePoint R} {P : StrictPerfectSystem N S}
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X} {L : EtalePullbackSystem O}
    {Z : OrdinaryComplexSourceSystem r P O L} (D : CoefficientMapSystem Z)
    {A B : CommAlgCat.{u} k} (f : A ⟶ B)
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌) :=
  derivedEtaleCoefficientMap (D.etale f E)

/-- The coefficient naturality output fixes every component to the literal derived source map. -/
structure ClassicalCoefficientNaturality {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    {r : ScalarFramePoint R} {I : ScalarFrameInterval r} {P : StrictPerfectSystem N S}
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X} {L : EtalePullbackSystem O}
    (Z : OrdinaryComplexSourceSystem r P O L) {A B : CommAlgCat.{u} k} (f : A ⟶ B)
    {F : ScalarFrameEdgeMaps I P A} {F' : ScalarFrameEdgeMaps I P B}
    (G : ClassicalComplexComparison F (Z.module A) L (Z.etale A))
    (G' : ClassicalComplexComparison F' (Z.module B) L (Z.etale B))
    (H : ClassicalPullbackSource L (CommRingCat.ofHom f.hom.toRingHom) (Z.etale A) (Z.etale B))
    (T : TildeAffinePullbackSource (CommRingCat.ofHom f.hom.toRingHom))
    (a : ∀ E : ((underivedModuliFunctor R P).obj A) _⦋0⦌,
      OrdinaryCoefficientMap r P f (Z.module A) (Z.module B) E)
    (D : ∀ E : ((underivedModuliFunctor R P).obj A) _⦋0⦌,
      EtaleCoefficientMapSource L (CommRingCat.ofHom f.hom.toRingHom) (Z.etale A) (Z.etale B)
        (tildeCoefficientMap T (a E).map)) where
  iso : G.functor ⋙ classicalPullback H ≅ glueableScalarGroupoidMap Z f ⋙ G'.functor
  component_eq : ∀ E : (universallyGlueableSpace r P A (Z.module A) L (Z.etale A)) _⦋0⦌,
    HEq ((iso.hom.app (SSet.FundamentalGroupoid.mk E)).iso.hom.hom)
      (derivedEtaleCoefficientMap (D E.val))

end MathlibExt.AlgebraicGeometry.ClassicalComplexCoefficientMaps
