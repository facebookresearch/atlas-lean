/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies
public import MathlibExt.AlgebraicGeometry.ProperComplexFamilySources

/-!
# Actual affine presentations of relatively perfect space complexes

Restriction to an étale scheme chart is the native module pushforward
along its actual small-site inclusion. The source inclusion is fixed
on every scheme, scheme map and structure-ring component. Its exact
derived functor is therefore a construction on actual source modules.

Relative perfection is local on these actual source charts. The
presentation and canonical versions respectively use a bounded flat
finitely presented B-complex and the actual finite-projective B-source
resolution/native A-Tor criterion. Both retain the fixed native
restriction of the same X_T complex, the actual coefficient ring map,
and the native tilde source on Spec B.

References: Stacks 0DKN, 0DKR, 0DLD and 0DLE; the source relative
subcategory at AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations
open MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.ProperComplexFamilySources
open MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The chart-site inclusion and Γ map are fixed on every actual scheme test. -/
structure ChartRestrictionSource (O : ∀ S : Scheme.{u}, EtaleStructureSource S)
    {X : SourceSpace.{u}} [SiteSource X] (U : EtaleChart X) where
  reindex : U.scheme.Etale ⥤ EtaleChart X
  scheme_eq : ∀ Z : U.scheme.Etale, (reindex.obj Z).scheme = Z.left
  object_map : ∀ Z : U.scheme.Etale,
    HEq (reindex.obj Z).map (represented.map Z.hom ≫ U.map)
  map_eq : ∀ (Z Z' : U.scheme.Etale) (h : Z ⟶ Z'), HEq (reindex.map h).schemeMap h.left
  [continuous : reindex.IsContinuous U.scheme.smallEtaleTopology (smallEtaleTopology X)]
  ringMap : etaleStructureRing O U.scheme ⟶
    (reindex.sheafPushforwardContinuous RingCat.{u} U.scheme.smallEtaleTopology
      (smallEtaleTopology X)).obj (structureRing X)
  ringMap_eq : ∀ Z : U.scheme.Etale, ringMap.hom.app (op Z) =
    (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (eqToHom (scheme_eq Z)).op)
  [finiteLimits : PreservesFiniteLimits (SheafOfModules.pushforward.{u} ringMap)]
  [finiteColimits : PreservesFiniteColimits (SheafOfModules.pushforward.{u} ringMap)]

/-- Literal native restriction functor, with the prescribed chart ring-map unit. -/
def chartModuleRestriction {O : ∀ S : Scheme.{u}, EtaleStructureSource S}
    {X : SourceSpace.{u}} [SiteSource X] {U : EtaleChart X}
    (R : ChartRestrictionSource O U) : Modules X ⥤ EtaleModules O U.scheme :=
  letI := R.continuous
  SheafOfModules.pushforward.{u} R.ringMap

instance {O : ∀ S : Scheme.{u}, EtaleStructureSource S}
    {X : SourceSpace.{u}} [SiteSource X] {U : EtaleChart X}
    (R : ChartRestrictionSource O U) : (chartModuleRestriction R).Additive where
  map_add {M M'} a b := by
    apply SheafOfModules.hom_ext
    ext Z x
    rfl

instance {O : ∀ S : Scheme.{u}, EtaleStructureSource S}
    {X : SourceSpace.{u}} [SiteSource X] {U : EtaleChart X}
    (R : ChartRestrictionSource O U) : PreservesFiniteLimits (chartModuleRestriction R) :=
  R.finiteLimits

instance {O : ∀ S : Scheme.{u}, EtaleStructureSource S}
    {X : SourceSpace.{u}} [SiteSource X] {U : EtaleChart X}
    (R : ChartRestrictionSource O U) : PreservesFiniteColimits (chartModuleRestriction R) :=
  R.finiteColimits

/-- The actual exact derived restriction on the native source complexes. -/
def chartDerivedRestriction {O : ∀ S : Scheme.{u}, EtaleStructureSource S}
    {X : SourceSpace.{u}} [SiteSource X] {U : EtaleChart X}
    (R : ChartRestrictionSource O U) : Derived X ⥤ EtaleDerived O U.scheme :=
  (chartModuleRestriction R).mapDerivedCategory

/-- A source system keeps the prescribed inclusion for every actual étale chart. -/
structure ChartRestrictionSystem (O : ∀ S : Scheme.{u}, EtaleStructureSource S) [SourceTheory.{u}] where
  chart : ∀ (X : SourceSpace.{u}) (U : EtaleChart X), ChartRestrictionSource O U

/-- An affine chart fixes both actual open base and actual scheme-to-space source map. -/
structure RelativeAffineChart {D : ProperSpaceSituation.{u}} (T : FamilyTest D) where
  chart : EtaleChart (familySpace D T)
  A : CommRingCat.{u}
  B : CommRingCat.{u}
  scheme_eq : chart.scheme = Spec B
  coefficient : A ⟶ B
  coefficient_flat : RingHom.Flat coefficient.hom
  baseOpen : Spec A ⟶ T.scheme
  base_openImmersion : IsOpenImmersion baseOpen
  square : chartStructuralMap (familyProjection D T) chart =
    eqToHom scheme_eq ≫ Spec.map coefficient ≫ baseOpen

/-- The affine coefficient restriction is the actual chart functor and the native Spec identification pullback. -/
def affineRestriction {O : ∀ S : Scheme.{u}, EtaleStructureSource S} [SourceTheory.{u}]
    (L : EtalePullbackSystem O) (R : ChartRestrictionSystem O)
    {D : ProperSpaceSituation.{u}} {T : FamilyTest D} (C : RelativeAffineChart T) :
    Derived (familySpace D T) ⥤ EtaleDerived O (Spec C.B) :=
  chartDerivedRestriction (R.chart _ C.chart) ⋙
    etaleDerivedPullback (L.derived (eqToHom C.scheme_eq.symm))

/-- The actual local bounded-flat presentation criterion, including the coefficient action and native complex comparison. -/
def IsRelativelyPerfect {O : ∀ S : Scheme.{u}, EtaleStructureSource S} [SourceTheory.{u}]
    (L : EtalePullbackSystem O) (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
    (R : ChartRestrictionSystem O) (D : ProperSpaceSituation.{u}) (T : FamilyTest D)
    (E : Derived (familySpace D T)) : Prop :=
  ∀ (U : EtaleChart (familySpace D T)) (x : U.scheme),
    ∃ C : RelativeAffineChart T, ∃ h : C.chart ⟶ U,
      x ∈ Set.range h.schemeMap ∧
      ∃ P : RelativePerfectComplex C.coefficient,
        Nonempty ((affineRestriction L R C).obj E ≅ associatedEtaleDerived (J C.B) P.complex)

/-- The canonical pseudo-coherent/relative-Tor version is tied to the same source complex and charts. -/
def IsCanonicalRelativelyPerfect {O : ∀ S : Scheme.{u}, EtaleStructureSource S} [SourceTheory.{u}]
    (L : EtalePullbackSystem O) (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
    (R : ChartRestrictionSystem O) (D : ProperSpaceSituation.{u}) (T : FamilyTest D)
    (E : Derived (familySpace D T)) : Prop :=
  ∀ (U : EtaleChart (familySpace D T)) (x : U.scheme),
    ∃ C : RelativeAffineChart T, ∃ h : C.chart ⟶ U,
      x ∈ Set.range h.schemeMap ∧
      ∃ K : CochainComplex (ModuleCat.{u} C.B) ℤ,
        IsCanonicalRelativePerfect C.coefficient C.coefficient_flat K ∧
          Nonempty ((affineRestriction L R C).obj E ≅ associatedEtaleDerived (J C.B) K)

/-- General native source objects have actual relative perfection and literal negative field self-Ext. -/
def ComplexesProperty {O : ∀ S : Scheme.{u}, EtaleStructureSource S} [SourceTheory.{u}]
    (P : PullbackSystem.{u}) (L : EtalePullbackSystem O)
    (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A) (R : ChartRestrictionSystem O)
    (D : ProperSpaceSituation.{u}) (T : FamilyTest D) : ObjectProperty (Derived (familySpace D T)) :=
  fun E => IsRelativelyPerfect L J R D T E ∧ ProperSpaceComplexFamilies.HasNoNegativeFibreExt P D T E

/-- The actual source-native algebraic-space complexes fibre. -/
abbrev ComplexesFibre {O : ∀ S : Scheme.{u}, EtaleStructureSource S} [SourceTheory.{u}]
    (P : PullbackSystem.{u}) (L : EtalePullbackSystem O)
    (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A) (R : ChartRestrictionSystem O)
    (D : ProperSpaceSituation.{u}) (T : FamilyTest D) :=
  Core ((ComplexesProperty P L J R D T).FullSubcategory)

/-- Preservation is a source theorem about the actual native X_h inverse image and both source conditions. -/
structure ComplexesPullbackSource {O : ∀ S : Scheme.{u}, EtaleStructureSource S} [SourceTheory.{u}]
    (P : PullbackSystem.{u}) (L : EtalePullbackSystem O)
    (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A) (R : ChartRestrictionSystem O)
    {D : ProperSpaceSituation.{u}} {T T' : FamilyTest D} (h : T ⟶ T') : Prop where
  preserves : ∀ E : Derived (familySpace D T'), ComplexesProperty P L J R D T' E →
    ComplexesProperty P L J R D T ((pull P (familyMap h)).obj E)

/-- The actual native derived inverse image is applied to objects and arrows of the general source fibre. -/
def complexesPullbackUnderlying {O : ∀ S : Scheme.{u}, EtaleStructureSource S} [SourceTheory.{u}]
    {P : PullbackSystem.{u}} {L : EtalePullbackSystem O}
    {J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A} {R : ChartRestrictionSystem O}
    {D : ProperSpaceSituation.{u}} {T T' : FamilyTest D} {h : T ⟶ T'}
    (H : ComplexesPullbackSource P L J R h) :
    (ComplexesProperty P L J R D T').FullSubcategory ⥤ (ComplexesProperty P L J R D T).FullSubcategory where
  obj E := ⟨(pull P (familyMap h)).obj E.obj, H.preserves E.obj E.property⟩
  map a := ObjectProperty.homMk ((pull P (familyMap h)).map a.hom)
  map_id E := by
    apply ObjectProperty.hom_ext
    exact (pull P (familyMap h)).map_id E.obj
  map_comp a b := by
    apply ObjectProperty.hom_ext
    exact (pull P (familyMap h)).map_comp a.hom b.hom

/-- Source groupoid pullback retains the actual native derived isomorphisms. -/
def complexesPullback {O : ∀ S : Scheme.{u}, EtaleStructureSource S} [SourceTheory.{u}]
    {P : PullbackSystem.{u}} {L : EtalePullbackSystem O}
    {J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A} {R : ChartRestrictionSystem O}
    {D : ProperSpaceSituation.{u}} {T T' : FamilyTest D} {h : T ⟶ T'}
    (H : ComplexesPullbackSource P L J R h) : ComplexesFibre P L J R D T' ⥤ ComplexesFibre P L J R D T :=
  (complexesPullbackUnderlying H).core

end MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations
