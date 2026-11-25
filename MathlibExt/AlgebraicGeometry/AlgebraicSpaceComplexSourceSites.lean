/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralStackGeometry
public import MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-!
# Actual algebraic-space small étale sources for complex families

Spaces use the existing literal étale-quotient fppf sheaf presentation.
The small étale objects are actual schemes with representably étale
maps to that sheaf. Their topology is induced from the native scheme
étale topology and their structure ring is the native scheme Γ functor.

Ringed inverse image is normalized by its universal property against
all compatible semilinear maps on actual étale chart squares. Its unit
uses the actual scheme Γ map of each square. This fixes the module
functor rather than supplying an independently named pullback.
Derived inverse image is then the native total left derived functor of
that prescribed module functor. Construction/adaptation proofs remain
separate Wanted requests.

References: Stacks 03G8, 06YY and 0DLE; AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b, small étale ringed sites and
ComplexesStack.lean. The quotient-space carrier and its actual fppf
maps are reused from EtaleSpacePresentations/GeneralStackGeometry.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The source space is the actual quotient sheaf of its native étale equivalence presentation. -/
structure SourceSpace where
  presentation : EtaleEquivalencePresentation.{u}

abbrev SourceSpace.sheaf (X : SourceSpace.{u}) := quotientSheaf X.presentation

instance : Category (SourceSpace.{u}) where
  Hom X Y := X.sheaf ⟶ Y.sheaf
  id _ := 𝟙 _
  comp f g := f ≫ g

/-- The source arrow is its actual morphism of quotient fppf sheaves. -/
def sheafMap {X Y : SourceSpace.{u}} (f : X ⟶ Y) : X.sheaf ⟶ Y.sheaf := f

/-- A represented source fibre square retains its literal scheme projections. -/
structure SchemeFibreSquare {F : FppfSheaf.{u}} {U V : Scheme.{u}}
    (a : represented.obj U ⟶ F) (b : represented.obj V ⟶ F) where
  scheme : Scheme.{u}
  fst : scheme ⟶ U
  snd : scheme ⟶ V
  commutes : represented.map fst ≫ a = represented.map snd ≫ b

/-- The comparison is the actual universal pullback map of these same projections. -/
def SchemeFibreSquare.comparison {F : FppfSheaf.{u}} {U V : Scheme.{u}}
    {a : represented.obj U ⟶ F} {b : represented.obj V ⟶ F}
    (P : SchemeFibreSquare a b) : represented.obj P.scheme ⟶ pullback a b :=
  pullback.lift (represented.map P.fst) (represented.map P.snd) P.commutes

/-- A source representability model fixes the actual fibre sheaf, not a new carrier. -/
structure SchemeFibreModel {F : FppfSheaf.{u}} {U V : Scheme.{u}}
    (a : represented.obj U ⟶ F) (b : represented.obj V ⟶ F)
    extends SchemeFibreSquare a b where
  comparison_iso : IsIso toSchemeFibreSquare.comparison

/-- Representably étale is tested on every actual scheme-valued base change. -/
def IsRepresentablyEtale {X : SourceSpace.{u}} {U : Scheme.{u}}
    (a : represented.obj U ⟶ X.sheaf) : Prop :=
  ∀ (V : Scheme.{u}) (b : represented.obj V ⟶ X.sheaf),
    ∃ P : SchemeFibreModel a b, Etale P.snd

/-- The actual scheme objects of the source small étale site. -/
structure EtaleChart (X : SourceSpace.{u}) where
  scheme : Scheme.{u}
  map : represented.obj scheme ⟶ X.sheaf
  etale : IsRepresentablyEtale map

/-- All chart arrows are actual scheme maps over the same quotient sheaf. -/
structure ChartHom {X : SourceSpace.{u}} (U V : EtaleChart X) where
  schemeMap : U.scheme ⟶ V.scheme
  commutes : represented.map schemeMap ≫ V.map = U.map

instance {X : SourceSpace.{u}} : Category (EtaleChart X) where
  Hom U V := ChartHom U V
  id U := ⟨𝟙 U.scheme, by simp⟩
  comp f g := ⟨f.schemeMap ≫ g.schemeMap, by
    rw [Functor.map_comp, Category.assoc, g.commutes, f.commutes]⟩
  id_comp f := by cases f; simp
  comp_id f := by cases f; simp
  assoc f g h := by
    cases f; cases g; cases h
    congr 1

/-- The source forgetful functor retains the actual scheme and every scheme map. -/
def chartForget (X : SourceSpace.{u}) : EtaleChart X ⥤ Scheme.{u} where
  obj U := U.scheme
  map f := f.schemeMap

/-- The source covering topology is the native étale topology on those actual chart schemes. -/
def smallEtaleTopology (X : SourceSpace.{u}) : GrothendieckTopology (EtaleChart X) :=
  (chartForget X).inducedTopology Scheme.etaleTopology

/-- The actual structure ring presheaf on the space charts. -/
def structurePresheaf (X : SourceSpace.{u}) : (EtaleChart X)ᵒᵖ ⥤ RingCat.{u} :=
  (chartForget X).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat

/-- Native sheafification/abelian-source hypotheses refer only to this prescribed site and Γ presheaf. -/
class SiteSource (X : SourceSpace.{u}) where
  isSheaf : Presheaf.IsSheaf (smallEtaleTopology X) (structurePresheaf X)
  [sheafify : HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
  [locallyBijective : (smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [instance] SiteSource.sheafify SiteSource.locallyBijective

/-- A source theory supplies the already canonical small étale site instances for every actual space. -/
class SourceTheory where
  siteSource : ∀ X : SourceSpace.{u}, SiteSource X

attribute [instance] SourceTheory.siteSource

/-- The source structure sheaf has no independent section-ring input. -/
def structureRing (X : SourceSpace.{u}) [SiteSource X] :
    Sheaf (smallEtaleTopology X) RingCat.{u} :=
  ⟨structurePresheaf X, SiteSource.isSheaf⟩

abbrev Modules (X : SourceSpace.{u}) [SiteSource X] := SheafOfModules.{u} (structureRing X)
abbrev Derived (X : SourceSpace.{u}) [SiteSource X] := DerivedCategory (Modules X)

/-- An actual chart square over a source morphism. -/
structure PullbackChart {X Y : SourceSpace.{u}} (f : X ⟶ Y) where
  source : EtaleChart X
  target : EtaleChart Y
  schemeMap : source.scheme ⟶ target.scheme
  commutes : source.map ≫ f = represented.map schemeMap ≫ target.map

/-- The coefficient-ring map of the actual chart square. -/
def PullbackChart.ringMap {X Y : SourceSpace.{u}} {f : X ⟶ Y} (P : PullbackChart f) :
    (structurePresheaf Y).obj (op P.target) ⟶ (structurePresheaf X).obj (op P.source) :=
  (forget₂ CommRingCat RingCat).map (Scheme.Γ.map P.schemeMap.op)

/-- Refinements retain both source/target chart arrows and the commuting native scheme square. -/
structure PullbackChartHom {X Y : SourceSpace.{u}} {f : X ⟶ Y} (P Q : PullbackChart f) where
  source : P.source ⟶ Q.source
  target : P.target ⟶ Q.target
  commutes : source.schemeMap ≫ Q.schemeMap = P.schemeMap ≫ target.schemeMap

/-- All compatible semilinear maps on all native chart squares, not a freely chosen source-Hom space. -/
structure CompatibleLocalMaps {X Y : SourceSpace.{u}} [SiteSource X] [SiteSource Y]
    (f : X ⟶ Y) (M : Modules Y) (N : Modules X) where
  map : ∀ P : PullbackChart f,
    M.val.obj (op P.target) ⟶
      (ModuleCat.restrictScalars P.ringMap.hom).obj (N.val.obj (op P.source))
  naturality : ∀ (P Q : PullbackChart f) (h : PullbackChartHom P Q),
    M.val.presheaf.map h.target.op ≫
        (forget₂ (ModuleCat ((structurePresheaf Y).obj (op P.target))) AddCommGrpCat).map (map P) =
      (forget₂ (ModuleCat ((structurePresheaf Y).obj (op Q.target))) AddCommGrpCat).map (map Q) ≫
        N.val.presheaf.map h.source.op

/-- The module inverse image represents the fixed chart-square semilinear mapping property. -/
structure ModulePullbackSource {X Y : SourceSpace.{u}} [SiteSource X] [SiteSource Y]
    (f : X ⟶ Y) where
  functor : Modules Y ⥤ Modules X
  [additive : functor.Additive]
  unit : ∀ M : Modules Y, CompatibleLocalMaps f M (functor.obj M)
  homEquiv : ∀ (M : Modules Y) (N : Modules X),
    (functor.obj M ⟶ N) ≃ CompatibleLocalMaps f M N
  hom_formula : ∀ (M : Modules Y) (N : Modules X) (a : functor.obj M ⟶ N) (P : PullbackChart f),
    (homEquiv M N a).map P = (unit M).map P ≫
      (ModuleCat.restrictScalars P.ringMap.hom).map (a.val.app (op P.source))
  unit_naturality : ∀ (M M' : Modules Y) (a : M ⟶ M') (P : PullbackChart f),
    a.val.app (op P.target) ≫ (unit M').map P = (unit M).map P ≫
      (ModuleCat.restrictScalars P.ringMap.hom).map ((functor.map a).val.app (op P.source))

attribute [instance] ModulePullbackSource.additive

/-- The ordinary source operator before its canonical derivation. -/
def pullbackBeforeDeriving {X Y : SourceSpace.{u}} [SiteSource X] [SiteSource Y]
    {f : X ⟶ Y} (P : ModulePullbackSource f) : CochainComplex (Modules Y) ℤ ⥤ Derived X :=
  P.functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

/-- Derivation existence belongs to the exact prescribed source inverse image. -/
structure DerivedPullbackSource {X Y : SourceSpace.{u}} [SiteSource X] [SiteSource Y]
    {f : X ⟶ Y} (P : ModulePullbackSource f) : Prop where
  hasLeftDerived : (pullbackBeforeDeriving P).HasLeftDerivedFunctor
    (HomologicalComplex.quasiIso (Modules Y) (.up ℤ))

/-- Actual native total left derived inverse image. -/
def derivedPullback {X Y : SourceSpace.{u}} [SiteSource X] [SiteSource Y]
    {f : X ⟶ Y} {P : ModulePullbackSource f} (D : DerivedPullbackSource P) : Derived Y ⥤ Derived X :=
  letI := D.hasLeftDerived
  (pullbackBeforeDeriving P).totalLeftDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules Y) (.up ℤ))

/-- Its comparison is the native total-left-derived counit. -/
def derivedPullbackCounit {X Y : SourceSpace.{u}} [SiteSource X] [SiteSource Y]
    {f : X ⟶ Y} {P : ModulePullbackSource f} (D : DerivedPullbackSource P) :
    DerivedCategory.Q ⋙ derivedPullback D ⟶ pullbackBeforeDeriving P :=
  letI := D.hasLeftDerived
  (pullbackBeforeDeriving P).totalLeftDerivedCounit DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules Y) (.up ℤ))

/-- Actual derived inverse-image source data for every algebraic-space arrow. -/
structure PullbackSystem [SourceTheory.{u}] where
  module : ∀ {X Y : SourceSpace.{u}} (f : X ⟶ Y), ModulePullbackSource f
  derived : ∀ {X Y : SourceSpace.{u}} (f : X ⟶ Y), DerivedPullbackSource (module f)

/-- Every system arrow still denotes the same prescribed native total-left-derived operation. -/
def pull [SourceTheory.{u}] (P : PullbackSystem.{u}) {X Y : SourceSpace.{u}} (f : X ⟶ Y) :
    Derived Y ⥤ Derived X :=
  derivedPullback (P.derived f)

/-- Its source-normalized comparison is retained for all coefficient/family pullbacks. -/
def pullCounit [SourceTheory.{u}] (P : PullbackSystem.{u}) {X Y : SourceSpace.{u}} (f : X ⟶ Y) :
    DerivedCategory.Q ⋙ pull P f ⟶ pullbackBeforeDeriving (P.module f) :=
  derivedPullbackCounit (P.derived f)

end MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites
