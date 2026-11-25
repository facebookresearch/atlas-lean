/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.KatoChartCoefficientModels
public import MathlibExt.AlgebraicGeometry.GeometricLogGhosts
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Sites.Precoverage

/-!
# Independent native Kummer-flat log geometry

Log-flatness is the actual fppf-local Kato chart comparison to
X times Spec Z[P] Spec Z[Q]. It does not require the original underlying
scheme map to be flat. Chart compatibility fixes every original log
generator, including generators with zero alpha. Kummerness is tested
on the actual geometric characteristic stalk maps. The underlying map
is locally of finite presentation as in the source definition.

Source: Talpo--Vistoli arXiv:1410.1164v2, Definition6.10 and
Remarks6.11--6.12. Fine/saturated log fibre products are kept in the
native log category; no identification with scheme fibre products is made.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeKummerFlatModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams LogStructures SmallEtaleGeometry
open EtaleLogNativeCategory KatoChartCoefficientModels GeometricLogGhosts

variable [InverseImageTheory.{0}]

/-- Native identity-etale lift into the actual base-changed chart. -/
def identityDiagonal {X Y : Scheme.{0}} (f : X ⟶ Y) :
    KatoChartCoefficientModels.identityEtale X ⟶
      (etaleBaseChange f).obj (KatoChartCoefficientModels.identityEtale Y) :=
  MorphismProperty.Over.homMk
    (pullback.lift f (𝟙 X) ((Category.comp_id f).trans (Category.id_comp f).symm)) (by
      change pullback.lift f (𝟙 X) _ ≫ pullback.snd (𝟙 Y) f = 𝟙 X
      exact pullback.lift_snd _ _ _)

def monoidRingMap {P Q : CommMonCat.{0}} (a : P →* Q) :
    MonoidAlgebra ℤ P →+* MonoidAlgebra ℤ Q :=
  (MonoidAlgebra.lift ℤ (MonoidAlgebra ℤ Q) P
    ((MonoidAlgebra.of ℤ Q).comp a)).toRingHom

def monoidSchemeMap {P Q : CommMonCat.{0}} (a : P →* Q) :
    monoidScheme Q ⟶ monoidScheme P := Spec.map (CommRingCat.ofHom (monoidRingMap a))

variable (D : RegularSectionComparisons)

/-- Every chart generator follows the actual log arrow, not just alpha. -/
structure ChartMorphism {X Y : LogScheme.{0}} (f : EtaleLogSchemes.Hom X Y)
    (CX : SmallChart X) (CY : SmallChart Y) where
  monoidMap : CY.monoid →* CX.monoid
  log_generators : ∀ p : CY.monoid,
    (monoid X.scheme.smallEtaleTopology X.log).obj.map (identityDiagonal f.map).op
      (f.logMap.left.hom.app (op (KatoChartCoefficientModels.identityEtale Y.scheme))
        (logGenerator CY (ULift.up p))) = logGenerator CX (ULift.up (monoidMap p))
  square : f.map ≫ schemeMap D CY = schemeMap D CX ≫ monoidSchemeMap monoidMap

def chartComparison {X Y : LogScheme.{0}} {f : EtaleLogSchemes.Hom X Y}
    {CX : SmallChart X} {CY : SmallChart Y} (A : ChartMorphism D f CX CY) :
    X.scheme ⟶ pullback (schemeMap D CY) (monoidSchemeMap A.monoidMap) :=
  pullback.lift f.map (schemeMap D CX) A.square

/-- Actual fppf chart neighbourhoods on source and target, with strict
log maps, the full original commuting log-section square, and Kummer chart
maps (Talpo--Vistoli, Remark 6.11). Without the Kummer condition on the chart
map a chart in the units can make the chart comparison an isomorphism for a
nonflat map. -/
structure LogFlatAtlas {X Y : LogScheme.{0}} (f : EtaleLogSchemes.Hom X Y) where
  index : Type
  source : index → LogScheme.{0}
  target : index → LogScheme.{0}
  sourceMap : ∀ i, EtaleLogSchemes.Hom (source i) X
  targetMap : ∀ i, EtaleLogSchemes.Hom (target i) Y
  localMap : ∀ i, EtaleLogSchemes.Hom (source i) (target i)
  source_flat : ∀ i, Flat (sourceMap i).map
  source_lfp : ∀ i, LocallyOfFinitePresentation (sourceMap i).map
  target_flat : ∀ i, Flat (targetMap i).map
  target_lfp : ∀ i, LocallyOfFinitePresentation (targetMap i).map
  source_cover : ∀ x : X.scheme, ∃ (i : index) (y : (source i).scheme), (sourceMap i).map y = x
  target_cover : ∀ x : Y.scheme, ∃ (i : index) (y : (target i).scheme), (targetMap i).map y = x
  source_strict : ∀ i, EtaleLogDiagrams.IsStrict (sourceMap i)
  target_strict : ∀ i, EtaleLogDiagrams.IsStrict (targetMap i)
  log_square : ∀ i, EtaleLogDiagrams.Square (sourceMap i) f (localMap i) (targetMap i)
  sourceChart : ∀ i, SmallChart (source i)
  targetChart : ∀ i, SmallChart (target i)
  chartMap : ∀ i, ChartMorphism D (localMap i) (sourceChart i) (targetChart i)
  /-- The chart monoid maps are Kummer. -/
  chart_kummer : ∀ i, IsKummerMonoidMap (CommMonCat.ofHom (chartMap i).monoidMap)
  comparison_flat : ∀ i, Flat (chartComparison D (chartMap i))

/-- The actual characteristic maps at every separably closed geometric point. -/
structure KummerStalks {X Y : LogScheme.{0}} (f : EtaleLogSchemes.Hom X Y) where
  maps : ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X.scheme), GhostMap f x
  kummer : ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X.scheme), IsKummerMonoidMap (maps Ω x).map

/-- Source definition: fs, log-flat, geometric Kummer and underlying LFP. -/
structure KummerFlatData {X Y : LogScheme.{0}} (f : EtaleLogSchemes.Hom X Y) where
  source_fs : X.IsFineSaturated
  target_fs : Y.IsFineSaturated
  locally_finite_presentation : LocallyOfFinitePresentation f.map
  log_flat : LogFlatAtlas D f
  stalks : KummerStalks f

def IsKummerFlat {X Y : LogScheme.{0}} (f : EtaleLogSchemes.Hom X Y) : Prop :=
  Nonempty (KummerFlatData D f)

section Site

variable [N : NativeCategoryModel.{0}]

def fineSaturatedProperty : ObjectProperty (LogScheme.{0}) := fun X => X.IsFineSaturated

abbrev FineSaturatedSchemes := fineSaturatedProperty.FullSubcategory

def siteProperty (X : LogScheme.{0}) : ObjectProperty (Over X) := fun U =>
  IsKummerFlat D U.hom

/-- Objects are actual Kfl log arrows; every native log arrow over X is allowed. -/
abbrev Site (X : LogScheme.{0}) := (siteProperty D X).FullSubcategory

/-- Coverings are the actual jointly surjective Kummer-flat log arrows. -/
def precoverage (X : LogScheme.{0}) : Precoverage (Site D X) where
  coverings U := {s | ∃ (I : Type) (V : I → Site D X) (f : ∀ i, V i ⟶ U),
    (∀ i, IsKummerFlat D (f i).hom.left) ∧
    (∀ x : U.obj.left.scheme, ∃ (i : I) (y : (V i).obj.left.scheme),
      (f i).hom.left.map y = x) ∧ s = Presieve.ofArrows V f}

def topology (X : LogScheme.{0}) : GrothendieckTopology (Site D X) :=
  (precoverage D X).toGrothendieck

end Site

end MathlibExt.AlgebraicGeometry.NativeKummerFlatModels
