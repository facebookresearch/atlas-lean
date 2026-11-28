/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticProEtaleCoefficientSources
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Topology.Maps.Basic

/-!
# Proper and smooth source geometry over a general p-adic base

The base is the actual all-rank Spa of the original complete discretely
valued field and its ring of integers. Affinoid finite type and smooth
charts use continuous restricted power series and the original Tate-ring
maps, rather than algebraic smoothness of raw global section rings.

Properness retains finite type, quasi-compactness, the actual diagonal
closed immersion and universal closedness under EVERY actual analytic
pullback. Existence of those pullbacks is included. The formal pro-site
base change is restriction of a source-normalized extension on the full
ind-presheaf categories, with its colimit property on every presentation.

References: Scholze, arXiv:1205.3463v2, Sections 3 and 8; Wedhorn,
arXiv:1910.05934v1, Sections 5--8 (the analytic affinoid realization reused
by `AnalyticTateAdicModels`). Native Mathlib topology and universal
pullback squares: Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticProperSmoothSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite TopologicalSpace Topology
open AnalyticTateAdicModels AnalyticDiamondEtaleSites AnalyticProObjectSites
open GeneralPadicCoefficientFields

variable (p : ℕ) [Fact p.Prime]

/-- The base realization fixes its ring, topology, plus ring and all-rank Spa points. -/
structure BaseRealization (K : BaseField p) where
  pair : TatePair p
  ring : BaseField.carrier p K ≃+* pair.ring
  continuous : Continuous ring
  inverse_continuous : Continuous ring.symm
  integers : ∀ x, ring x ∈ pair.plus ↔ x ∈ BaseField.integralRing p K
  model : AffinoidModel p pair
  analytic : AnalyticAdicSpace p
  whole : model.valued ≅ analytic.obj

/-- Restricted series have the coefficient-uniform topology of the original Tate ring, and the
standard plus ring of the polydisc: the series with coefficients in the plus ring. In zero variables
this is the original pair itself. -/
structure TatePowerSeries (P : TatePair p) (n : ℕ) where
  series : Subring (MvPowerSeries (Fin n) P.ring)
  restricted : ∀ f, f ∈ series ↔ Filter.Tendsto
    (fun d => MvPowerSeries.coeff d f) Filter.cofinite (nhds 0)
  pair : TatePair p
  coordinates : pair.ring ≃+* series
  scalar : TateRingMap p P pair
  scalar_coefficients : ∀ (a : P.ring) (d : Fin n →₀ ℕ),
    MvPowerSeries.coeff d (coordinates (scalar.hom a)).val =
      if d = 0 then a else 0
  coefficient_neighborhoods : ∀ N : Set pair.ring,
    N ∈ nhds (0 : pair.ring) ↔
      ∃ V : Set P.ring, V ∈ nhds (0 : P.ring) ∧
        {f | ∀ d, MvPowerSeries.coeff d (coordinates f).val ∈ V} ⊆ N
  plus_coefficients : ∀ f : pair.ring,
    f ∈ pair.plus ↔ ∀ d, MvPowerSeries.coeff d (coordinates f).val ∈ P.plus

/-- Topological finite type is an actual continuous quotient of restricted series. -/
def IsTopologicallyFiniteType {P Q : TatePair p} (f : TateRingMap p P Q) : Prop :=
  ∃ (n : ℕ) (T : TatePowerSeries p P n) (q : TateRingMap p T.pair Q),
    IsQuotientMap q.hom ∧ q.hom.comp T.scalar.hom = f.hom

variable {X Y : AnalyticAdicSpace p}

structure FiniteTypeChart (f : X ⟶ Y) (x : X.obj.space) where
  source : Chart p X
  target : Chart p Y
  contains : x ∈ Set.range source.map.val.base
  map : AffinoidMap p source target
  square : source.map ≫ f.hom = map.valued ≫ target.map
  finiteType : IsTopologicallyFiniteType p map.ring

def IsLocallyFiniteType (f : X ⟶ Y) : Prop :=
  ∀ x : X.obj.space, Nonempty (FiniteTypeChart p f x)

/-- A smooth chart is finite etale over a rational open in an actual relative polydisc. Finite
étaleness is that of the map of Tate pairs, including the integral closure of the plus rings, so a
change of plus ring alone (which need not have open image) is not smooth. -/
structure SmoothChart (f : X ⟶ Y) (x : X.obj.space) where
  source : Chart p X
  target : Chart p Y
  contains : x ∈ Set.range source.map.val.base
  map : AffinoidMap p source target
  square : source.map ≫ f.hom = map.valued ≫ target.map
  dimension : ℕ
  polydisc : TatePowerSeries p target.pair dimension
  neighborhood : RationalTateModel p polydisc.pair
  etale : TateRingMap p neighborhood.pair source.pair
  finite_etale : IsFiniteEtalePair p etale
  coefficients : etale.hom.comp (neighborhood.map.hom.comp polydisc.scalar.hom) = map.ring.hom

def IsSmooth (f : X ⟶ Y) : Prop := ∀ x, Nonempty (SmoothChart p f x)

def IsQuasiCompact (f : X ⟶ Y) : Prop :=
  ∀ U : Opens Y.obj.space, IsCompact (U : Set Y.obj.space) →
    IsCompact (f.hom.val.base ⁻¹' (U : Set Y.obj.space))

def IsClosedImmersion (f : X ⟶ Y) : Prop :=
  IsClosedEmbedding f.hom.val.base ∧
    ∀ x : X.obj.space, Function.Surjective (f.hom.val.stalkMap x)

/-- A base change is the native universal square in the original analytic category. -/
structure BaseChange (f : X ⟶ Y) (Z : AnalyticAdicSpace p) (g : Z ⟶ Y) where
  space : AnalyticAdicSpace p
  first : space ⟶ X
  second : space ⟶ Z
  square : IsPullback first second f g

def IsSeparated (f : X ⟶ Y) : Prop :=
  ∀ (B : BaseChange p f X f) (d : X ⟶ B.space),
    d ≫ B.first = 𝟙 X → d ≫ B.second = 𝟙 X → IsClosedImmersion p d

/-- No algebraic model or single test base change substitutes for analytic properness. -/
def IsProper (f : X ⟶ Y) : Prop :=
  IsLocallyFiniteType p f ∧ IsQuasiCompact p f ∧ IsSeparated p f ∧
    (∀ (Z : AnalyticAdicSpace p) (g : Z ⟶ Y), Nonempty (BaseChange p f Z g)) ∧
    (∀ (Z : AnalyticAdicSpace p) (g : Z ⟶ Y) (B : BaseChange p f Z g),
      IsClosedMap B.second.hom.val.base)

variable {K : BaseField p} (B : BaseRealization p K)

abbrev SpaceOver := Over B.analytic

/-- The actual source scope of Scholze's relative Theorem 8.8. -/
def RelativeScope (X Y : SpaceOver p B) (f : X ⟶ Y) : Prop :=
  IsLocallyNoetherian p X.left ∧ IsLocallyNoetherian p Y.left ∧
    IsSmooth p X.hom ∧ IsSmooth p Y.hom ∧ IsProper p f.left ∧ IsSmooth p f.left

section SiteBaseChange

variable {X Y : AnalyticAdicSpace p} (f : X ⟶ Y)

def etaleUnderlying (T : AnalyticAdicSpace p) : Etale p T ⥤ AnalyticAdicSpace p :=
  ObjectProperty.ι _ ⋙ Over.forget T

/-- Small etale base change retains every actual analytic universal pullback. -/
structure EtaleBaseChangeSource where
  functor : Etale p Y ⥤ Etale p X
  projection : functor ⋙ etaleUnderlying p X ⟶ etaleUnderlying p Y
  pullback : ∀ U : Etale p Y,
    IsPullback (projection.app U) (functor.obj U).obj.hom U.obj.hom f

namespace EtaleBaseChangeSource

variable (E : EtaleBaseChangeSource p f)

/-- The original ring map is native Γ of the original analytic projection. -/
def regularScalar :
    AnalyticProEtaleCoefficientSources.etaleRings p Y ⟶
      E.functor.op ⋙ AnalyticProEtaleCoefficientSources.etaleRings p X where
  app U := _root_.AlgebraicGeometry.LocallyRingedSpace.Γ.map
    ((E.projection.app U.unop).hom.val).op
  naturality {U V} g := by
    have h := congrArg (fun k => k.hom.val) (E.projection.naturality g.unop)
    change _root_.AlgebraicGeometry.LocallyRingedSpace.Γ.map
      (g.unop.hom.left.hom.val).op ≫
        _root_.AlgebraicGeometry.LocallyRingedSpace.Γ.map (E.projection.app V.unop).hom.val.op =
      _root_.AlgebraicGeometry.LocallyRingedSpace.Γ.map (E.projection.app U.unop).hom.val.op ≫
        _root_.AlgebraicGeometry.LocallyRingedSpace.Γ.map
          (E.functor.map g.unop).hom.left.hom.val.op
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _root_.AlgebraicGeometry.LocallyRingedSpace.Γ.map
      (congrArg (fun a => a.op) h.symm)

end EtaleBaseChangeSource

/-- Extension on full ind-presheaves is normalized on all Yoneda objects and all presentations. -/
structure ProBaseChangeSource (E : EtaleBaseChangeSource p f) where
  presheaf : Presheaves p Y ⥤ Presheaves p X
  yoneda : _root_.CategoryTheory.yoneda ⋙ presheaf ≅
    E.functor.op ⋙ _root_.CategoryTheory.yoneda
  colimit : ∀ {F : Presheaves p Y} (P : ProEtalePresentation p Y F),
    IsColimit (presheaf.mapCocone P.ind.cocone)
  closed : ∀ (F : Presheaves p Y), IsProEtaleObject p Y F →
    IsProEtaleObject p X (presheaf.obj F)

namespace ProBaseChangeSource

variable {E : EtaleBaseChangeSource p f} (Q : ProBaseChangeSource p f E)

/-- This acts on FULL formal pro-morphisms by the same normalized native extension. -/
def functor : ProEtaleSite p Y ⥤ ProEtaleSite p X :=
  (ObjectProperty.lift (IsProEtaleObject p X)
    (ObjectProperty.ι (IsProEtaleObject p Y) ⋙ Q.presheaf)
    (fun U => Q.closed U.obj U.property)).op

end ProBaseChangeSource

end SiteBaseChange

end MathlibExt.AlgebraicGeometry.AnalyticProperSmoothSources
