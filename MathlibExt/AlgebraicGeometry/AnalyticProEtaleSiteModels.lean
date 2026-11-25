/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticDiamondEtaleSites
public import Mathlib.CategoryTheory.Limits.Filtered

/-!
# Represented local analytic pro-étale presentations

Local presentations are normalized cofiltered systems of the original
finite-étale Tate rings with surjective transition point maps. These
representations are a local complete-ring boundary; the full formal
pro-object site and its basis comparison are separate source adapters. Their
limiting ring is characterized by continuous plus-preserving
maps of complete Tate rings, and their all-rank adic points are the actual
compatible point families. No tilting criterion defines pro-étaleness.

Coverings include joint surjectivity and the finite compact-open refinement
condition on this represented boundary, including non-quasicompact
analytic spaces. Étale charts and valuations are the existing original
general analytic models, with no perfectoid restriction.

Reference: Scholze, arXiv:1205.3463v2, Definition 3.9; BMS18,
arXiv:1602.03148v3, Section 3.1; BMS19, arXiv:1802.03261v2, Section 10.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticProEtaleSiteModels

open CategoryTheory CategoryTheory.Limits Opposite Topology TopologicalSpace
open AnalyticTateAdicModels AnalyticDiamondEtaleSites

variable (p : ℕ)

@[ext]
theorem tateMap_ext {P Q : TatePair p} {f g : TateRingMap p P Q}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Geometric orientation on the original complete Tate pairs. -/
instance : Category (TatePair p) where
  Hom P Q := TateRingMap p Q P
  id P := ⟨RingHom.id P.ring, continuous_id, fun _ h ↦ h⟩
  comp f g := ⟨f.hom.comp g.hom, f.continuous.comp g.continuous, fun _ h ↦ f.plus _ (g.plus _ h)⟩
  id_comp _ := by apply tateMap_ext; ext a; rfl
  comp_id _ := by apply tateMap_ext; ext a; rfl
  assoc _ _ _ := by apply tateMap_ext; ext a; rfl

/-- Finite étale maps of Tate pairs (Scholze, *Étale cohomology of diamonds*, Def. 6.2(i)): the
ring map is finite étale and the plus ring of the source is the integral closure of the image of
the plus ring of the target. -/
def IsFiniteEtale {P Q : TatePair p} (f : P ⟶ Q) : Prop :=
  letI := f.hom.toAlgebra
  Module.Finite Q.ring P.ring ∧ Algebra.Etale Q.ring P.ring ∧
    ∀ s : P.ring, s ∈ P.plus ↔ (f.hom.comp Q.plus.subtype).IsIntegralElem s

/-- Standard étale maps of Tate pairs: a rational localization of a finite étale map, up to an
isomorphism of Tate pairs. -/
def IsStandardEtale {P Q : TatePair p} (f : P ⟶ Q) : Prop :=
  ∃ (W : TatePair p) (g : W ⟶ Q) (D : RationalTateModel p W) (e : D.pair.ring ≃+* P.ring),
    IsFiniteEtale p g ∧ Continuous e ∧ Continuous e.symm ∧
      (∀ a, a ∈ D.pair.plus ↔ e a ∈ P.plus) ∧
      f.hom = e.toRingHom.comp (D.map.hom.comp g.hom)

/-- Étale maps of Tate pairs (Scholze, *Étale cohomology of diamonds*, Def. 6.2(ii): locally an
open embedding followed by a finite étale map): every point `x` of the source has a rational
neighbourhood `V`, and `f x` a rational neighbourhood `U` of the target, such that `f` restricts to
a standard étale map from `V` to `U`. -/
def IsEtale {P Q : TatePair p} (f : P ⟶ Q) : Prop :=
  ∀ x : P.Space, ∃ (V : RationalTateModel p P) (U : RationalTateModel p Q) (g : V.pair ⟶ U.pair),
    x ∈ V.domain ∧ f.spa p x ∈ U.domain ∧
      (show V.pair ⟶ P from V.map) ≫ f = g ≫ (show U.pair ⟶ Q from U.map) ∧
      IsStandardEtale p g

def CompatiblePoints {I : Type} [SmallCategory I] (D : I ⥤ TatePair p) :=
  {x : ∀ i, (D.obj i).Space |
    ∀ {i j} (f : i ⟶ j), (D.map f).spa p (x i) = x j}

/-- Actual complete-ring and all-rank point limits of étale charts with finite étale transition
maps. The stages are only étale over the target, not finite étale: rational localizations are
pro-étale. -/
structure ProEtalePresentation {P Q : TatePair p} (f : P ⟶ Q) where
  index : Type
  [category : SmallCategory index]
  [cofiltered : IsCofiltered index]
  diagram : index ⥤ TatePair p
  base : diagram ⟶ (Functor.const index).obj Q
  etale : ∀ i, IsEtale p (base.app i)
  transition_finite_etale : ∀ {i j} (g : i ⟶ j), IsFiniteEtale p (diagram.map g)
  transition_surjective : ∀ {i j} (g : i ⟶ j), Function.Surjective ((diagram.map g).spa p)
  cone : (Functor.const index).obj P ⟶ diagram
  triangle : ∀ i, cone.app i ≫ base.app i = f
  point : P.Space ≃ₜ CompatiblePoints p diagram
  point_normalized : ∀ x i, (point x).val i = (cone.app i).spa p x
  ring_universal : ∀ (C : TatePair p) (g : ∀ i, TateRingMap p (diagram.obj i) C),
    (∀ {i j} (h : i ⟶ j), (g i).hom.comp (diagram.map h).hom = (g j).hom) →
    ∃! h : TateRingMap p P C, ∀ i, h.hom.comp (cone.app i).hom = (g i).hom

variable [Fact p.Prime]

/-- A local chart of the original analytic map, including its source/target
coordinates and the actual complete-ring limit. -/
structure ProEtaleChart {X Y : AnalyticAdicSpace p} (f : X ⟶ Y) (x : X.obj.space) where
  source : Chart p X
  target : Chart p Y
  point : x ∈ Set.range source.map.val.base
  map : AffinoidMap p source target
  square : source.map ≫ f.hom = map.valued ≫ target.map
  presentation : ProEtalePresentation p map.ring

def IsAnalyticProEtale {X Y : AnalyticAdicSpace p} (f : X ⟶ Y) : Prop :=
  ∀ x : X.obj.space, Nonempty (ProEtaleChart p f x)

abbrev ProEtaleSite (Y : AnalyticAdicSpace p) :=
  (show ObjectProperty (Over Y) from fun T ↦ IsAnalyticProEtale p T.hom).FullSubcategory

variable {Y : AnalyticAdicSpace p}

/-- The actual compact-open covering rule, including nonvacuous coverage of every point. -/
def IsCover {I : Type 1} {T : ProEtaleSite p Y} (U : I → ProEtaleSite p Y)
    (f : ∀ i, U i ⟶ T) : Prop := by
  classical
  exact (∀ x : T.obj.left.obj.space,
    ∃ i, x ∈ Set.range (f i).hom.left.hom.val.base) ∧
    ∀ V : Opens T.obj.left.obj.space, IsCompact (V : Set T.obj.left.obj.space) →
      ∃ (s : Finset I) (W : ∀ i ∈ s, Opens (U i).obj.left.obj.space),
        (∀ i (h : i ∈ s), IsCompact (W i h : Set (U i).obj.left.obj.space)) ∧
        ∀ x ∈ V, ∃ (i : I) (h : i ∈ s) (y : (U i).obj.left.obj.space),
          y ∈ W i h ∧ (f i).hom.left.hom.val.base y = x

def proEtaleTopology (Y : AnalyticAdicSpace p) : GrothendieckTopology (ProEtaleSite p Y) :=
  sInf {J | ∀ (I : Type 1) (T : ProEtaleSite p Y)
    (U : I → ProEtaleSite p Y) (f : ∀ i, U i ⟶ T),
    (∀ i, IsAnalyticProEtale p (f i).hom.left) → IsCover p U f → Sieve.ofArrows U f ∈ J T}

def forget (Y : AnalyticAdicSpace p) : ProEtaleSite p Y ⥤ AnalyticAdicSpace p :=
  ObjectProperty.ι _ ⋙ Over.forget Y

end MathlibExt.AlgebraicGeometry.AnalyticProEtaleSiteModels
