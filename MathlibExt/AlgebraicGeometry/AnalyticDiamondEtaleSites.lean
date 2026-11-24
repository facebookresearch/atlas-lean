/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticAdicDiamondification
public import MathlibExt.AlgebraicGeometry.PerfectoidSliceSites
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# The actual analytic and diamond etale sites

Analytic etaleness is tested at each actual point by affinoid charts
whose original Tate-ring map is finite etale. It is defined before
diamondification. Representable etaleness on the diamond side uses the
actual affine pullbacks, their open perfectoid atlases, and the actual
etale ring maps to the test affine. The site comparison is restriction
of the prescribed diamondification functor on every object and arrow.

Source: Scholze, arXiv:1709.07343v4, Definitions 10.1 and 15.5,
Lemma 15.6. The finite etale subsite uses the actual global finite-ring
condition and its source/target affinoid charts.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.AnalyticDiamondEtaleSites

open CategoryTheory CategoryTheory.Limits Opposite Topology
open AffinePerfectoidVSite PerfectoidDiamondModels
open AnalyticTateAdicModels AnalyticAdicDiamondification

variable (p : ℕ) [Fact p.Prime]

/-- An actual affinoid open chart, including its local-ring isomorphisms and the identification of
the topological section rings of opens inside its image. -/
structure Chart (X : AnalyticAdicSpace p) where
  pair : TatePair p
  model : AffinoidModel p pair
  map : model.valued ⟶ X.obj
  open_embedding : IsOpenEmbedding map.val.base
  stalk_iso : ∀ x, IsIso (map.val.stalkMap x)
  sections : SectionsHomeomorphic map.val

/-- An actual affinoid morphism fixes every point and every original coordinate. -/
structure AffinoidMap {X Y : AnalyticAdicSpace p}
    (U : Chart p X) (V : Chart p Y) where
  ring : TateRingMap p V.pair U.pair
  valued : U.model.valued ⟶ V.model.valued
  points : ∀ x, V.model.point (valued.val.base x) = ring.spa p (U.model.point x)
  coordinates : ∀ a : V.pair.ring,
    (valued.val.c.app (op ⊤)) (V.model.globalRing a) =
      U.model.globalRing (ring.hom a)

/-- A finite étale map of Tate pairs (Scholze, *Étale cohomology of diamonds*, Def. 6.2(i)): the
ring map is finite étale and the target plus ring is the integral closure of the image of the source
plus ring. -/
def IsFiniteEtalePair {V W : TatePair p} (g : TateRingMap p V W) : Prop :=
  letI := g.hom.toAlgebra
  Module.Finite V.ring W.ring ∧ Algebra.Etale V.ring W.ring ∧
    ∀ s : W.ring, s ∈ W.plus ↔ (g.hom.comp V.plus.subtype).IsIntegralElem s

/-- Local finite etaleness of an affinoid map is finite étaleness of its map of Tate pairs. -/
def IsFiniteEtale {X Y : AnalyticAdicSpace p}
    {U : Chart p X} {V : Chart p Y} (f : AffinoidMap p U V) : Prop :=
  IsFiniteEtalePair p f.ring

/-- An affinoid map is étale on charts if its map of Tate pairs is a rational localization of a
finite étale map, up to an isomorphism of Tate pairs (Scholze, Def. 6.2(ii): locally an open
embedding followed by a finite étale map). -/
def IsChartEtale {X Y : AnalyticAdicSpace p}
    {U : Chart p X} {V : Chart p Y} (f : AffinoidMap p U V) : Prop :=
  ∃ (W : TatePair p) (g : TateRingMap p V.pair W) (D : RationalTateModel p W)
    (e : D.pair.ring ≃+* U.pair.ring),
    IsFiniteEtalePair p g ∧ Continuous e ∧ Continuous e.symm ∧
      (∀ a, a ∈ D.pair.plus ↔ e a ∈ U.pair.plus) ∧
      f.ring.hom = e.toRingHom.comp (D.map.hom.comp g.hom)

/-- An actual etale chart of the given analytic morphism at its given point. -/
structure EtaleChart {X Y : AnalyticAdicSpace p} (f : X ⟶ Y) (x : X.obj.space) where
  source : Chart p X
  target : Chart p Y
  point : x ∈ Set.range source.map.val.base
  map : AffinoidMap p source target
  square : source.map ≫ f.hom = map.valued ≫ target.map
  etale : IsChartEtale p map

/-- Analytic etaleness is defined on the actual Tate-ring charts before diamondification. -/
def IsAnalyticEtale {X Y : AnalyticAdicSpace p} (f : X ⟶ Y) : Prop :=
  ∀ x : X.obj.space, Nonempty (EtaleChart p f x)

/-- The genuine analytic etale objects over the specified original space. -/
abbrev AnalyticEtaleSite (Y : AnalyticAdicSpace p) :=
  (show ObjectProperty (Over Y) from
    fun T ↦ IsAnalyticEtale p T.hom).FullSubcategory

/-- The etale covering topology retains actual surjectivity on all original points. -/
def analyticEtaleTopology (Y : AnalyticAdicSpace p) :
    GrothendieckTopology (AnalyticEtaleSite p Y) :=
  sInf {J | ∀ (I : Type 1) (T : AnalyticEtaleSite p Y)
    (U : I → AnalyticEtaleSite p Y) (f : ∀ i, U i ⟶ T),
    (∀ i, IsAnalyticEtale p (f i).hom.left) →
    (∀ x : T.obj.left.obj.space,
      ∃ i, x ∈ Set.range (f i).hom.left.hom.val.base) → Sieve.ofArrows U f ∈ J T}

/-- Representable etaleness uses every actual perfectoid affine pullback. -/
def IsRepresentableEtale {F G : VSheaf p} (f : F ⟶ G) : Prop :=
  ∀ (P : Affine p) (a : affineSheaf p P ⟶ G),
    ∃ A : OpenAtlas p (pullback f a),
      ∃ g : ∀ i, A.affine i ⟶ P,
        (∀ i, A.chart i ≫ pullback.snd f a = affineMap p (g i)) ∧
        (∀ i, PerfectoidLocalModels.IsEtale p (g i))

/-- The actual small representable-etale site over the specified diamond sheaf. -/
abbrev DiamondEtaleSite (G : VSheaf p) :=
  (show ObjectProperty (Over G) from
    fun T ↦ IsRepresentableEtale p T.hom).FullSubcategory

/-- Covering families are jointly epimorphic actual etale sheaf maps. -/
def diamondEtaleTopology (G : VSheaf p) :
    GrothendieckTopology (DiamondEtaleSite p G) :=
  sInf {J | ∀ (I : Type 1) (T : DiamondEtaleSite p G)
    (U : I → DiamondEtaleSite p G) (f : ∀ i, U i ⟶ T),
    (∀ i, IsRepresentableEtale p (f i).hom.left) →
    JointlyEpi p (fun i ↦ (U i).obj.left) (fun i ↦ (f i).hom.left) →
      Sieve.ofArrows U f ∈ J T}

/-- Preservation is a conclusion about the prescribed diamondification map. -/
def PreservesEtale (R : AffineRealization p) : Prop :=
  ∀ {X Y : AnalyticAdicSpace p} (f : X ⟶ Y),
    IsAnalyticEtale p f → IsRepresentableEtale p ((diamondFunctor p R).map f)

/-- The induced etale-site functor uses the actual diamondification on every arrow. -/
def etaleDiamondification (R : AffineRealization p) (Y : AnalyticAdicSpace p)
    (h : PreservesEtale p R) :
    AnalyticEtaleSite p Y ⥤ DiamondEtaleSite p ((diamondFunctor p R).obj Y) where
  obj T := ⟨(Over.post (diamondFunctor p R)).obj T.obj, h T.obj.hom T.property⟩
  map f := ObjectProperty.homMk ((Over.post (diamondFunctor p R)).map f.hom)

/-- Restriction of actual etale sheaves along that fixed site comparison. -/
def etaleInverseImage (R : AffineRealization p) (Y : AnalyticAdicSpace p)
    (h : PreservesEtale p R)
    [(etaleDiamondification p R Y h).IsContinuous (analyticEtaleTopology p Y)
      (diamondEtaleTopology p ((diamondFunctor p R).obj Y))] :
    Sheaf (diamondEtaleTopology p ((diamondFunctor p R).obj Y)) (Type 1) ⥤
      Sheaf (analyticEtaleTopology p Y) (Type 1) :=
  (etaleDiamondification p R Y h).sheafPushforwardContinuous (Type 1)
    (analyticEtaleTopology p Y) (diamondEtaleTopology p ((diamondFunctor p R).obj Y))

/-- Finite etaleness retains the full affinoid inverse image of every original affinoid chart. -/
def IsAnalyticFiniteEtale {X Y : AnalyticAdicSpace p} (f : X ⟶ Y) : Prop :=
  ∀ V : Chart p Y, ∃ U : Chart p X, ∃ g : AffinoidMap p U V,
    U.map ≫ f.hom = g.valued ≫ V.map ∧ IsFiniteEtale p g ∧
      Set.range U.map.val.base = f.hom.val.base ⁻¹' Set.range V.map.val.base

/-- Finite-etale diamond maps: every affine pullback is empty (initial) or an actual finite-étale
affine, with fixed projection. Empty pullbacks occur for the empty map, and for the inclusion of an
open and closed component tested on the complementary component. -/
def IsRepresentableFiniteEtale {F G : VSheaf p} (f : F ⟶ G) : Prop :=
  ∀ (Q : Affine p) (a : affineSheaf p Q ⟶ G),
    Nonempty (IsInitial (pullback f a)) ∨
      ∃ P : Affine p, ∃ e : affineSheaf p P ≅ pullback f a, ∃ g : P ⟶ Q,
        e.hom ≫ pullback.snd f a = affineMap p g ∧ PerfectoidLocalModels.IsFiniteEtale g

/-- Actual finite-etale objects over the original analytic space. -/
abbrev AnalyticFiniteEtaleSite (Y : AnalyticAdicSpace p) :=
  (show ObjectProperty (Over Y) from
    fun T ↦ IsAnalyticFiniteEtale p T.hom).FullSubcategory

/-- Actual finite-etale sheaf arrows over the specified diamondification. -/
abbrev DiamondFiniteEtaleSite (G : VSheaf p) :=
  (show ObjectProperty (Over G) from
    fun T ↦ IsRepresentableFiniteEtale p T.hom).FullSubcategory

/-- Finite-etale preservation refers to the same prescribed source diamondification. -/
def PreservesFiniteEtale (R : AffineRealization p) : Prop :=
  ∀ {X Y : AnalyticAdicSpace p} (f : X ⟶ Y), IsAnalyticFiniteEtale p f →
    IsRepresentableFiniteEtale p ((diamondFunctor p R).map f)

/-- The actual finite-etale comparison on every object and original map. -/
def finiteEtaleDiamondification (R : AffineRealization p) (Y : AnalyticAdicSpace p)
    (h : PreservesFiniteEtale p R) : AnalyticFiniteEtaleSite p Y ⥤
    DiamondFiniteEtaleSite p ((diamondFunctor p R).obj Y) where
  obj T := ⟨(Over.post (diamondFunctor p R)).obj T.obj, h T.obj.hom T.property⟩
  map f := ObjectProperty.homMk ((Over.post (diamondFunctor p R)).map f.hom)

end MathlibExt.AlgebraicGeometry.AnalyticDiamondEtaleSites
