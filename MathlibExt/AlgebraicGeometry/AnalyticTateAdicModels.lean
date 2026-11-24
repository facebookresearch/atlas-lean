/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry

/-!
# Actual analytic Tate-adic spaces and affine realizations

Tate pairs need not be uniform. Their points are the actual all-rank
continuous valuations, and rational localizations retain their complete
ring universal property and actual point map. Affinoid realizations use
native locally ringed spaces with valuations on their actual stalks.
Every rational section ring and every integral-section test is fixed
against the actual rational localization. Global objects are spaces
covered by these actual valued affinoid charts.

The affine perfectoid realization input fixes every global coordinate
and original Spa point map. It is integration of the completed local
adic realization/gluing source, not a new abstract analytic carrier.

Sources: Scholze, arXiv:1709.07343v4, Section 15; Wedhorn,
arXiv:1910.05934v1, Sections 5--8. Completed local realization and
gluing integration: TauCetiProject/TauCeti revision
62bbc0596dc3539d488232e4e924a338548ea0a9,
AdicSpace/PreAdicSpace/Affinoid/PairEquiv.lean and Gluing.lean.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.AnalyticTateAdicModels

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open _root_.AlgebraicGeometry
open MathlibExt.RingTheory.CompleteHuberPairModels
open AffineAdicSpectra AffineUntiltingGeometry

/-- A native locally ringed space with actual valuations on its stalk rings and topologies on its
rings of sections. -/
structure ValuedSpace where
  space : LocallyRingedSpace.{0}
  valuation : ∀ x : space, ValuativeRel (space.presheaf.stalk x)
  sectionTopology : ∀ U : Opens space, TopologicalSpace (space.presheaf.obj (op U))

/-- The pullback of sections over `U` along a morphism of locally ringed spaces is continuous for
the section topologies. -/
def SectionsContinuous {X Y : ValuedSpace} (f : X.space ⟶ Y.space) : Prop :=
  ∀ U : Opens Y.space,
    @Continuous _ _ (Y.sectionTopology U) (X.sectionTopology ((Opens.map f.base).obj U))
      (f.c.app (op U)).hom

/-- The pullback of sections along a morphism of locally ringed spaces identifies the topological
section rings of every open inside the image of the morphism. -/
def SectionsHomeomorphic {X Y : ValuedSpace} (f : X.space ⟶ Y.space) : Prop :=
  ∀ U : Opens Y.space, (U : Set Y.space) ⊆ Set.range f.base →
    @IsHomeomorph _ _ (Y.sectionTopology U) (X.sectionTopology ((Opens.map f.base).obj U))
      (f.c.app (op U)).hom

/-- A morphism preserves the actual stalk valuation comparisons and pulls back sections
continuously: morphisms of analytic adic spaces are locally induced by continuous maps of
affinoid rings (Wedhorn, *Adic Spaces*, Prop. 8.19), not by arbitrary ring maps. -/
def ValuedHom (X Y : ValuedSpace) :=
  {f : X.space ⟶ Y.space // (∀ (x : X.space)
    (a b : Y.space.presheaf.stalk (f.base x)),
    (Y.valuation (f.base x)).vle a b ↔
      (X.valuation x).vle ((f.stalkMap x) a) ((f.stalkMap x) b)) ∧
    SectionsContinuous f}

instance : Category ValuedSpace where
  Hom := ValuedHom
  id X := ⟨𝟙 X.space, by
    intro x a b
    rw [LocallyRingedSpace.stalkMap_id]
    rfl, fun U ↦ by
    change @Continuous _ _ (X.sectionTopology U) (X.sectionTopology U) id
    exact @continuous_id _ (X.sectionTopology U)⟩
  comp {X Y Z} f g := ⟨f.val ≫ g.val, by
    intro x a b
    rw [LocallyRingedSpace.stalkMap_comp]
    exact (g.property.1 (f.val.base x) a b).trans
      (f.property.1 x ((g.val.stalkMap (f.val.base x)) a)
        ((g.val.stalkMap (f.val.base x)) b)), fun U ↦ by
    let := Z.sectionTopology U
    let := Y.sectionTopology ((Opens.map g.val.base).obj U)
    let := X.sectionTopology ((Opens.map f.val.base).obj ((Opens.map g.val.base).obj U))
    exact (f.property.2 ((Opens.map g.val.base).obj U)).comp (g.property.2 U)⟩
  id_comp f := Subtype.ext (Category.id_comp f.val)
  comp_id f := Subtype.ext (Category.comp_id f.val)
  assoc f g h := Subtype.ext (Category.assoc f.val g.val h.val)

/-- The actual forgetful functor to locally ringed spaces. -/
def forgetValuations : ValuedSpace ⥤ LocallyRingedSpace where
  obj X := X.space
  map f := f.val

variable (p : ℕ)

/-- A complete Tate Huber pair over the p-adic base; uniformity is not required. -/
structure TatePair where
  ring : CommRingCat.{0}
  [uniformSpace : UniformSpace ring]
  [uniformAdd : IsUniformAddGroup ring]
  [topologicalRing : IsTopologicalRing ring]
  [complete : CompleteSpace ring]
  [hausdorff : T2Space ring]
  definition : PairOfDefinition ring
  powerbounded : Subring ring
  powerbounded_mem : ∀ a : ring, a ∈ powerbounded ↔ IsPowerBounded ring a
  plus : Subring ring
  plus_open : IsOpen (plus : Set ring)
  plus_integral : IsIntegrallyClosedIn plus ring
  plus_bound : plus ≤ powerbounded
  parameter : ringˣ
  parameter_nilpotent : IsTopologicallyNilpotent (parameter : ring)
  p_nilpotent : IsTopologicallyNilpotent (p : ring)

attribute [instance] TatePair.uniformSpace TatePair.uniformAdd
  TatePair.topologicalRing TatePair.complete TatePair.hausdorff

/-- The actual all-rank adic point space of this general Tate pair. -/
abbrev TatePair.Space (P : TatePair p) := Spa P.plus

/-- Continuous plus-preserving maps of the actual general Tate pairs. -/
structure TateRingMap (P Q : TatePair p) where
  hom : P.ring →+* Q.ring
  continuous : Continuous hom
  plus : ∀ a ∈ P.plus, hom a ∈ Q.plus

/-- Its actual contravariant map of all-rank point spectra. -/
def TateRingMap.spa {P Q : TatePair p} (f : TateRingMap p P Q) : Q.Space → P.Space :=
  spaComap f.hom f.continuous f.plus

/-- Original perfectoid pairs include into general Tate pairs on exactly the same rings. -/
def TatePair.ofPerfectoid [Fact p.Prime] (P : PerfectoidPair p) : TatePair p where
  ring := P.ring
  definition := P.definition
  powerbounded := P.powerbounded
  powerbounded_mem := P.powerbounded_mem
  plus := P.plus
  plus_open := P.plus_open
  plus_integral := P.plus_integral
  plus_bound := P.plus_bound
  parameter := P.parameter
  parameter_nilpotent := P.parameter_nilpotent
  p_nilpotent := P.p_nilpotent

/-- A genuine complete rational localization of the actual Tate ring and plus ring. -/
structure RationalTateModel (P : TatePair p) where
  numerators : Finset P.ring
  denominator : P.ring
  open_ideal : IsOpen (Ideal.span (numerators : Set P.ring) : Set P.ring)
  pair : TatePair p
  map : TateRingMap p P pair
  fraction : ∃ u : pair.ringˣ, (u : pair.ring) = map.hom denominator ∧
    ∀ a ∈ numerators, map.hom a * ((u⁻¹ : pair.ringˣ) : pair.ring) ∈ pair.plus
  universal : ∀ (Q : TatePair p) (f : TateRingMap p P Q),
    (∃ u : Q.ringˣ, (u : Q.ring) = f.hom denominator ∧
      ∀ a ∈ numerators, f.hom a * ((u⁻¹ : Q.ringˣ) : Q.ring) ∈ Q.plus) →
    ∃! g : TateRingMap p pair Q, g.hom.comp map.hom = f.hom
  domain : Opens P.Space
  mem_domain : ∀ v : P.Space, v ∈ domain ↔
    ¬ v.1.relation.vle denominator 0 ∧
      ∀ a ∈ numerators, v.1.relation.vle a denominator
  point : pair.Space ≃ₜ domain
  point_normalized : ∀ x, (point x).val = map.spa p x

/-- An affinoid has its actual point, rational section rings and stalk valuations. Its rational
section rings are the rational localizations as topological rings. -/
structure AffinoidModel (P : TatePair p) where
  valued : ValuedSpace
  point : valued.space ≃ₜ P.Space
  globalRing : P.ring ≃+* valued.space.presheaf.obj (op ⊤)
  globalRing_continuous : @Continuous _ _ _ (valued.sectionTopology ⊤) globalRing
  globalRing_symm_continuous : @Continuous _ _ (valued.sectionTopology ⊤) _ globalRing.symm
  valuation_normalized : ∀ (x : valued.space) (a b : P.ring),
    (valued.valuation x).vle
      (valued.space.presheaf.germ ⊤ x (by trivial) (globalRing a))
      (valued.space.presheaf.germ ⊤ x (by trivial) (globalRing b)) ↔
        (point x).1.relation.vle a b
  rationalSections : ∀ (D : RationalTateModel p P) (U : Opens valued.space),
    (U : Set valued.space) = point ⁻¹' (D.domain : Set P.Space) →
      D.pair.ring ≃+* valued.space.presheaf.obj (op U)
  rationalSections_continuous : ∀ (D : RationalTateModel p P) (U : Opens valued.space)
    (h : (U : Set valued.space) = point ⁻¹' (D.domain : Set P.Space)),
    @Continuous _ _ _ (valued.sectionTopology U) (rationalSections D U h)
  rationalSections_symm_continuous : ∀ (D : RationalTateModel p P) (U : Opens valued.space)
    (h : (U : Set valued.space) = point ⁻¹' (D.domain : Set P.Space)),
    @Continuous _ _ (valued.sectionTopology U) _ (rationalSections D U h).symm
  sectionTopology_eq : ∀ U : Opens valued.space, valued.sectionTopology U =
    ⨅ (D : RationalTateModel p P) (V : Opens valued.space) (h : V ≤ U)
      (_ : (V : Set valued.space) = point ⁻¹' (D.domain : Set P.Space)),
      (valued.sectionTopology V).induced (valued.space.presheaf.map (homOfLE h).op).hom
  rational_constants : ∀ (D : RationalTateModel p P) (U : Opens valued.space)
    (h : (U : Set valued.space) = point ⁻¹' (D.domain : Set P.Space)) (a : P.ring),
    rationalSections D U h (D.map.hom a) =
      valued.space.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (globalRing a)
  rational_integral : ∀ (D : RationalTateModel p P) (U : Opens valued.space)
    (h : (U : Set valued.space) = point ⁻¹' (D.domain : Set P.Space)) (a : D.pair.ring),
    a ∈ D.pair.plus ↔ ∀ (x : valued.space) (hx : x ∈ U),
      (valued.valuation x).vle
        (valued.space.presheaf.germ U x hx (rationalSections D U h a)) 1
  rational_basis : ∀ (U : Opens valued.space) (x : valued.space), x ∈ U →
    ∃ D : RationalTateModel p P, point x ∈ D.domain ∧
      point ⁻¹' (D.domain : Set P.Space) ⊆ (U : Set valued.space)

/-- The section topologies of an affinoid model make its restriction maps continuous. -/
theorem AffinoidModel.continuous_restrict {P : TatePair p} (M : AffinoidModel p P)
    {U V : Opens M.valued.space} (h : V ≤ U) :
    @Continuous _ _ (M.valued.sectionTopology U) (M.valued.sectionTopology V)
      (M.valued.space.presheaf.map (homOfLE h).op).hom := by
  rw [M.sectionTopology_eq V]
  refine continuous_iInf_rng.2 fun D ↦ continuous_iInf_rng.2 fun W ↦
    continuous_iInf_rng.2 fun hW ↦ continuous_iInf_rng.2 fun hD ↦ ?_
  apply continuous_induced_rng.2
  have hc : (M.valued.space.presheaf.map (homOfLE hW).op).hom ∘
      (M.valued.space.presheaf.map (homOfLE h).op).hom =
        (M.valued.space.presheaf.map (homOfLE (hW.trans h)).op).hom := by
    funext x
    change (M.valued.space.presheaf.map (homOfLE h).op ≫
      M.valued.space.presheaf.map (homOfLE hW).op).hom x = _
    rw [← Functor.map_comp]
    rfl
  rw [hc, M.sectionTopology_eq U]
  exact continuous_iInf_dom (i := D) (continuous_iInf_dom (i := W)
    (continuous_iInf_dom (i := hW.trans h) (continuous_iInf_dom (i := hD) continuous_induced_dom)))

/-- Global analytic adic objects are locally these actual valued rational models, as topologically
ringed valued spaces: each chart identifies the topological section rings of opens inside its
image, and the topology on the sections over any open is the initial topology for the restrictions
to the opens inside chart images. -/
def HasAnalyticAtlas (X : ValuedSpace) : Prop :=
  ∃ (I : Type 1) (P : I → TatePair p) (M : ∀ i, AffinoidModel p (P i))
    (f : ∀ i, (M i).valued ⟶ X),
    (∀ i, IsOpenEmbedding (f i).val.base) ∧
    (∀ i x, IsIso ((f i).val.stalkMap x)) ∧
    (∀ i, SectionsHomeomorphic (f i).val) ∧
    (∀ U : Opens X.space, X.sectionTopology U =
      ⨅ (V : Opens X.space) (h : V ≤ U)
        (_ : ∃ i, (V : Set X.space) ⊆ Set.range (f i).val.base),
        (X.sectionTopology V).induced (X.space.presheaf.map (homOfLE h).op).hom) ∧
    (∀ x : X.space, ∃ i, x ∈ Set.range (f i).val.base)

/-- The actual category of analytic Tate-adic models over the p-adic base. -/
abbrev AnalyticAdicSpace :=
  (show ObjectProperty ValuedSpace from HasAnalyticAtlas p).FullSubcategory

variable [Fact p.Prime]

/-- Completed local affine realization, fixed on every coordinate and Spa point. -/
structure AffineRealization where
  model : ∀ P : AffineUntilting p, AffinoidModel p (TatePair.ofPerfectoid p P.pair)
  map : ∀ {P Q : AffineUntilting p} (_f : P ⟶ Q), (model P).valued ⟶ (model Q).valued
  points : ∀ {P Q : AffineUntilting p} (f : P ⟶ Q) (x : (model P).valued.space),
    (model Q).point ((map f).val.base x) = f.original.spa ((model P).point x)
  coordinates : ∀ {P Q : AffineUntilting p} (f : P ⟶ Q) (a : Q.pair.ring),
    ((map f).val.c.app (op ⊤)) ((model Q).globalRing a) =
      (model P).globalRing (f.original.hom a)
  identity : ∀ P, map (𝟙 P) = 𝟙 (model P).valued
  composition : ∀ {P Q R : AffineUntilting p} (f : P ⟶ Q) (g : Q ⟶ R),
    map (f ≫ g) = map f ≫ map g

end MathlibExt.AlgebraicGeometry.AnalyticTateAdicModels
