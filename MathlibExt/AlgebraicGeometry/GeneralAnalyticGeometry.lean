/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PolynomialAnalyticSpaces
public import MathlibExt.AlgebraicGeometry.AnalyticRealization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Minimal general algebraic-to-analytic contracts

The carrier is X(C) with its existing topology. Local analytic rings are
the actual polynomial holomorphic quotients, with all defining equations
retained. Open ringed charts and their commutative algebraic squares fix
the structure sheaf, including singular local models.

The module pullback and its adjunction are constructed from that actual
ringed map. Coherence, exactness and GAGA are separate dependency contracts
on these fixed maps. Paper tasks can bind the contracts while contributors
prove their providers; no manifold or completed theory is required here.

References: Serre, GAGA, https://doi.org/10.5802/aif.59; SGA1, Expose XII.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.GeneralAnalyticGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open ComplexAnalytification
open PolynomialAnalyticSpaces

open MathlibExt.AlgebraicGeometry.AnalyticRealization (ComplexScheme)

def sheafRingedSpace (X : ComplexScheme)
    (O : TopCat.Sheaf CommRingCat (space X)) : RingedSpace where
  carrier := space X
  presheaf := O.obj
  IsSheaf := O.property

def ringedMapOf (X : ComplexScheme) (O : TopCat.Sheaf CommRingCat (space X))
    (r : X.left.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat (AnalyticRealization.pointMap X)).obj O.obj) :
    sheafRingedSpace X O ⟶ X.left.toRingedSpace :=
  InducedCategory.homMk { base := AnalyticRealization.pointMap X, c := r }

/-- The actual local analytic quotient maps to its algebraic affine scheme.
The polynomial normalization includes nilpotent equations, not only values
in the residue field. Locality excludes unrelated sheaf-ring maps. -/
structure AffineAnalyticMap (n : ℕ) (I : Ideal (PolynomialRing n)) where
  map : PolynomialAnalyticSpaces.ringedSpace n I ⟶ (affine n I).left.toRingedSpace
  point_normalization : ∀ p : zeroSet n I,
    map.hom.base p = ComplexPoints.schemePoint (point n I p)
  localRing : ∀ p : zeroSet n I,
    IsLocalRing (_root_.TopCat.Presheaf.stalk (C := CommRingCat)
      (structureSheaf n I).obj p)
  stalk_local : ∀ p : zeroSet n I,
    letI := localRing p
    IsLocalHom (map.hom.stalkMap p).hom
  polynomial_normalization : ∀ f : PolynomialRing n,
    (map.hom.c.app (op ⊤)).hom
      ((Scheme.ΓSpecIso (.of (PolynomialRing n ⧸ I))).inv.hom
        (Ideal.Quotient.mk I f)) = polynomialMap n I f

/-- Analytic realization is characterized on actual open affine presentations.
The charts cover every complex point and are isomorphisms on stalks. -/
structure AnalyticSpace (X : ComplexScheme) where
  structureSheaf : TopCat.Sheaf CommRingCat (space X)
  regularMap : X.left.presheaf ⟶
    (TopCat.Presheaf.pushforward CommRingCat (AnalyticRealization.pointMap X)).obj
      structureSheaf.obj
  localRing : ∀ p : space X,
    IsLocalRing (_root_.TopCat.Presheaf.stalk (C := CommRingCat) structureSheaf.obj p)
  stalk_local : ∀ p : space X,
    letI := localRing p
    IsLocalHom ((ringedMapOf X structureSheaf regularMap).hom.stalkMap p).hom
  charts : ∀ p : space X,
    ∃ (n : ℕ) (I : Ideal (PolynomialRing n)) (A : AffineAnalyticMap n I)
      (i : affine n I ⟶ X)
      (c : PolynomialAnalyticSpaces.ringedSpace n I ⟶
        sheafRingedSpace X structureSheaf),
      IsOpenImmersion i.left ∧ IsOpenEmbedding c.hom.base ∧
      (∀ q, IsIso (c.hom.stalkMap q)) ∧
      p ∈ Set.range c.hom.base ∧
      c ≫ ringedMapOf X structureSheaf regularMap = A.map ≫ i.left.toLRSHom.toShHom

namespace AnalyticSpace

variable {X Y : ComplexScheme}

abbrev ringed (A : AnalyticSpace X) : RingedSpace :=
  sheafRingedSpace X A.structureSheaf

def algebraic (A : AnalyticSpace X) : A.ringed ⟶ X.left.toRingedSpace :=
  ringedMapOf X A.structureSheaf A.regularMap

abbrev ringSheaf (A : AnalyticSpace X) : TopCat.Sheaf RingCat (space X) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat)).obj A.structureSheaf

abbrev Modules (A : AnalyticSpace X) := SheafOfModules.{0} A.ringSheaf

def ringMap (A : AnalyticSpace X) : X.left.ringCatSheaf ⟶
    ((Opens.map (AnalyticRealization.pointMap X)).sheafPushforwardContinuous _ _ _).obj
      A.ringSheaf where
  hom := Functor.whiskerRight A.regularMap (forget₂ CommRingCat RingCat)

instance presheafRightAdjoint (A : AnalyticSpace X) :
    (PresheafOfModules.pushforward.{0}
      (F := Opens.map (AnalyticRealization.pointMap X)) A.ringMap.hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top A.ringMap.hom)

instance sheafRightAdjoint (A : AnalyticSpace X) :
    (SheafOfModules.pushforward.{0}
      (F := Opens.map (AnalyticRealization.pointMap X)) A.ringMap).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{0} A.ringMap).isRightAdjoint

def pullback (A : AnalyticSpace X) : X.left.Modules ⥤ A.Modules :=
  SheafOfModules.pullback.{0} (F := Opens.map (AnalyticRealization.pointMap X)) A.ringMap

def pushforward (A : AnalyticSpace X) : A.Modules ⥤ X.left.Modules :=
  SheafOfModules.pushforward.{0} (F := Opens.map (AnalyticRealization.pointMap X)) A.ringMap

def adjunction (A : AnalyticSpace X) : A.pullback ⊣ A.pushforward :=
  SheafOfModules.pullbackPushforwardAdjunction.{0} A.ringMap

/-- A scheme map lifts to an actual local analytic ringed map, in the
canonical regular-function square. -/
structure Morphism (A : AnalyticSpace X) (B : AnalyticSpace Y) (f : X ⟶ Y) where
  map : A.ringed ⟶ B.ringed
  square : map ≫ B.algebraic = A.algebraic ≫ f.left.toLRSHom.toShHom
  point_map : map.hom.base = spaceMap f
  stalk_local : ∀ p : space X,
    letI := A.localRing p
    letI := B.localRing (map.hom.base p)
    IsLocalHom (map.hom.stalkMap p).hom

/-- Coherent module categories are the native finite-presentation full
subcategories on the actual algebraic and analytic structure sheaves. -/
abbrev AlgebraicCoherent (X : ComplexScheme) :=
  (SheafOfModules.isFinitePresentation X.left.ringCatSheaf).FullSubcategory

abbrev Coherent (A : AnalyticSpace X) :=
  (SheafOfModules.isFinitePresentation A.ringSheaf).FullSubcategory

/-- Minimal coherence/exactness dependency on the constructed pullback. -/
structure CoherentPullback (A : AnalyticSpace X) : Prop where
  preserves : ∀ F : X.left.Modules, F.IsFinitePresentation →
    (A.pullback.obj F).IsFinitePresentation
  exact : PreservesFiniteLimits A.pullback

def coherentFunctor (A : AnalyticSpace X) (h : A.CoherentPullback) :
    AlgebraicCoherent X ⥤ A.Coherent where
  obj F := ⟨A.pullback.obj F.obj, h.preserves F.obj F.property⟩
  map f := ObjectProperty.homMk (A.pullback.map f.hom)
  map_id F := by apply ObjectProperty.hom_ext; exact A.pullback.map_id F.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact A.pullback.map_comp f.hom g.hom

/-- The conclusions of GAGA for an analytic space structure `A` on the complex points of a scheme
$X$ over $\mathbb{C}$, stated for the pullback of sheaves of modules along its comparison map to
$X$: the pullback preserves finitely presented modules and finite limits (`CoherentPullback`); it
is bijective on morphisms between finitely presented sheaves of modules on $X$; and every finitely
presented sheaf of modules on the analytic space is isomorphic to the pullback of a finitely
presented sheaf of modules on $X$. -/
structure GAGA (A : AnalyticSpace X) : Prop where
  coherent : A.CoherentPullback
  fullyFaithful : ∀ (F G : X.left.Modules), F.IsFinitePresentation →
    G.IsFinitePresentation → Function.Bijective (A.pullback.map (X := F) (Y := G))
  essential : ∀ G : A.Modules, G.IsFinitePresentation →
    ∃ F : X.left.Modules, F.IsFinitePresentation ∧ Nonempty (A.pullback.obj F ≅ G)

end AnalyticSpace

end MathlibExt.AlgebraicGeometry.GeneralAnalyticGeometry
