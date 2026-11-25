/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Sites.InducedTopology
public import MathlibExt.AlgebraicGeometry.PerfectoidRationalTilting

/-!
# Actual original and tilted etale/pro-etale sites

Etaleness of original maps is tested on their actual original rings
after actual rational localization. Pro-etale presentations retain
the cofiltered diagram, all original point maps and the universal
complete-ring map. These properties are defined before tilting.

The induced site functors retain the actual tilt of every map. Their
construction needs preservation of the corresponding local property;
equivalence and sheaf-unit/counit comparisons remain separate results.

Sources: Scholze, arXiv:1111.4914v1, Theorems 1.10--1.11 and 7.12;
arXiv:1709.07343v4, Definitions 7.1 and 8.1.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.PerfectoidUntiltingSites

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MathlibExt.RingTheory.CompleteHuberPairModels
open AffineUntiltingGeometry PerfectoidRationalTilting

variable (p : ℕ) [Fact p.Prime]

/-- Actual finite etaleness of the original map of pairs (Scholze, *Étale cohomology of diamonds*,
Def. 6.2(i)): the coefficient map is finite étale, and the plus ring of the source is the integral
closure of the image of the plus ring of the target. Changing only the plus ring is not finite
étale. -/
def IsFiniteEtale {P Q : AffineUntilting p} (f : P ⟶ Q) : Prop :=
  letI := f.original.hom.toAlgebra
  Module.Finite Q.pair.ring P.pair.ring ∧ Algebra.Etale Q.pair.ring P.pair.ring ∧
    ∀ s : P.pair.ring,
      s ∈ P.pair.plus ↔ (f.original.hom.comp Q.pair.plus.subtype).IsIntegralElem s

/-- Actual rational charts exhibiting etaleness at a specified original point (Scholze, Def.
6.2(ii): locally an open embedding followed by a finite étale map): a rational neighbourhood of the
point is identified with a rational open of a finite étale cover of a rational neighbourhood of
its image. -/
structure EtaleChart {P Q : AffineUntilting p} (f : P ⟶ Q)
    (x : P.pair.toHuberPair.Space) where
  source : OriginalRationalModel p P
  point : x ∈ Set.range source.map.original.spa
  target : OriginalRationalModel p Q
  cover : AffineUntilting p
  coverMap : cover ⟶ target.affine
  finite_etale : IsFiniteEtale p coverMap
  opening : OriginalRationalModel p cover
  identification : source.affine ≅ opening.affine
  square : source.map ≫ f = identification.hom ≫ opening.map ≫ coverMap ≫ target.map

/-- Original etaleness is a local property of the actual original rings. -/
def IsEtale {P Q : AffineUntilting p} (f : P ⟶ Q) : Prop :=
  ∀ x : P.pair.toHuberPair.Space, Nonempty (EtaleChart p f x)

/-- The actual compatible point families of a cofiltered original diagram. -/
def CompatiblePoints {I : Type} [SmallCategory I] (D : I ⥤ AffineUntilting p) :=
  {x : ∀ i, (D.obj i).pair.toHuberPair.Space |
    ∀ {i j} (f : i ⟶ j), (D.map f).original.spa (x i) = x j}

/-- A pro-etale presentation uses genuine complete-ring and all-rank point limits. -/
structure ProEtalePresentation {P Q : AffineUntilting p} (f : P ⟶ Q) where
  index : Type
  [category : SmallCategory index]
  [cofiltered : IsCofiltered index]
  diagram : index ⥤ AffineUntilting p
  base : diagram ⟶ (Functor.const index).obj Q
  etale : ∀ i, IsEtale p (base.app i)
  cone : (Functor.const index).obj P ⟶ diagram
  triangle : ∀ i, cone.app i ≫ base.app i = f
  point : P.pair.toHuberPair.Space ≃ₜ CompatiblePoints p diagram
  point_normalized : ∀ x i, (point x).val i = (cone.app i).original.spa x
  ring_universal : ∀ (C : HuberPair)
    (g : ∀ i, RingMap (diagram.obj i).pair.toHuberPair C),
    (∀ {i j} (h : i ⟶ j), (g i).hom.comp (diagram.map h).original.hom = (g j).hom) →
    ∃! h : RingMap P.pair.toHuberPair C,
      ∀ i, h.hom.comp (cone.app i).original.hom = (g i).hom

/-- A local original pro-etale chart with its actual limiting map. -/
structure ProEtaleChart {P Q : AffineUntilting p} (f : P ⟶ Q)
    (x : P.pair.toHuberPair.Space) where
  source : OriginalRationalModel p P
  point : x ∈ Set.range source.map.original.spa
  target : OriginalRationalModel p Q
  map : source.affine ⟶ target.affine
  square : source.map ≫ f = map ≫ target.map
  presentation : ProEtalePresentation p map

/-- Original pro-etaleness is checked at every actual original point. -/
def IsProEtale {P Q : AffineUntilting p} (f : P ⟶ Q) : Prop :=
  ∀ x : P.pair.toHuberPair.Space, Nonempty (ProEtaleChart p f x)

/-- The actual original etale covering topology. -/
def etaleTopology : GrothendieckTopology (AffineUntilting p) :=
  sInf {J | ∀ (I : Type 1) (P : AffineUntilting p)
    (U : I → AffineUntilting p) (f : ∀ i, U i ⟶ P),
    (∀ i, IsEtale p (f i)) → IsOriginalVCover p P U f → Sieve.ofArrows U f ∈ J P}

/-- The actual original pro-etale covering topology. -/
def proEtaleTopology : GrothendieckTopology (AffineUntilting p) :=
  sInf {J | ∀ (I : Type 1) (P : AffineUntilting p)
    (U : I → AffineUntilting p) (f : ∀ i, U i ⟶ P),
    (∀ i, IsProEtale p (f i)) → IsOriginalVCover p P U f → Sieve.ofArrows U f ∈ J P}

/-- The actual original small etale objects over the fixed affine. -/
abbrev EtaleSite (K : AffineUntilting p) :=
  (show ObjectProperty (Over K) from fun T ↦ IsEtale p T.hom).FullSubcategory

/-- The actual original small pro-etale objects over the fixed affine. -/
abbrev ProEtaleSite (K : AffineUntilting p) :=
  (show ObjectProperty (Over K) from fun T ↦ IsProEtale p T.hom).FullSubcategory

/-- Actual etale objects on the characteristic-p side. -/
abbrev TiltEtaleSite (K : AffineUntilting p) :=
  (show ObjectProperty (Over K.tilt.pair) from
    fun T ↦ PerfectoidLocalModels.IsEtale p T.hom).FullSubcategory

/-- Actual pro-etale objects on the characteristic-p side. -/
abbrev TiltProEtaleSite (K : AffineUntilting p) :=
  (show ObjectProperty (Over K.tilt.pair) from
    fun T ↦ PerfectoidLocalModels.IsProEtale p T.hom).FullSubcategory

/-- Etale preservation is a result about the fixed actual tilting maps. -/
def PreservesEtale : Prop :=
  ∀ {P Q : AffineUntilting p} (f : P ⟶ Q),
    IsEtale p f → PerfectoidLocalModels.IsEtale p f.tilted

/-- Pro-etale preservation is a result about the fixed actual tilting maps. -/
def PreservesProEtale : Prop :=
  ∀ {P Q : AffineUntilting p} (f : P ⟶ Q),
    IsProEtale p f → PerfectoidLocalModels.IsProEtale p f.tilted

/-- The actual induced etale site functor. -/
def etaleTilting (K : AffineUntilting p) (h : PreservesEtale p) :
    EtaleSite p K ⥤ TiltEtaleSite p K where
  obj T := ⟨(relativeTilting p K).obj T.obj, h T.obj.hom T.property⟩
  map f := ObjectProperty.homMk ((relativeTilting p K).map f.hom)

/-- The actual induced pro-etale site functor. -/
def proEtaleTilting (K : AffineUntilting p) (h : PreservesProEtale p) :
    ProEtaleSite p K ⥤ TiltProEtaleSite p K where
  obj T := ⟨(relativeTilting p K).obj T.obj, h T.obj.hom T.property⟩
  map f := ObjectProperty.homMk ((relativeTilting p K).map f.hom)

end MathlibExt.AlgebraicGeometry.PerfectoidUntiltingSites
