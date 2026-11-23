/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import MathlibExt.AlgebraicGeometry.AffinePerfectoidVSite

/-!
# Source-normalized rational and pro-etale affine perfectoid models

Rational algebras are characterized by the universal extension of actual
continuous plus-preserving ring maps with the prescribed fractions in
the plus ring. Their point map is the actual all-rank Spa map, with range
the stated rational domain. They are not free affinoid labels.

An affine pro-etale model has an actual cofiltered diagram of etale
models, its fixed projections, the canonical topological limit and the
complete-ring universal property. Local models use rational charts.
The completed Tau localization/gluing proofs are available source inputs;
this file defines their canonical adapter contracts.

References: Scholze, arXiv:1709.07343v4, Definitions 6.2 and 8.1;
Wedhorn, arXiv:1910.05934v1, §7; TauCetiProject/TauCeti revision
`62bbc0596dc3539d488232e4e924a338548ea0a9`,
`TauCeti/AlgebraicGeometry/AdicSpace/Spa/Localization/PresentationIndependence.lean`
and `TauCeti/RingTheory/Affinoid/Subdomain/Rational/Basic.lean`
(Apache 2.0). No new generic localization or gluing theorem is asserted.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PerfectoidLocalModels

open CategoryTheory TopologicalSpace Topology
open MathlibExt.RingTheory.CompleteHuberPairModels
open AffinePerfectoidVSite

variable (p : ℕ) [Fact p.Prime]

/-- The prescribed rational subset, on actual all-rank valuation points. -/
def rationalSet (P : Affine p) (T : Finset P.ring) (s : P.ring) :
    Set (Space p P) :=
  {v | ¬ v.1.relation.vle s 0 ∧ ∀ t ∈ T, v.1.relation.vle t s}

/-- The exact rational fraction condition for a continuous pair map. -/
def FractionCondition {P : Affine p} (T : Finset P.ring) (s : P.ring)
    (C : HuberPair) (f : RingMap P.toHuberPair C) : Prop :=
  ∃ u : C.ringˣ, (u : C.ring) = f.hom s ∧
    ∀ t ∈ T, f.hom t * ((u⁻¹ : C.ringˣ) : C.ring) ∈ C.plus

/-- A genuine rational-localization model with its defining universal map. -/
structure RationalModel (P : Affine p) where
  numerators : Finset P.ring
  denominator : P.ring
  open_ideal : IsOpen (Ideal.span (numerators : Set P.ring) : Set P.ring)
  affine : Affine p
  map : RingMap P.toHuberPair affine.toHuberPair
  fractions : FractionCondition p numerators denominator affine.toHuberPair map
  universal : ∀ (C : HuberPair) (f : RingMap P.toHuberPair C),
    FractionCondition p numerators denominator C f →
    ∃! g : RingMap affine.toHuberPair C, g.hom.comp map.hom = f.hom
  embedding : IsOpenEmbedding map.spa
  range : Set.range map.spa = rationalSet p P numerators denominator

/-- Actual finite etaleness of a map of Huber pairs (Scholze, *Étale cohomology of diamonds*,
Def. 6.2(i)): the ring map is finite étale and the target plus ring is the integral closure of the
image of the source plus ring. Changing only the plus ring is not finite étale. -/
def IsFiniteEtale {P Q : HuberPair} (f : RingMap P Q) : Prop :=
  letI := f.hom.toAlgebra
  Module.Finite P.ring Q.ring ∧ Algebra.Etale P.ring Q.ring ∧
    ∀ s : Q.ring, s ∈ Q.plus ↔ (f.hom.comp P.plus.subtype).IsIntegralElem s

/-- An étale chart around the specified point (Scholze, Def. 6.2(ii): locally an open embedding
followed by a finite étale map): a rational neighbourhood of the point is identified with a
rational open of a finite étale cover of a rational neighbourhood of its image. -/
structure EtaleChart {P Q : Affine p} (f : P ⟶ Q) (x : Space p P) where
  source : RationalModel p P
  point : x ∈ Set.range source.map.spa
  target : RationalModel p Q
  cover : Affine p
  coverMap : RingMap target.affine.toHuberPair cover.toHuberPair
  finite_etale : IsFiniteEtale coverMap
  opening : RationalModel p cover
  identification : source.affine ≅ opening.affine
  square : source.map.hom.comp f.hom =
    identification.hom.hom.comp (opening.map.hom.comp (coverMap.hom.comp target.map.hom))

/-- Etaleness is local: around every point there is an étale chart. -/
def IsEtale {P Q : Affine p} (f : P ⟶ Q) : Prop :=
  ∀ x : Space p P, Nonempty (EtaleChart p f x)

/-- The compatible point families of an actual affine diagram. -/
def CompatiblePoints {I : Type} [SmallCategory I] (D : I ⥤ Affine p) :=
  {x : ∀ i, Space p (D.obj i) |
    ∀ {i j} (h : i ⟶ j), spaceMap p (D.map h) (x i) = x j}

/-- A global affine pro-etale presentation, with fixed topological and
complete-ring limit maps rather than an opaque pro-etale predicate. -/
structure ProEtalePresentation {P Q : Affine p} (f : P ⟶ Q) where
  index : Type
  [category : SmallCategory index]
  [cofiltered : IsCofiltered index]
  diagram : index ⥤ Affine p
  base : diagram ⟶ (Functor.const index).obj Q
  etale : ∀ i, IsEtale p (base.app i)
  projection : (Functor.const index).obj P ⟶ diagram
  base_square : ∀ i, projection.app i ≫ base.app i = f
  points : Space p P ≃ₜ CompatiblePoints p diagram
  points_projection : ∀ (x : Space p P) i,
    (points x).val i = spaceMap p (projection.app i) x
  ring_universal : ∀ (C : HuberPair)
    (g : ∀ i, RingMap (diagram.obj i).toHuberPair C),
    (∀ {i j} (h : i ⟶ j), (g i).hom.comp (diagram.map h).hom = (g j).hom) →
    ∃! k : RingMap P.toHuberPair C,
      ∀ i, k.hom.comp (projection.app i).hom = (g i).hom

/-- The local source/target rational presentation of a pro-etale map. -/
structure ProEtaleChart {P Q : Affine p} (f : P ⟶ Q) (x : Space p P) where
  source : RationalModel p P
  point : x ∈ Set.range source.map.spa
  target : RationalModel p Q
  map : source.affine ⟶ target.affine
  square : source.map.hom.comp f.hom = map.hom.comp target.map.hom
  presentation : ProEtalePresentation p map

def IsProEtale {P Q : Affine p} (f : P ⟶ Q) : Prop :=
  ∀ x : Space p P, Nonempty (ProEtaleChart p f x)

/-- The pro-etale topology is generated by actual local-model v-covers. -/
def proEtaleTopology : GrothendieckTopology (Affine p) :=
  sInf {J | ∀ (ι : Type 1) (P : Affine p) (U : ι → Affine p)
    (f : ∀ i, U i ⟶ P), (∀ i, IsProEtale p (f i)) →
      IsVCover p P U f → Sieve.ofArrows U f ∈ J P}

end MathlibExt.AlgebraicGeometry.PerfectoidLocalModels
