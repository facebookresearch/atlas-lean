/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SemistableFormalAtlas
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Global semistable strata and the normalized skeletal retraction

Generic charts and reductions are fixed on every actual model section.
Overlaps use actual section restriction and complete model-ring maps, and
their generic seminorms agree on every model element. The global strata are
the actual irreducible components of the specified locally closed residue
strata. The skeleton is the union of the actual chart Shilov points.

Retraction and strong-deformation records contain the requested conclusions;
none of them is assumed by the model or generic/reduction atlas.

Reference: Gubler--Rabinoff--Werner, 1404.7044v3, sections 3--4, Theorem 4.13.
The generic/reduction/gluing dictionaries are ordinary source integration
from formal/Berkovich/adic geometry, including the positively credited
TauCeti adic gluing at 62bbc0596dc3539d488232e4e924a338548ea0a9, Apache 2.0.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GlobalSemistableSkeleton

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry TopologicalSpace
open SemistableFormalAtlas BerkovichAnalytification
open scoped BigOperators

variable {K : Type} [NormedField K] [IsUltrametricDist K] (P : StrictPair K)

abbrev AnalyticPoint := BerkovichAnalytification.Point K P.generic

def complementOpen : P.generic.left.Opens :=
  ⨅ i : Fin P.boundarySize,
    ⟨genericToModel P ⁻¹' (Set.range (P.boundaryInclusion i).left)ᶜ,
      ((P.boundaryInclusion i).left.isClosedEmbedding.isClosed_range.isOpen_compl).preimage
        (genericToModel P).continuous⟩

def complementScheme : Over (Spec (CommRingCat.of K)) :=
  Over.mk ((complementOpen P).ι ≫ P.generic.hom)

def complementInclusion : complementScheme P ⟶ P.generic :=
  Over.homMk (complementOpen P).ι

structure ChartComparison (C : StandardEtaleChart K P.model) where
  map : C.model.GenericPoint → AnalyticPoint P
  continuous : Continuous map
  lands : ∀ q, genericToModel P (map q).schemePoint ∈ C.openSet.val
  evaluations : ∀ (q : C.model.GenericPoint) (s : Γ(P.model.left, C.openSet.val)),
    (map q).eval ((genericToModel P).app C.openSet.val s) (lands q) =
      q.val.seminorm (algebraMap C.model.modelRing C.model.genericAlgebra (completedSection C s))
  injective : Function.Injective map
  reduction : SemistableFormalAtlas.Reduction C
  specialMap : Spec (CommRingCat.of (SemistableFormalAtlas.SpecialRing C)) ⟶
    SemistableFormalAtlas.specialFibre P
  special_lands : ∀ z,
    SemistableFormalAtlas.specialToModel P (specialMap z) ∈ C.openSet.val
  special_coefficients : ∀ s : Γ(P.model.left, C.openSet.val),
    (Scheme.ΓSpecIso (CommRingCat.of (SemistableFormalAtlas.SpecialRing C))).hom
      (((specialMap ≫ SemistableFormalAtlas.specialToModel P).appLE C.openSet.val ⊤
        (by intro z _hz; exact special_lands z)).hom s) =
      Ideal.Quotient.mk (SemistableFormalAtlas.specialIdeal C) (completedSection C s)

structure FormalOverlap {i j : Fin P.atlasSize} (L : ChartComparison P (P.chart i))
    (R : ChartComparison P (P.chart j)) where
  chart : StandardEtaleChart K P.model
  leftLE : chart.openSet.val ≤ (P.chart i).openSet.val
  rightLE : chart.openSet.val ≤ (P.chart j).openSet.val
  leftRing : (P.chart i).model.modelRing →+* chart.model.modelRing
  rightRing : (P.chart j).model.modelRing →+* chart.model.modelRing
  leftSections : ∀ s : Γ(P.model.left, (P.chart i).openSet.val),
    leftRing (completedSection (P.chart i) s) = completedSection chart
      ((P.model.left.presheaf.map (homOfLE leftLE).op).hom s)
  rightSections : ∀ s : Γ(P.model.left, (P.chart j).openSet.val),
    rightRing (completedSection (P.chart j) s) = completedSection chart
      ((P.model.left.presheaf.map (homOfLE rightLE).op).hom s)
  leftGeneric : chart.model.GenericPoint → (P.chart i).model.GenericPoint
  rightGeneric : chart.model.GenericPoint → (P.chart j).model.GenericPoint
  leftNorm : ∀ (q : chart.model.GenericPoint) (a : (P.chart i).model.modelRing),
    (leftGeneric q).val.seminorm (algebraMap _ _ a) =
      q.val.seminorm (algebraMap _ _ (leftRing a))
  rightNorm : ∀ (q : chart.model.GenericPoint) (a : (P.chart j).model.modelRing),
    (rightGeneric q).val.seminorm (algebraMap _ _ a) =
      q.val.seminorm (algebraMap _ _ (rightRing a))
  agreement : ∀ q, L.map (leftGeneric q) = R.map (rightGeneric q)

def horizontalLocus (j : Fin P.boundarySize) : Set (SemistableFormalAtlas.specialFibre P) :=
  {x | SemistableFormalAtlas.specialToModel P x ∈ Set.range (P.boundaryInclusion j).left}

def stratumLocus
    (I : Finset (irreducibleComponents (SemistableFormalAtlas.specialFibre P)))
    (J : Finset (Fin P.boundarySize)) : Set (SemistableFormalAtlas.specialFibre P) :=
  {x | (∀ Z : irreducibleComponents (SemistableFormalAtlas.specialFibre P), x ∈ Z.val ↔ Z ∈ I) ∧
    ∀ j : Fin P.boundarySize, x ∈ horizontalLocus P j ↔ j ∈ J}

/-- Indices are actual global residue strata, independent of a chart cover. The generic point is
taken in the locally closed stratum locus, with the subspace topology: a stratum need not be
closed in the special fibre. -/
structure GlobalStratum where
  vertical : Finset (irreducibleComponents (SemistableFormalAtlas.specialFibre P))
  horizontal : Finset (Fin P.boundarySize)
  component : irreducibleComponents (stratumLocus P vertical horizontal)
  genericPoint : stratumLocus P vertical horizontal
  generic : IsGenericPoint genericPoint component.val

structure GlobalAtlas where
  chart : ∀ i : Fin P.atlasSize, ChartComparison P (P.chart i)
  covers : ∀ p : AnalyticPoint P, ∃ i q, (chart i).map q = p
  overlap : ∀ (i j : Fin P.atlasSize) (q : (P.chart i).model.GenericPoint)
      (r : (P.chart j).model.GenericPoint), (chart i).map q = (chart j).map r →
    ∃ C : FormalOverlap P (chart i) (chart j),
      ∃ s : C.chart.model.GenericPoint, C.leftGeneric s = q ∧ C.rightGeneric s = r
  reduction : AnalyticPoint P → SemistableFormalAtlas.specialFibre P
  reduction_normalized : ∀ i q,
    reduction ((chart i).map q) = (chart i).specialMap ((chart i).reduction.map q)
  [specialNoetherian : IsNoetherian (SemistableFormalAtlas.specialFibre P)]
  [strataFinite : Finite (GlobalStratum P)]
  domainLift : ∀ p : AnalyticPoint P, p.schemePoint ∈ complementOpen P →
      BerkovichAnalytification.Point K (complementScheme P)
  domainLift_normalized : ∀ (p : AnalyticPoint P) (h : p.schemePoint ∈ complementOpen P),
    BerkovichAnalytification.mapPoint (complementInclusion P) (domainLift p h) = p

variable (A : GlobalAtlas P)

def skeleton : Set (AnalyticPoint P) :=
  {p | ∃ (i : Fin P.atlasSize) (q : (P.chart i).model.GenericPoint), (A.chart i).map q = p ∧
    q ∈ SemistableFormalAtlas.localSkeleton (P.chart i) (A.chart i).reduction}

def stratumCell (S : GlobalStratum P) : Set (AnalyticPoint P) :=
  closure {p | p ∈ skeleton P A ∧ A.reduction p = S.genericPoint.val}

structure GlobalRetraction where
  map : AnalyticPoint P → AnalyticPoint P
  continuous : Continuous map
  chart_covers : ∀ (i : Fin P.atlasSize) (q : (P.chart i).model.GenericPoint),
    ∃ S : SemistableFormalAtlas.Stratum (P.chart i), (A.chart i).reduction.map q ∈ S.component
  normalized : ∀ (i : Fin P.atlasSize) (q : (P.chart i).model.GenericPoint)
      (S : SemistableFormalAtlas.Stratum (P.chart i)),
    (A.chart i).reduction.map q ∈ S.component →
      ∃ r : (P.chart i).model.GenericPoint, (A.chart i).map r = map ((A.chart i).map q) ∧
        IsGaussPoint (P.chart i) (A.chart i).reduction S q r
  image : Set.range map = skeleton P A
  fixes : ∀ p ∈ skeleton P A, map p = p
  preserves_complement : ∀ p, p.schemePoint ∈ complementOpen P →
    (map p).schemePoint ∈ complementOpen P
  horizontal_strata : ∀ (i : Fin P.boundarySize) (p : AnalyticPoint P),
    genericToModel P (map p).schemePoint ∈ Set.range (P.boundaryInclusion i).left ↔
      genericToModel P p.schemePoint ∈ Set.range (P.boundaryInclusion i).left
  proper : IsProperMap map

structure StrongDeformation (R : GlobalRetraction P A) where
  map : unitInterval × AnalyticPoint P → AnalyticPoint P
  continuous : Continuous map
  start : ∀ p, map (0, p) = p
  finish : ∀ p, map (1, p) = R.map p
  fixes : ∀ t p, p ∈ skeleton P A → map (t, p) = p
  preserves_complement : ∀ t p, p.schemePoint ∈ complementOpen P →
    (map (t, p)).schemePoint ∈ complementOpen P
  horizontal_strata : ∀ (i : Fin P.boundarySize) t (p : AnalyticPoint P),
    genericToModel P (map (t, p)).schemePoint ∈ Set.range (P.boundaryInclusion i).left ↔
      genericToModel P p.schemePoint ∈ Set.range (P.boundaryInclusion i).left
  proper : IsProperMap map

end MathlibExt.AlgebraicGeometry.GlobalSemistableSkeleton
