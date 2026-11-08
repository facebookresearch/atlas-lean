/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bridge between the trusted Conway knot stack and the Euclidean link API

`WantedExt.Topology.ConwayKnotShared` is a trusted, verbatim copy of
lean-eval knot-theory helpers (Apache License, Version 2.0), kept
unchanged apart from its namespace so that the wanted statements
depending on it retain their original meaning. The canonical working
API for parametrized smooth knots and links in this repository is
`MathlibExt.Topology.Knot.EuclideanLink`; MathlibExt cannot import
WantedExt (the layering runs the other way), so the two APIs
deliberately duplicate three structures field-for-field
(`Knot`/`ParametrizedKnot`, `AmbientIsotopy`, and `CircleReparam`).

This module is the interoperation point. It does not modify either
definition: it provides the fieldwise identity conversions in both
directions, packages them as equivalences, and proves that ambient
isotopy transfers across the conversions. A future deduplication can
therefore replace either side by the other mechanically, but only as
a deliberate change to the trusted file's provenance.
-/
module

public import Mathlib.Data.Fin.VecNotation
public import MathlibExt.Topology.Knot.EuclideanLink
public import WantedExt.Topology.ConwayKnotShared

import Mathlib.Tactic.FinCases

@[expose] public section

namespace MathlibExt.Topology.ConwayKnotEuclideanBridge

/-- A trusted lean-eval `Knot` as a canonical `ParametrizedKnot`. The
conversion is the identity on every field. -/
def toParametrizedKnot (K : ConwayKnotShared.KnotTheory.Knot) :
    Knot.Euclidean.ParametrizedKnot where
  curve := K.curve
  smooth := K.smooth
  periodic := K.periodic
  injOn := K.injOn
  immersion := K.immersion

/-- A canonical `ParametrizedKnot` as a trusted lean-eval `Knot`. -/
def ofParametrizedKnot (K : Knot.Euclidean.ParametrizedKnot) :
    ConwayKnotShared.KnotTheory.Knot where
  curve := K.curve
  smooth := K.smooth
  periodic := K.periodic
  injOn := K.injOn
  immersion := K.immersion

@[simp]
theorem ofParametrizedKnot_toParametrizedKnot
    (K : ConwayKnotShared.KnotTheory.Knot) :
    ofParametrizedKnot (toParametrizedKnot K) = K := by
  cases K
  rfl

@[simp]
theorem toParametrizedKnot_ofParametrizedKnot
    (K : Knot.Euclidean.ParametrizedKnot) :
    toParametrizedKnot (ofParametrizedKnot K) = K := by
  cases K
  rfl

/-- The trusted lean-eval knot type is equivalent to the canonical
parametrized-knot type, by the identity on fields. -/
def knotEquiv :
    ConwayKnotShared.KnotTheory.Knot ≃ Knot.Euclidean.ParametrizedKnot where
  toFun := toParametrizedKnot
  invFun := ofParametrizedKnot
  left_inv := ofParametrizedKnot_toParametrizedKnot
  right_inv := toParametrizedKnot_ofParametrizedKnot

/-- A trusted lean-eval ambient isotopy as a canonical one. -/
def toEuclideanAmbientIsotopy
    (Φ : ConwayKnotShared.KnotTheory.AmbientIsotopy) :
    Knot.Euclidean.AmbientIsotopy where
  H := Φ.H
  Hinv := Φ.Hinv
  smooth := Φ.smooth
  smooth_inv := Φ.smooth_inv
  inv_left := Φ.inv_left
  inv_right := Φ.inv_right
  start := Φ.start

/-- A canonical ambient isotopy as a trusted lean-eval one. -/
def ofEuclideanAmbientIsotopy (Φ : Knot.Euclidean.AmbientIsotopy) :
    ConwayKnotShared.KnotTheory.AmbientIsotopy where
  H := Φ.H
  Hinv := Φ.Hinv
  smooth := Φ.smooth
  smooth_inv := Φ.smooth_inv
  inv_left := Φ.inv_left
  inv_right := Φ.inv_right
  start := Φ.start

/-- A trusted lean-eval circle reparametrization as a canonical one. -/
def toEuclideanCircleReparam
    (σ : ConwayKnotShared.KnotTheory.CircleReparam) :
    Knot.Euclidean.CircleReparam where
  f := σ.f
  finv := σ.finv
  smooth := σ.smooth
  smooth_inv := σ.smooth_inv
  left_inv := σ.left_inv
  right_inv := σ.right_inv
  periodic := σ.periodic
  periodic_inv := σ.periodic_inv
  mono := σ.mono

/-- A canonical circle reparametrization as a trusted lean-eval one. -/
def ofEuclideanCircleReparam (σ : Knot.Euclidean.CircleReparam) :
    ConwayKnotShared.KnotTheory.CircleReparam where
  f := σ.f
  finv := σ.finv
  smooth := σ.smooth
  smooth_inv := σ.smooth_inv
  left_inv := σ.left_inv
  right_inv := σ.right_inv
  periodic := σ.periodic
  periodic_inv := σ.periodic_inv
  mono := σ.mono

/-- Ambient isotopy in the trusted lean-eval sense is ambient isotopy
of the converted knots in the canonical sense. -/
theorem knot_isotopic_iff {K₁ K₂ : ConwayKnotShared.KnotTheory.Knot} :
    ConwayKnotShared.KnotTheory.Knot.Isotopic K₁ K₂ ↔
      Knot.Euclidean.ParametrizedKnot.Isotopic
        (toParametrizedKnot K₁) (toParametrizedKnot K₂) := by
  constructor
  · rintro ⟨Φ, σ, h⟩
    exact ⟨toEuclideanAmbientIsotopy Φ, toEuclideanCircleReparam σ, h⟩
  · rintro ⟨Φ, σ, h⟩
    exact ⟨ofEuclideanAmbientIsotopy Φ, ofEuclideanCircleReparam σ, h⟩

/-- A trusted lean-eval two-component link as a canonical labeled
link with two components. Components keep their order and labels:
component `0` is `L.K` and component `1` is `L.L`. -/
def toParametrizedLink (L : ConwayKnotShared.KnotTheory.TwoLink) :
    Knot.Euclidean.ParametrizedLink 2 where
  component := ![toParametrizedKnot L.K, toParametrizedKnot L.L]
  pairwiseDisjoint := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact L.disjoint
    · exact L.disjoint.symm
    · exact absurd rfl hij

/-- A canonical labeled link with two components as a trusted
lean-eval two-component link, reading components `0` and `1`. -/
def ofParametrizedLink (L : Knot.Euclidean.ParametrizedLink 2) :
    ConwayKnotShared.KnotTheory.TwoLink where
  K := ofParametrizedKnot (L.component 0)
  L := ofParametrizedKnot (L.component 1)
  disjoint := by
    have h := L.pairwiseDisjoint (Set.mem_univ 0) (Set.mem_univ 1)
      (by decide : (0 : Fin 2) ≠ 1)
    exact h

@[simp]
theorem ofParametrizedLink_toParametrizedLink
    (L : ConwayKnotShared.KnotTheory.TwoLink) :
    ofParametrizedLink (toParametrizedLink L) = L := by
  cases L
  rfl

/-- Ambient isotopy of trusted two-component links is ambient isotopy
of the converted labeled links. -/
theorem twoLink_isotopic_iff
    {L₁ L₂ : ConwayKnotShared.KnotTheory.TwoLink} :
    ConwayKnotShared.KnotTheory.TwoLink.Isotopic L₁ L₂ ↔
      Knot.Euclidean.ParametrizedLink.Isotopic
        (toParametrizedLink L₁) (toParametrizedLink L₂) := by
  constructor
  · rintro ⟨Φ, σ, τ, hK, hL⟩
    refine ⟨toEuclideanAmbientIsotopy Φ,
      ![toEuclideanCircleReparam σ, toEuclideanCircleReparam τ],
      fun i t => ?_⟩
    fin_cases i
    · exact hK t
    · exact hL t
  · rintro ⟨Φ, σ, h⟩
    refine ⟨ofEuclideanAmbientIsotopy Φ,
      ofEuclideanCircleReparam (σ 0), ofEuclideanCircleReparam (σ 1),
      fun t => ?_, fun t => ?_⟩
    · exact h 0 t
    · exact h 1 t

end MathlibExt.Topology.ConwayKnotEuclideanBridge
