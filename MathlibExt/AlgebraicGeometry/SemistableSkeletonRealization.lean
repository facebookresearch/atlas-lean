/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffinoidFormalModels
public import MathlibExt.AlgebraicGeometry.BerkovichAnalytification
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Homotopy.Basic

/-!
# Strict semistable chart coordinates and actual skeletal Shilov points

The coefficient ring is the actual valuation subring of a complete real-valued
nonarchimedean field; it is not required to be a DVR. Standard formal charts
are adic completions of the actual polynomial relation t0...tr=pi. Reduction
uses the full valuation maximal ideal, not only the principal pi ideal.
Coordinates are actual model-ring elements and their seminorm evaluations.

A skeletal point is the unique point which maximizes every actual affinoid
function on the specified coordinate/reduction fibre. Retraction contracts
are pinned by that characterization. No free polyhedral set or unspecified
map is called a skeleton.

Reference: Gubler--Rabinoff--Werner, 1404.7044v3, Definition3.1, section4
and Proposition4.13. Existing affinoid/formal/adic gluing primitives are
source dependencies; they are not re-requested here.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SemistableSkeletonRealization

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace
open AffinoidFormalModels NonarchimedeanAnalyticSpaces BerkovichAnalytification
open scoped BigOperators

variable (K : Type) [NormedField K] [IsUltrametricDist K]

abbrev Integers := (NormedField.valuation (K := K)).valuationSubring
abbrev Residue := IsLocalRing.ResidueField (Integers K)

def parameterIdeal (pi : Integers K) : Ideal (Integers K) := Ideal.span {pi}

def standardEquation (n r : ℕ) (hr : r + 1 ≤ n) (pi : Integers K) :
    MvPolynomial (Fin n) (Integers K) :=
  (∏ i : Fin (r + 1), MvPolynomial.X ⟨i.val, i.isLt.trans_le hr⟩) - MvPolynomial.C pi

abbrev standardQuotient (n r : ℕ) (hr : r + 1 ≤ n) (pi : Integers K) :=
  MvPolynomial (Fin n) (Integers K) ⧸ Ideal.span {standardEquation K n r hr pi}

abbrev standardCompletion (n r : ℕ) (hr : r + 1 ≤ n) (pi : Integers K) :=
  AdicCompletion ((parameterIdeal K pi).map
    (algebraMap (Integers K) (standardQuotient K n r hr pi)))
      (standardQuotient K n r hr pi)

def standardCoordinate (n r : ℕ) (hr : r + 1 ≤ n) (pi : Integers K) (j : Fin n) :
    standardQuotient K n r hr pi :=
  Ideal.Quotient.mk (Ideal.span {standardEquation K n r hr pi}) (MvPolynomial.X j)

def completedCoordinate (n r : ℕ) (hr : r + 1 ≤ n) (pi : Integers K) (j : Fin n) :
    standardCompletion K n r hr pi :=
  AdicCompletion.of ((parameterIdeal K pi).map
    (algebraMap (Integers K) (standardQuotient K n r hr pi)))
    (standardQuotient K n r hr pi)
    (standardCoordinate K n r hr pi j)

/-- The standard chart keeps its complete actual ring and every coordinate. -/
structure StandardChart (n r s : ℕ) where
  bound : r + 1 + s ≤ n
  relationBound : r + 1 ≤ n
  pi : Integers K
  pi_nonzero : pi ≠ 0
  pi_small : ‖(pi : K)‖ < 1
  model : AffinoidFormalModel (Integers K) K pi
  presentation : standardCompletion K n r relationBound pi ≃ₐ[Integers K] model.modelRing
  coordinate : Fin n → model.modelRing
  coordinate_normalized : ∀ j, coordinate j = presentation
    (completedCoordinate K n r relationBound pi j)

variable {K} {n r s : ℕ} (C : StandardChart K n r s)

def specialIdeal : Ideal C.model.modelRing :=
  (IsLocalRing.maximalIdeal (Integers K)).map (algebraMap (Integers K) C.model.modelRing)

abbrev SpecialRing := C.model.modelRing ⧸ specialIdeal C

def specialFibre : Scheme := Spec (CommRingCat.of (SpecialRing C))

/-- The canonical reduced-special-fibre comparison tests the whole valuation ideal. -/
structure Reduction where
  map : C.model.GenericPoint → PrimeSpectrum (SpecialRing C)
  normalized : ∀ (p : C.model.GenericPoint) (a : C.model.modelRing),
    Ideal.Quotient.mk (specialIdeal C) a ∈ (map p).asIdeal ↔
      p.val.seminorm (algebraMap C.model.modelRing C.model.genericAlgebra a) < 1

def coordinateNorm (p : C.model.GenericPoint) (j : Fin n) : ℝ :=
  p.val.seminorm (algebraMap C.model.modelRing C.model.genericAlgebra (C.coordinate j))

/-- Zero coordinates have infinite additive valuation. -/
def valuationCoordinate (p : C.model.GenericPoint) (j : Fin n) : ENNReal :=
  if coordinateNorm C p j = 0 then ⊤ else ENNReal.ofReal (-Real.log (coordinateNorm C p j))

def coordinateStratum (I : Finset (Fin n)) : Set (PrimeSpectrum (SpecialRing C)) :=
  {x | ∀ j : Fin n, j.val < r + 1 + s →
    (Ideal.Quotient.mk (specialIdeal C) (C.coordinate j) ∈ x.asIdeal ↔ j ∈ I)}

/-- A component of the actual prescribed coordinate stratum. Its generic point is taken in the
locally closed coordinate locus, with the subspace topology: a stratum need not be closed in the
special fibre, so it is not the closure of its generic point there. -/
structure Stratum where
  vanishing : Finset (Fin n)
  allowed : ∀ j ∈ vanishing, j.val < r + 1 + s
  component : Set (PrimeSpectrum (SpecialRing C))
  in_coordinates : component ⊆ coordinateStratum C vanishing
  locusComponent : Set (coordinateStratum C vanishing)
  maximal_irreducible : locusComponent ∈ irreducibleComponents (coordinateStratum C vanishing)
  component_eq : component = Subtype.val '' locusComponent
  genericPoint : coordinateStratum C vanishing
  generic : IsGenericPoint genericPoint locusComponent

def coordinateFibre (R : Reduction C) (S : Stratum C) (p : C.model.GenericPoint) :
    Set C.model.GenericPoint :=
  {q | R.map q ∈ S.component ∧
    ∀ j : Fin (r + 1 + s),
      coordinateNorm C q ⟨j.val, j.isLt.trans_le C.bound⟩ =
        coordinateNorm C p ⟨j.val, j.isLt.trans_le C.bound⟩}

/-- A singleton Shilov boundary maximizes every actual affinoid function. -/
def IsSkeletalPoint (R : Reduction C) (S : Stratum C) (p q : C.model.GenericPoint) : Prop :=
  q ∈ coordinateFibre C R S p ∧ R.map q = S.genericPoint.val ∧
  ∀ (a : C.model.genericAlgebra) (z : C.model.GenericPoint),
    z ∈ coordinateFibre C R S p → z.val.seminorm a ≤ q.val.seminorm a

def skeleton (R : Reduction C) : Set C.model.GenericPoint :=
  {p | ∃ S : Stratum C, IsSkeletalPoint C R S p p}

/-- A retraction of the generic fibre of the standard chart `C` onto its skeleton, for the reduction
map `R`: a continuous self-map $\tau$ of the points of the generic fibre such that every point
reduces into the component of some coordinate stratum; whenever a point $p$ reduces into the
component of a stratum $S$, $\tau(p)$ is a skeletal point of $S$ for $p$ (`IsSkeletalPoint`: it
reduces into that component with the same norms of the coordinates $t_0, \dots, t_{r+s}$ as $p$,
reduces to the generic point of $S$, and has the largest seminorm on every affinoid function among
all such points); the image of $\tau$ is the skeleton; and $\tau$ fixes every point of the
skeleton. -/
structure Retraction (R : Reduction C) where
  map : C.model.GenericPoint → C.model.GenericPoint
  continuous : Continuous map
  covers : ∀ p : C.model.GenericPoint, ∃ S : Stratum C, R.map p ∈ S.component
  normalized : ∀ (p : C.model.GenericPoint) (S : Stratum C),
    R.map p ∈ S.component → IsSkeletalPoint C R S p (map p)
  image : Set.range map = skeleton C R
  fixes : ∀ p ∈ skeleton C R, map p = p

/-- The actual strong deformation homotopy of the normalized map. -/
structure StrongDeformation (R : Reduction C) (P : Retraction C R) where
  map : unitInterval × C.model.GenericPoint → C.model.GenericPoint
  continuous : Continuous map
  start : ∀ p, map (0, p) = p
  finish : ∀ p, map (1, p) = P.map p
  fixes : ∀ t p, p ∈ skeleton C R → map (t, p) = p

end MathlibExt.AlgebraicGeometry.SemistableSkeletonRealization
