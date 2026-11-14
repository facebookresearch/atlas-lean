/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR k-MEANS is NP-complete

Source:
M. Mahajan, P. Nimbhorkar and K. Varadarajan, "The planar k-means problem is NP-hard",
Theoretical Computer Science 442 (2012), 13-21, doi:10.1016/j.tcs.2010.05.034, Theorem 1
(reduction from planar 3-SAT).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarKMeans

/-!
# PLANAR k-MEANS is NP-complete

INSTANCE: a finite set `S = {p₁, …, pₙ}` of points with rational coordinates in the plane, an
integer `k ≥ 1`, and a rational bound `R`.
QUESTION: are there `k` centers `c₁, …, c_k` anywhere in `ℝ²` such that
`∑ᵢ min_{1 ≤ j ≤ k} d(pᵢ, cⱼ)² ≤ R`, where `d` is the Euclidean distance?

Points are elements of `EuclideanSpace ℝ (Fin 2)` and `d` is its `dist`. A rational number is
given as the positive and negative parts of its numerator and its denominator, which must be
positive. The points are a list, so a repeated point counts with its multiplicity; the source
also considers instances whose points form a multiset, and instances without repetition are a
subclass. Coordinates and the bound use the canonical binary encoding.

Membership in NP: for a fixed assignment of the points to `k` clusters, the best center of each
cluster is its centroid, so the rational clustering cost of an assignment is a polynomial-size
certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A rational number: the positive and negative parts of its numerator, and its denominator. -/
abbrev RatCode := (ℕ × ℕ) × ℕ

/-- The value of a rational code. -/
def RatCode.val (q : RatCode) : ℚ := ((q.1.1 : ℤ) - q.1.2 : ℤ) / (q.2 : ℚ)

/-- An instance: the points (pairs of rational coordinates), `k`, and the bound `R`. -/
abbrev PlanarKMeansInstance := List (RatCode × RatCode) × ℕ × RatCode

/-- A point of the instance as an element of the Euclidean plane. -/
noncomputable def point (p : RatCode × RatCode) : EuclideanSpace ℝ (Fin 2) :=
  !₂[(p.1.val : ℝ), (p.2.val : ℝ)]

/-- Well-formedness of an instance: all denominators are positive and `k ≥ 1`. -/
def WellFormed (i : PlanarKMeansInstance) : Prop :=
  (∀ p ∈ i.1, 0 < p.1.2 ∧ 0 < p.2.2) ∧ 1 ≤ i.2.1 ∧ 0 < i.2.2.2

/-- Some `k` centers in the plane give every point its squared distance to the nearest center,
with total at most `R`. -/
def PlanarKMeansFeasible (i : PlanarKMeansInstance) : Prop :=
  ∃ c : Fin i.2.1 → EuclideanSpace ℝ (Fin 2),
    (i.1.map fun p => ⨅ j, dist (point p) (c j) ^ 2).sum ≤ (i.2.2.val : ℝ)

open Classical in
/-- PLANAR k-MEANS as a decision problem over bitstrings. -/
noncomputable def planarKMeansDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PlanarKMeansInstance) x with
  | some i => decide (WellFormed i ∧ PlanarKMeansFeasible i)
  | none => false

/-- **PLANAR k-MEANS is NP-complete.** Source: Mahajan, Nimbhorkar and Varadarajan (2012),
Theorem 1. -/
public theorem_wanted planarKMeans_npComplete :
    planarKMeansDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarKMeansDec

end MetaMathlibExt.Complexity.NPComplete.PlanarKMeans
