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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PlanarKMeansDefs

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

/-- **PLANAR k-MEANS is NP-complete.** Source: Mahajan, Nimbhorkar and Varadarajan (2012),
Theorem 1. -/
public theorem_wanted planarKMeans_npComplete :
    planarKMeansDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarKMeansDec

end MetaMathlibExt.Complexity.NPComplete.PlanarKMeans
