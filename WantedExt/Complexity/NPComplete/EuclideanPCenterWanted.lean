/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EUCLIDEAN p-CENTER is NP-complete

Source:
N. Megiddo and K. J. Supowit, "On the complexity of some common geometric location
problems", SIAM Journal on Computing 13 (1984), 182-196, doi:10.1137/0213014;
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM GEOMETRIC DISK COVER.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EuclideanPCenterDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EuclideanPCenter

open GeometricTravelingSalesman (point)

/-!
# EUCLIDEAN p-CENTER is NP-complete

INSTANCE: a finite set `P ⊆ Z × Z` of points in the plane, a positive integer `p`, and a
positive rational `r`. QUESTION: can `P` be covered by `p` closed disks of radius `r`, that is,
are there `p` centers `c₁, ..., c_p` anywhere in the Euclidean plane such that every point of
`P` is at Euclidean distance at most `r` from some `cⱼ`?

This is the decision form of the planar Euclidean `p`-center problem of Megiddo and Supowit
(find `p` supply points anywhere in the plane minimizing the maximum distance from a demand
point to its nearest supply point), and of MINIMUM GEOMETRIC DISK COVER in the
Crescenzi-Kann compendium (`P ⊆ Z × Z`, rational `r > 0`).

Points use the encoding of `GeometricTravelingSalesmanWanted`: each coordinate is an integer
given as a pair `(a, b)` of naturals standing for `a - b` (`GeometricTravelingSalesman.point`).
The radius is `r = num / den`. The centers are real points `(x, y)`, and the distance condition
is written with squares, `(x₀ - x)² + (y₀ - y)² ≤ r²` (Mathlib's `dist` on `ℝ × ℝ` is the
sup distance, not the Euclidean one).

Megiddo and Supowit prove that the Euclidean `p`-center problem is NP-hard, indeed NP-hard even
to approximate the optimal radius sufficiently closely. Such a gap survives moving each point
by a small enough distance, so their instances can be replaced by rational points and then,
after scaling, by integer points with a rational radius between the two gap values. Membership in
NP: a certificate assigns the points to `p` groups; the smallest disk enclosing a group is
determined by at most three of its points, its center and squared radius are rational, and
comparing that squared radius with `r²` is exact.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EUCLIDEAN p-CENTER is NP-complete.** Source: Megiddo and Supowit (1984); Crescenzi and
Kann, MINIMUM GEOMETRIC DISK COVER. -/
public theorem_wanted euclideanPCenter_npComplete :
    euclideanPCenterDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L euclideanPCenterDec

end MetaMathlibExt.Complexity.NPComplete.EuclideanPCenter
