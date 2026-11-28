/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanDefs

/-!
# EUCLIDEAN p-CENTER: definitions

INSTANCE: a finite set `P ⊆ Z × Z` of points in the plane, a positive integer `p`, and a
positive rational `r`. QUESTION: can `P` be covered by `p` closed disks of radius `r`, that is,
are there `p` centers `c₁, ..., c_p` anywhere in the Euclidean plane such that every point of
`P` is at Euclidean distance at most `r` from some `cⱼ`?

This is the decision form of the planar Euclidean `p`-center problem of Megiddo and Supowit
(find `p` supply points anywhere in the plane minimizing the maximum distance from a demand
point to its nearest supply point), and of MINIMUM GEOMETRIC DISK COVER in the
Crescenzi-Kann compendium (`P ⊆ Z × Z`, rational `r > 0`).

Points use the encoding of `GeometricTravelingSalesmanDefs`: each coordinate is an integer
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

Source:
N. Megiddo and K. J. Supowit, "On the complexity of some common geometric location
problems", SIAM Journal on Computing 13 (1984), 182-196, doi:10.1137/0213014;
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM GEOMETRIC DISK COVER.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EuclideanPCenter

open GeometricTravelingSalesman (point)

/-- An instance: the points (pairs of encoded integers), the number `p` of disks, and the
radius `r` as a pair `(num, den)` standing for `num / den`. -/
abbrev EuclideanPCenterInstance := List ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ × (ℕ × ℕ)

/-- The radius `r = num / den` of the instance. -/
noncomputable def radius (i : EuclideanPCenterInstance) : ℝ :=
  (i.2.2.1 : ℝ) / i.2.2.2

/-- Well-formedness of an instance: the points are distinct, `p` is positive, and the radius
`num / den` has a positive denominator and is positive. -/
def WellFormed (i : EuclideanPCenterInstance) : Prop :=
  (i.1.map point).Nodup ∧ 0 < i.2.1 ∧ 0 < i.2.2.2 ∧ 0 < i.2.2.1

/-- Some `p` centers in the plane put every point within Euclidean distance `r` of one of
them. -/
def EuclideanPCenterFeasible (i : EuclideanPCenterInstance) : Prop :=
  ∃ c : Fin i.2.1 → ℝ × ℝ, ∀ q ∈ i.1, ∃ j,
    ((point q).1 - (c j).1) ^ 2 + ((point q).2 - (c j).2) ^ 2 ≤ radius i ^ 2

open Classical in
/-- EUCLIDEAN p-CENTER as a decision problem over bitstrings. -/
noncomputable def euclideanPCenterDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EuclideanPCenterInstance) x with
  | some i => decide (WellFormed i ∧ EuclideanPCenterFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EuclideanPCenter
