/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMMON POINT SET is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MAXIMUM COMMON POINT SET;
T. Akutsu and M. M. Halldórsson, "On the approximation of largest common subtrees and largest
common point sets", Theoretical Computer Science 233 (2000), 33-50,
doi:10.1016/S0304-3975(97)00278-8 (conference version: Proc. ISAAC 1994, LNCS 834, 405-413,
doi:10.1007/3-540-58325-4_205).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Congruence
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.QuadraticProgrammingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CommonPointSet

open QuadraticProgramming (RatCode ratVal)

/-!
# COMMON POINT SET is NP-complete

INSTANCE: a positive integer `d`, a collection `S₁, …, S_k` of finite sets of points in `ℝ^d`,
and a positive integer `K`. QUESTION: is there a point set `S'` with at least `K` points that is
congruent to a subset of each `Sᵢ`?

This is the decision version of MAXIMUM COMMON POINT SET in the compendium of Crescenzi and
Kann, whose measure is the number of points of `S'`.

Points have rational coordinates: a point is a list of `d` rationals, and a rational is encoded
as `((p, q), r)` with value `(p - q) / r` and `r > 0` (`QuadraticProgramming.RatCode`,
`QuadraticProgramming.ratVal`, reused from `QuadraticProgrammingWanted`). A set `Sᵢ` is a list
of points (a repeated point denotes the same point), and points are read in
`EuclideanSpace ℝ (Fin d)`. All numbers use the canonical binary encoding.

The set `S'` is an injective family `v : Fin m → ℝ^d` with `K ≤ m`, and "`S'` is congruent to a
subset of `Sᵢ`" is a family `w` of points of `Sᵢ` with `Congruent v w` (Mathlib's congruence of
indexed families: all corresponding pairwise distances agree). Such a `w` is injective because
`v` is, and in Euclidean space a bijection between finite point sets that preserves all pairwise
distances extends to an isometry of `ℝ^d` (translations, rotations and reflections), so this is
congruence of point sets. The collection is nonempty (`k ≥ 1`); with no sets every `K` would be
a yes-instance.

Membership in NP: a certificate picks `K` points of each `Sᵢ` (taking `v` to be the points picked
in `S₁`), and the squared pairwise distances, which are rational, are compared exactly.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the dimension `d`, the point sets `S₁, …, S_k` (each a list of points, each
point a list of `d` rational coordinates), and the bound `K`. -/
abbrev CommonPointSetInstance := ℕ × List (List (List RatCode)) × ℕ

/-- The point of `ℝ^d` whose coordinates are listed in `x`. -/
noncomputable def point (d : ℕ) (x : List RatCode) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun c => (ratVal (x.getD c ((0, 0), 1)) : ℝ)

/-- Well-formedness of an instance: `d` is positive, the collection is nonempty, every point has
`d` coordinates, every encoded rational has a positive denominator, and `K` is positive. -/
def WellFormed (i : CommonPointSetInstance) : Prop :=
  0 < i.1 ∧ i.2.1 ≠ [] ∧ (∀ S ∈ i.2.1, ∀ x ∈ S, x.length = i.1 ∧ ∀ q ∈ x, 0 < q.2) ∧
    0 < i.2.2

/-- Some set `S'` of at least `K` points of `ℝ^d` is congruent to a subset of every `Sᵢ`. -/
def CommonPointSetFeasible (i : CommonPointSetInstance) : Prop :=
  ∃ m, i.2.2 ≤ m ∧ ∃ v : Fin m → EuclideanSpace ℝ (Fin i.1), Function.Injective v ∧
    ∀ S ∈ i.2.1, ∃ w : Fin m → EuclideanSpace ℝ (Fin i.1),
      (∀ a, ∃ x ∈ S, w a = point i.1 x) ∧ Congruent v w

open Classical in
/-- COMMON POINT SET as a decision problem over bitstrings. -/
noncomputable def commonPointSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CommonPointSetInstance) x with
  | some i => decide (WellFormed i ∧ CommonPointSetFeasible i)
  | none => false

/-- **COMMON POINT SET is NP-complete.** Source: Crescenzi and Kann, MAXIMUM COMMON POINT SET;
Akutsu and Halldórsson (2000). -/
public theorem_wanted commonPointSet_npComplete :
    commonPointSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L commonPointSetDec

end MetaMathlibExt.Complexity.NPComplete.CommonPointSet
