/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TERRAIN GUARDING is NP-complete

Source:
J. King and E. Krohn, "Terrain guarding is NP-hard", SIAM Journal on Computing 40(5) (2011),
1316-1339, doi:10.1137/100791506 (arXiv:0907.1280, Section 2: the reduction from planar
3-SAT is for the discrete terrain guarding problem, "where both the set of guards and the set
of points to be guarded are a finite subset of the terrain").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TerrainGuarding

/-!
# TERRAIN GUARDING is NP-complete

INSTANCE: a 1.5-dimensional terrain `T`, that is, an `x`-monotone polygonal chain given by its
vertices `v₁, …, vₙ` with `vᵢ = (xᵢ, yᵢ)` and `xᵢ < xᵢ₊₁`, with an edge joining each pair
`vᵢ, vᵢ₊₁`; a finite set `G` of candidate guard points on the terrain; a finite set `N` of
points on the terrain; and an integer `K`.
QUESTION: is there a set of at most `K` guards from `G` such that every point of `N` is seen
by one of them? A point `p` on the terrain sees a point `q` on the terrain if the line segment
`pq` is never strictly below the terrain.

This is the discrete version of the problem, the one the source's reduction targets. Points
are elements of `ℝ × ℝ` with rational coordinates; the terrain is the union of its edges, each
the Mathlib `segment` between consecutive vertices. A segment point `z` is strictly below the
terrain when a terrain point `t` with the same `x`-coordinate has `t.2 > z.2`. A rational
number is given as the positive and negative parts of its numerator and its denominator, which
must be positive; coordinates and `K` use the canonical binary encoding. The terrain has at
least two vertices, so it has at least one edge.

Membership in NP: a certificate is the chosen guard set; since the terrain is piecewise linear,
whether `p` sees `q` is decided by comparing the segment `pq` with the terrain vertices between
them, in rational arithmetic.

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

/-- An instance: the terrain vertices `v₁, …, vₙ` in order, the candidate guards `G`, the points
`N` to be guarded (all as pairs of rational coordinates), and the bound `K`. -/
abbrev TerrainGuardingInstance :=
  List (RatCode × RatCode) × List (RatCode × RatCode) × List (RatCode × RatCode) × ℕ

/-- A point given by rational coordinates, as a point of `ℝ × ℝ`. -/
noncomputable def toPoint (p : RatCode × RatCode) : ℝ × ℝ :=
  ((p.1.val : ℝ), (p.2.val : ℝ))

/-- The terrain: the union of its edges, the segments `vᵢ vᵢ₊₁` between consecutive
vertices. -/
noncomputable def terrain (i : TerrainGuardingInstance) : Set (ℝ × ℝ) :=
  {z | ∃ e ∈ i.1.zip i.1.tail, z ∈ segment ℝ (toPoint e.1) (toPoint e.2)}

/-- `p` sees `q`: the segment `pq` is never strictly below the terrain, i.e. no terrain point
lies strictly above a point of the segment with the same `x`-coordinate. -/
def Sees (i : TerrainGuardingInstance) (p q : ℝ × ℝ) : Prop :=
  ∀ z ∈ segment ℝ p q, ∀ t ∈ terrain i, t.1 = z.1 → t.2 ≤ z.2

/-- Well-formedness of an instance: all denominators are positive; the terrain has at least two
vertices and strictly increasing `x`-coordinates; every guard and every point to be guarded
lies on the terrain; and `G` and `N` list distinct points, so they are sets. -/
def WellFormed (i : TerrainGuardingInstance) : Prop :=
  (∀ p ∈ i.1 ++ i.2.1 ++ i.2.2.1, 0 < p.1.2 ∧ 0 < p.2.2) ∧
    2 ≤ i.1.length ∧ (i.1.map fun v => v.1.val).IsChain (· < ·) ∧
    (∀ g ∈ i.2.1, toPoint g ∈ terrain i) ∧ (∀ p ∈ i.2.2.1, toPoint p ∈ terrain i) ∧
    (i.2.1.map fun p => (p.1.val, p.2.val)).Nodup ∧
    (i.2.2.1.map fun p => (p.1.val, p.2.val)).Nodup

/-- Some set of at most `K` guards from `G` sees every point of `N`. -/
def TerrainGuardingFeasible (i : TerrainGuardingInstance) : Prop :=
  ∃ S : Finset (Fin i.2.1.length), S.card ≤ i.2.2.2 ∧
    ∀ p ∈ i.2.2.1, ∃ g ∈ S, Sees i (toPoint i.2.1[g]) (toPoint p)

open Classical in
/-- TERRAIN GUARDING as a decision problem over bitstrings. -/
noncomputable def terrainGuardingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TerrainGuardingInstance) x with
  | some i => decide (WellFormed i ∧ TerrainGuardingFeasible i)
  | none => false

/-- **TERRAIN GUARDING is NP-complete.** Source: King and Krohn (2011). -/
public theorem_wanted terrainGuarding_npComplete :
    terrainGuardingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L terrainGuardingDec

end MetaMathlibExt.Complexity.NPComplete.TerrainGuarding
