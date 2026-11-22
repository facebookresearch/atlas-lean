/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECTILINEAR STEINER TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND13] GEOMETRIC STEINER TREE,
comment ("Remains so if the distance measure is replaced by the `L₁` "rectilinear" metric,
`|x₁ - x₂| + |y₁ - y₂|`");
M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM
Journal on Applied Mathematics 32 (1977), 826-834, doi:10.1137/0132071.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Sym.Sym2
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RectilinearSteinerTree

/-!
# RECTILINEAR STEINER TREE is NP-complete

INSTANCE: a set `P ⊆ ℤ × ℤ` of points in the plane and a positive integer `K`.
QUESTION: is there a finite set `Q ⊆ ℤ × ℤ` such that there is a spanning tree of total
weight `K` or less for the vertex set `P ∪ Q`, where the weight of an edge
`{(x₁, y₁), (x₂, y₂)}` is the rectilinear (`L₁`) distance `|x₁ - x₂| + |y₁ - y₂|`?

Each integer coordinate is encoded as a pair of naturals `(positive part, negative part)`
representing their difference, and `P` is the set of the listed points (a repeated point
does not change it). A spanning tree for `P ∪ Q` is a graph `T` on the vertex type `P ∪ Q`
(a `Finset (ℤ × ℤ)`) that is a tree in Mathlib's sense (`SimpleGraph.IsTree`), so every point
of `P ∪ Q` is a vertex of `T`; its weight is the sum over its edges of the rectilinear
distance between their endpoints.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the points of `P`, each a pair of coordinates encoded as (positive part,
negative part) pairs, and the bound `K`. -/
abbrev RectilinearSteinerTreeInstance := List ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ

/-- The integer a (positive part, negative part) pair represents. -/
def toInt (z : ℕ × ℕ) : ℤ := (z.1 : ℤ) - z.2

/-- The point set `P ⊆ ℤ × ℤ` of the instance. -/
def points (i : RectilinearSteinerTreeInstance) : Finset (ℤ × ℤ) :=
  (i.1.map fun p => (toInt p.1, toInt p.2)).toFinset

/-- The rectilinear (`L₁`) distance `|x₁ - x₂| + |y₁ - y₂|`. -/
def rectilinear (a b : ℤ × ℤ) : ℤ := |a.1 - b.1| + |a.2 - b.2|

/-- The rectilinear distance between the endpoints of an unordered pair of points. -/
def edgeWeight {V : Finset (ℤ × ℤ)} : Sym2 V → ℤ :=
  Sym2.lift ⟨fun a b => rectilinear a b, fun a b => by
    simp only [rectilinear, abs_sub_comm (a : ℤ × ℤ).1, abs_sub_comm (a : ℤ × ℤ).2]⟩

/-- The total weight of a graph on a finite set of points: the sum of the rectilinear lengths
of its edges. -/
noncomputable def totalWeight {V : Finset (ℤ × ℤ)} (T : SimpleGraph V) : ℤ :=
  ∑ᶠ e ∈ T.edgeSet, edgeWeight e

/-- Well-formedness of an instance: `0 < K`. -/
def WellFormed (i : RectilinearSteinerTreeInstance) : Prop :=
  0 < i.2

/-- Some finite `Q ⊆ ℤ × ℤ` and some tree `T` on the vertex set `P ∪ Q` have total
rectilinear weight at most `K`. -/
def RectilinearSteinerTreeFeasible (i : RectilinearSteinerTreeInstance) : Prop :=
  ∃ Q : Finset (ℤ × ℤ), ∃ T : SimpleGraph ↥(points i ∪ Q), T.IsTree ∧
    totalWeight T ≤ i.2

open Classical in
/-- RECTILINEAR STEINER TREE as a decision problem over bitstrings. -/
noncomputable def rectilinearSteinerTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RectilinearSteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ RectilinearSteinerTreeFeasible i)
  | none => false

/-- **RECTILINEAR STEINER TREE is NP-complete.** Source: Garey and Johnson (1979), [ND13],
comment; Garey and Johnson (1977). -/
public theorem_wanted rectilinearSteinerTree_npComplete :
    rectilinearSteinerTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rectilinearSteinerTreeDec

end MetaMathlibExt.Complexity.NPComplete.RectilinearSteinerTree
