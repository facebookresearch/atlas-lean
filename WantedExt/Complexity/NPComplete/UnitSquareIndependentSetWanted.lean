/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET OF UNIT SQUARES is NP-complete

Source:
R. J. Fowler, M. S. Paterson and S. L. Tanimoto, "Optimal packing and covering in the plane are
NP-complete", Information Processing Letters 12(3) (1981), 133-137,
doi:10.1016/0020-0190(81)90111-3;
S. Bhore, J. Cardinal, J. Iacono and G. Koumoutsos, "Dynamic geometric independent set",
arXiv:2007.08643 (2020), Section 1 ("even the case of independent set of unit squares is
NP-complete", citing Fowler, Paterson and Tanimoto);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import WantedExt.Complexity.NPComplete.PlanarKMeansWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitSquareIndependentSet

open MetaMathlibExt.Complexity.NPComplete.PlanarKMeans (RatCode)

/-!
# INDEPENDENT SET OF UNIT SQUARES is NP-complete

INSTANCE: a finite set of `n` axis-parallel closed unit squares (side length `1`) in the plane,
given by their centers, which have rational coordinates, and a positive integer `K ≤ n`.
QUESTION: are there `K` pairwise disjoint squares, that is, an independent set of size at least
`K` in the intersection graph of the squares?

Fowler, Paterson and Tanimoto proved that this packing problem is NP-complete; their full text
was not available, and Bhore, Cardinal, Iacono and Koumoutsos (Section 1) record the result and
its attribution. The problem restricts [GT20] INDEPENDENT SET to intersection graphs of unit
squares.

Centers are given in the rational encoding `RatCode` of
`WantedExt.Complexity.NPComplete.PlanarKMeansWanted` (the positive and negative parts of the
numerator, and the denominator, which must be positive), with value `RatCode.val`. Two closed
axis-parallel squares of side `1` with centers `p` and `q` intersect exactly when
`|p.x - q.x| ≤ 1` and `|p.y - q.y| ≤ 1`, i.e. when the `ℓ∞` distance of the centers is at most
`1`; `unitSquareGraph` joins two distinct squares that intersect, and independence is Mathlib's
`SimpleGraph.IsIndepSet`. The squares form a set, so their centers are distinct. The bound
`K ≤ n` follows the instance class of [GT20]; for `K > n` the answer is trivially no.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the centers of the squares (pairs of rational coordinates) and the bound `K`. -/
abbrev UnitSquareIndependentSetInstance := List (RatCode × RatCode) × ℕ

/-- The intersection graph of the closed axis-parallel unit squares centered at the given
points: two distinct squares are adjacent when both coordinates of their centers differ by at
most `1`. -/
def unitSquareGraph (P : List (RatCode × RatCode)) : SimpleGraph (Fin P.length) :=
  SimpleGraph.fromRel fun a b =>
    |P[a].1.val - P[b].1.val| ≤ 1 ∧ |P[a].2.val - P[b].2.val| ≤ 1

/-- Well-formedness of an instance: all denominators are positive, the centers are distinct (as
points of the plane), and `1 ≤ K ≤ n`. -/
def WellFormed (i : UnitSquareIndependentSetInstance) : Prop :=
  (∀ p ∈ i.1, 0 < p.1.2 ∧ 0 < p.2.2) ∧ (i.1.map fun p => (p.1.val, p.2.val)).Nodup ∧
    1 ≤ i.2 ∧ i.2 ≤ i.1.length

/-- Some `K` of the squares are pairwise disjoint: an independent set of at least `K` vertices
in the intersection graph. -/
def UnitSquareIndependentSetFeasible (i : UnitSquareIndependentSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1.length), i.2 ≤ S.card ∧ (unitSquareGraph i.1).IsIndepSet ↑S

open Classical in
/-- INDEPENDENT SET OF UNIT SQUARES as a decision problem over bitstrings. -/
noncomputable def unitSquareIndependentSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitSquareIndependentSetInstance) x with
  | some i => decide (WellFormed i ∧ UnitSquareIndependentSetFeasible i)
  | none => false

/-- **INDEPENDENT SET OF UNIT SQUARES is NP-complete.** Source: Fowler, Paterson and Tanimoto
(1981); Bhore, Cardinal, Iacono and Koumoutsos (2020), Section 1. -/
public theorem_wanted unitSquareIndependentSet_npComplete :
    unitSquareIndependentSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitSquareIndependentSetDec

end MetaMathlibExt.Complexity.NPComplete.UnitSquareIndependentSet
