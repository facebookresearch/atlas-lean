/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET OF UNIT SQUARES: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import CSLibExt.Complexity.NPComplete.PlanarKMeansDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitSquareIndependentSet

open MetaMathlibExt.Complexity.NPComplete.PlanarKMeans (RatCode)

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

end MetaMathlibExt.Complexity.NPComplete.UnitSquareIndependentSet
