/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMUM COMMUNICATION SPANNING TREE: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND7] OPTIMUM COMMUNICATION
SPANNING TREE;
D. S. Johnson, J. K. Lenstra and A. H. G. Rinnooy Kan, "The complexity of the network design
problem", Networks 8(4) (1978), 279-285, doi:10.1002/net.3230080402;
T. C. Hu, "Optimum communication spanning trees", SIAM Journal on Computing 3(3) (1974),
188-195, doi:10.1137/0203015 (the problem).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Filter

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimumCommunicationSpanningTree

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), weight matrix `w`, requirement
matrix `r`, bound `B`. -/
abbrev OptimumCommunicationSpanningTreeInstance := ℕ × List (List ℕ) × List (List ℕ) × ℕ

/-- The weight `w({u, v})` of the edge between `u` and `v`. -/
def weight (i : OptimumCommunicationSpanningTreeInstance) (u v : Fin i.1) : ℕ :=
  (i.2.1.getD u []).getD v 0

/-- The requirement `r({u, v})` of the pair `u, v`. -/
def requirement (i : OptimumCommunicationSpanningTreeInstance) (u v : Fin i.1) : ℕ :=
  (i.2.2.1.getD u []).getD v 0

/-- `M` is a symmetric `n × n` matrix with zero diagonal. -/
def SymmetricZeroDiagonal (n : ℕ) (M : List (List ℕ)) : Prop :=
  M.length = n ∧ (∀ row ∈ M, row.length = n) ∧
    (∀ a < n, ∀ b < n, (M.getD a []).getD b 0 = (M.getD b []).getD a 0) ∧
    ∀ a < n, (M.getD a []).getD a 0 = 0

/-- Well-formedness of an instance: at least one vertex (a tree is nonempty), and the weight
and requirement matrices are symmetric `n × n` matrices with zero diagonal. -/
def WellFormed (i : OptimumCommunicationSpanningTreeInstance) : Prop :=
  0 < i.1 ∧ SymmetricZeroDiagonal i.1 i.2.1 ∧ SymmetricZeroDiagonal i.1 i.2.2.1

/-- The total weight of the edges on a walk: the sum of `w` over its darts. -/
def walkWeight (i : OptimumCommunicationSpanningTreeInstance) {T : SimpleGraph (Fin i.1)}
    {u v : Fin i.1} (p : T.Walk u v) : ℕ :=
  (p.darts.map fun d => weight i d.fst d.snd).sum

/-- A spanning tree `T` with `∑_{u, v} W_T({u, v}) * r({u, v}) ≤ B`, the sum over unordered
pairs `{u, v}` of distinct vertices (each once, as `u < v`), where `P u v` is the path joining
`u` and `v` in `T` and `W_T({u, v})` its total weight. -/
def OptimumCommunicationSpanningTreeFeasible (i : OptimumCommunicationSpanningTreeInstance) :
    Prop :=
  ∃ T : SimpleGraph (Fin i.1), T.IsTree ∧
    ∃ P : (u v : Fin i.1) → T.Walk u v, (∀ u v, (P u v).IsPath) ∧
      ∑ u : Fin i.1, ∑ v ∈ Finset.univ.filter (u < ·),
        walkWeight i (P u v) * requirement i u v ≤ i.2.2.2

open Classical in
/-- OPTIMUM COMMUNICATION SPANNING TREE as a decision problem over bitstrings. -/
noncomputable def optimumCommunicationSpanningTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OptimumCommunicationSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ OptimumCommunicationSpanningTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OptimumCommunicationSpanningTree
