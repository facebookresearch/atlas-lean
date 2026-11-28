/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED STEINER NETWORK: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM GENERALIZED STEINER NETWORK ("Also called Minimum Survivable Network");
K. Jain, "A factor 2 approximation algorithm for the generalized Steiner network problem",
Combinatorica 21 (2001), 39-60, doi:10.1007/s004930170004 (the problem with a bound `u_e` on
the number of copies of each edge `e`);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (STEINER TREE is NP-complete);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedSteinerNetwork

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list (an entry `(u, v, w, c)` is
the edge `{u, v}` with weight `w` and capacity `c`), the requirements (an entry `(i, j, r)`
says `r(i, j) = r`), and the bound `K`. -/
abbrev GeneralizedSteinerNetworkInstance :=
  ℕ × List (ℕ × ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : GeneralizedSteinerNetworkInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (i.2.1.map fun e => (e.1, e.2.1))

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the requirements
name pairs of distinct vertices with at most one entry per ordered pair, and `0 < K`. -/
def WellFormed (i : GeneralizedSteinerNetworkInstance) : Prop :=
  ((i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)) ∧
    (i.2.2.1.map fun q => (q.1, q.2.1)).Nodup ∧
    (∀ q ∈ i.2.2.1, q.1 < i.1 ∧ q.2.1 < i.1 ∧ q.1 ≠ q.2.1) ∧ 0 < i.2.2.2

/-- Some `f` within the capacities and of cost at most `K` meets every requirement: for each
listed `(a, b, r)` there are `r` paths from `a` to `b` in `G` such that every edge `e` lies on
at most `f(e)` of them. -/
def GeneralizedSteinerNetworkFeasible (i : GeneralizedSteinerNetworkInstance) : Prop :=
  ∃ f : Fin i.2.1.length → ℕ,
    (∀ k, f k ≤ (i.2.1.get k).2.2.2) ∧
      ∑ k, (i.2.1.get k).2.2.1 * f k ≤ i.2.2.2 ∧
        ∀ q ∈ i.2.2.1, ∀ (ha : q.1 < i.1) (hb : q.2.1 < i.1),
          ∃ paths : Fin q.2.2 → (Graph i).Path ⟨q.1, ha⟩ ⟨q.2.1, hb⟩,
            ∀ k, (Finset.univ.filter fun l =>
              s((i.2.1.get k).1, (i.2.1.get k).2.1) ∈
                (paths l).1.edges.map (Sym2.map Fin.val)).card ≤ f k

open Classical in
/-- GENERALIZED STEINER NETWORK as a decision problem over bitstrings. -/
noncomputable def generalizedSteinerNetworkDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeneralizedSteinerNetworkInstance) x with
  | some i => decide (WellFormed i ∧ GeneralizedSteinerNetworkFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GeneralizedSteinerNetwork
