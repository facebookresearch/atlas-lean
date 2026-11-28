/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REGISTER SUFFICIENCY: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO1] REGISTER SUFFICIENCY;
R. Sethi, "Complete register allocation problems", SIAM Journal on Computing 4 (1975),
226-248, doi:10.1137/0204020.
-/
module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Equiv.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RegisterSufficiency

/-- An instance: the vertex count `n`, the arc list `A` (pairs `(v, u)` for arcs `v → u`), and
the register bound `K`. -/
abbrev RegisterSufficiencyInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The digraph of the instance on `Fin n`: `v → u` is an arc iff `(v, u)` is in the arc
list. -/
def Graph (i : RegisterSufficiencyInstance) : Digraph (Fin i.1) where
  Adj v u := ((v : ℕ), (u : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: the arc list has no repeated arcs and its endpoints are
vertices, the digraph is acyclic (no vertex reaches itself by a nonempty directed path), and
the bound `K` is positive. -/
def WellFormed (i : RegisterSufficiencyInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1) ∧
    (∀ v, ¬ Relation.TransGen (Graph i).Adj v v) ∧ 0 < i.2.2

/-- A computation with at most `K` registers: an ordering `v` of the vertices and register sets
`S 0, …, S n` of size at most `K`, with `S 0 = ∅`, every in-degree-`0` vertex in `S n`, and, at
each step, the computed vertex held afterwards, no other value newly loaded, and all its
operands held before. -/
def RegisterSufficiencyFeasible (i : RegisterSufficiencyInstance) : Prop :=
  ∃ v : Equiv.Perm (Fin i.1), ∃ S : Fin (i.1 + 1) → Finset (Fin i.1),
    (∀ k, (S k).card ≤ i.2.2) ∧ S 0 = ∅ ∧
      (∀ u, (∀ w, ¬ (Graph i).Adj w u) → u ∈ S (Fin.last i.1)) ∧
      ∀ k : Fin i.1, v k ∈ S k.succ ∧ S k.succ \ {v k} ⊆ S k.castSucc ∧
        ∀ u, (Graph i).Adj (v k) u → u ∈ S k.castSucc

open Classical in
/-- REGISTER SUFFICIENCY as a decision problem over bitstrings. -/
noncomputable def registerSufficiencyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RegisterSufficiencyInstance) x with
  | some i => decide (WellFormed i ∧ RegisterSufficiencyFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RegisterSufficiency
