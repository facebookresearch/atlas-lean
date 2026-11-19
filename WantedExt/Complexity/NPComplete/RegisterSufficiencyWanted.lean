/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REGISTER SUFFICIENCY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO1] REGISTER SUFFICIENCY;
R. Sethi, "Complete register allocation problems", SIAM Journal on Computing 4 (1975),
226-248, doi:10.1137/0204020.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Equiv.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RegisterSufficiency

/-!
# REGISTER SUFFICIENCY is NP-complete

Given a directed acyclic graph `G = (V, A)` and a positive integer `K`, is there a computation
for `G` that uses `K` or fewer registers, i.e., an ordering `v₁, …, vₙ` of the vertices in `V`,
where `n = |V|`, and a sequence `S₀, …, Sₙ` of subsets of `V`, each satisfying `|Sᵢ| ≤ K`, such
that `S₀` is empty, `Sₙ` contains all vertices with in-degree `0` in `G`, and, for
`1 ≤ i ≤ n`, `vᵢ ∈ Sᵢ`, `Sᵢ - {vᵢ} ⊆ Sᵢ₋₁`, and `Sᵢ₋₁` contains all vertices `u` for which
`(vᵢ, u) ∈ A`?

An arc `(v, u)` says that `u` is an operand of `v`; `Sᵢ` is the set of values held in registers
after the `i`-th step, which computes `vᵢ`. Each vertex is computed exactly once.

The digraph has vertices `Fin n` and is given by its arc list, with no repeated arcs; it is
acyclic, and `K ≥ 1` (`WellFormed`). The ordering is a permutation `v` of `Fin n`, with
`v k` the vertex computed at step `k + 1`; `S k` is `Sₖ` for `k : Fin (n + 1)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **REGISTER SUFFICIENCY is NP-complete.** Source: Garey and Johnson (1979), [PO1];
Sethi (1975). -/
public theorem_wanted registerSufficiency_npComplete :
    registerSufficiencyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L registerSufficiencyDec

end MetaMathlibExt.Complexity.NPComplete.RegisterSufficiency
