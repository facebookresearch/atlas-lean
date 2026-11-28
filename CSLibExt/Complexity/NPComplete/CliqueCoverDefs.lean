/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueCover

/-- **A clique-cover instance.** A vertex count `n`, a list of edges on the vertices
`0, …, n - 1`, and the bound `ℓ` on the number of cliques (Karp 1972, problem 13). -/
abbrev CliqueCoverInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **The graph of a clique-cover instance.** The simple graph on `Fin n` whose edges are the
listed pairs, read in either orientation. -/
def Graph (i : CliqueCoverInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- **Well-formed clique-cover instances.** The edge list has no repeated entry, and every listed
edge joins two distinct vertices below `n` and is not also listed in the reverse orientation. -/
def WellFormed (i : CliqueCoverInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasible clique-cover instances.** The vertices can be labelled with `ℓ` labels so that
any two distinct vertices with the same label are adjacent: the vertex set is the union of `ℓ` or
fewer cliques (Karp 1972, problem 13). -/
def CliqueCoverFeasible (i : CliqueCoverInstance) : Prop :=
  ∃ c : Fin i.1 → Fin i.2.2, ∀ u v, u ≠ v → c u = c v → (Graph i).Adj u v

open Classical in
/-- **The CLIQUE COVER decision problem.** It accepts a bitstring exactly when it decodes to a
well-formed, feasible clique-cover instance. -/
noncomputable def cliqueCoverDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := CliqueCoverInstance) x with
  | some i => decide (WellFormed i ∧ CliqueCoverFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CliqueCover
