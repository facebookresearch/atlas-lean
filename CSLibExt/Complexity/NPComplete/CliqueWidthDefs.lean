/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE-WIDTH: definitions

Source:
M. R. Fellows, F. A. Rosamond, U. Rotics and S. Szeider, "Clique-width is NP-complete",
SIAM Journal on Discrete Mathematics 23(2) (2009), 909-939, doi:10.1137/070687256;
definition of `k`-expressions and clique-width: B. Courcelle and S. Olariu, "Upper bounds to the
clique width of graphs", Discrete Applied Mathematics 101(1-3) (2000), 77-114,
doi:10.1016/S0166-218X(99)00184-5.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Sum

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueWidth

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, and the bound `K`. -/
abbrev CliqueWidthInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CliqueWidthInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- `Generated k V H l`: the graph `H` on `V` with vertex labels `l : V → Fin k` is the value of
a `k`-expression. -/
inductive Generated (k : ℕ) : (V : Type) → SimpleGraph V → (V → Fin k) → Prop
  /-- `i(v)`: a single vertex with label `i`. -/
  | vertex (i : Fin k) : Generated k Unit ⊥ fun _ => i
  /-- `G ⊕ H`: the disjoint union of two labelled graphs. -/
  | union {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} {l : V → Fin k}
      {m : W → Fin k} :
      Generated k V G l → Generated k W H m → Generated k (V ⊕ W) (G ⊕g H) (Sum.elim l m)
  /-- `η_{i,j}`, `i ≠ j`: join every vertex labelled `i` to every vertex labelled `j`. -/
  | join {V : Type} {G : SimpleGraph V} {l : V → Fin k} (i j : Fin k) (hij : i ≠ j) :
      Generated k V G l →
        Generated k V (G ⊔ SimpleGraph.fromRel fun u v => l u = i ∧ l v = j) l
  /-- `ρ_{i→j}`: relabel every vertex labelled `i` to `j`. -/
  | relabel {V : Type} {G : SimpleGraph V} {l : V → Fin k} (i j : Fin k) :
      Generated k V G l → Generated k V G fun v => if l v = i then j else l v

/-- Well-formedness of an instance: the graph has at least one vertex (clique-width is defined
for such graphs), and the edge list describes a simple graph (no duplicate edges in either
orientation, no self-loops, endpoints in range). -/
def WellFormed (i : CliqueWidthInstance) : Prop :=
  0 < i.1 ∧ i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- The clique-width of the graph is at most `K`: the graph is isomorphic to the graph of some
`K`-expression. -/
def CliqueWidthFeasible (i : CliqueWidthInstance) : Prop :=
  ∃ (V : Type) (H : SimpleGraph V) (l : V → Fin i.2.2), Generated i.2.2 V H l ∧
    Nonempty (Graph i ≃g H)

open Classical in
/-- CLIQUE-WIDTH as a decision problem over bitstrings. -/
noncomputable def cliqueWidthDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CliqueWidthInstance) x with
  | some i => decide (WellFormed i ∧ CliqueWidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CliqueWidth
