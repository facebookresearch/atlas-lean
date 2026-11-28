/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HARMONIOUS COLORING: definitions

Source:
J. E. Hopcroft and M. S. Krishnamoorthy, "On the harmonious coloring of graphs", SIAM Journal
on Algebraic and Discrete Methods 4 (1983), 306-311, doi:10.1137/0604032.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HarmoniousColoring

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev HarmoniousColoringInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : HarmoniousColoringInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K`. -/
def WellFormed (i : HarmoniousColoringInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- A coloring `c` of `G` is harmonious: two edges with the same unordered pair of colors are
the same edge. -/
def IsHarmonious {n k : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin k)) : Prop :=
  ∀ u v x y : Fin n, G.Adj u v → G.Adj x y → s(c u, c v) = s(c x, c y) → s(u, v) = s(x, y)

/-- Some proper coloring with colors `Fin K` (at most `K` colors) is harmonious. -/
def HarmoniousColoringFeasible (i : HarmoniousColoringInstance) : Prop :=
  ∃ c : (Graph i).Coloring (Fin i.2.2), IsHarmonious c

open Classical in
/-- HARMONIOUS COLORING as a decision problem over bitstrings. -/
noncomputable def harmoniousColoringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HarmoniousColoringInstance) x with
  | some i => decide (WellFormed i ∧ HarmoniousColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HarmoniousColoring
