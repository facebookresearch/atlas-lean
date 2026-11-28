/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# H-DECOMPOSITION: definitions

Source:
D. Dor and M. Tarsi, "Graph decomposition is NP-complete: a complete proof of Holyer's
conjecture", SIAM Journal on Computing 26 (1997), 1166-1187, doi:10.1137/S0097539792229507.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HDecomposition

/-- An instance: vertex count `n` of `G` (vertices `Fin n`) and the edge list of `G`. -/
abbrev HDecompositionInstance := ℕ × List (ℕ × ℕ)

/-- The graph `G` of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : HDecompositionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- The pattern graph `H = (m, hs)` as a `SimpleGraph (Fin m)`. -/
def Pattern (m : ℕ) (hs : List (ℕ × ℕ)) : SimpleGraph (Fin m) :=
  Cslib.Complexity.Karp.edgeGraph m hs

/-- A pattern `H = (m, hs)` for which the theorem is stated: `hs` is a simple edge list on
`Fin m` (no duplicate edges in either orientation, no self-loops, endpoints in range), and some
connected component of `H` has at least three edges. -/
def ValidPattern (m : ℕ) (hs : List (ℕ × ℕ)) : Prop :=
  (hs.Nodup ∧ ∀ e ∈ hs, e.1 < m ∧ e.2 < m ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ hs) ∧
    ∃ c : (Pattern m hs).ConnectedComponent, 3 ≤ c.toSimpleGraph.edgeSet.ncard

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : HDecompositionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `G` has an `H`-decomposition: some finite family of copies of `H` in `G` whose edge sets
partition the edge set of `G`. -/
def HDecompositionFeasible (m : ℕ) (hs : List (ℕ × ℕ)) (i : HDecompositionInstance) : Prop :=
  ∃ k : ℕ, ∃ f : Fin k → (Pattern m hs).Copy (Graph i),
    ∀ e ∈ (Graph i).edgeSet, ∃! j : Fin k, e ∈ Sym2.map (f j) '' (Pattern m hs).edgeSet

open Classical in
/-- H-DECOMPOSITION for the fixed pattern `H = (m, hs)` as a decision problem over
bitstrings. -/
noncomputable def hDecompositionDec (m : ℕ) (hs : List (ℕ × ℕ)) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := HDecompositionInstance) x with
  | some i => decide (WellFormed i ∧ HDecompositionFeasible m hs i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HDecomposition
