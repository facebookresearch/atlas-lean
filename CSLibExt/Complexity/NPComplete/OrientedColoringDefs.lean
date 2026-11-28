/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ORIENTED k-COLORING: definitions

Source:
W. F. Klostermeyer and G. MacGillivray, "Homomorphisms and oriented colorings of equivalence
classes of oriented graphs", Discrete Mathematics 274 (2004), 161-172,
doi:10.1016/S0012-365X(03)00086-4;
É. Sopena, "Homomorphisms and colourings of oriented graphs: An updated survey", Discrete
Mathematics 339 (2016), 1993-2005, doi:10.1016/j.disc.2015.03.018 (its section on complexity
records the result).
-/
module

public import Mathlib.Combinatorics.Digraph.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OrientedColoring

/-- An instance: the number `n` of vertices and the arcs `(u, v)` of `D`. -/
abbrev OrientedColoringInstance := ℕ × List (ℕ × ℕ)

/-- Well-formedness of an instance: the arcs are distinct, join vertices `< n`, and `D` has no
loops and no pair of opposite arcs. -/
def WellFormed (i : OrientedColoringInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `D` has an oriented `k`-coloring: a map to `Fin k` that is a homomorphism to some oriented
graph `T` on `Fin k` (no loops, no pair of opposite arcs). -/
def OrientedColoringFeasible (k : ℕ) (i : OrientedColoringInstance) : Prop :=
  ∃ (T : Digraph (Fin k)) (c : ℕ → Fin k), (∀ a, ¬ T.Adj a a) ∧
    (∀ a b, T.Adj a b → ¬ T.Adj b a) ∧ ∀ e ∈ i.2, T.Adj (c e.1) (c e.2)

open Classical in
/-- ORIENTED k-COLORING, for the fixed `k`, as a decision problem over bitstrings. -/
noncomputable def orientedColoringDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OrientedColoringInstance) x with
  | some i => decide (WellFormed i ∧ OrientedColoringFeasible k i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OrientedColoring
