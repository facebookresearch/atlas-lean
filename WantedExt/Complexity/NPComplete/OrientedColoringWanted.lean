/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ORIENTED k-COLORING is NP-complete for every fixed k ≥ 4

Source:
W. F. Klostermeyer and G. MacGillivray, "Homomorphisms and oriented colorings of equivalence
classes of oriented graphs", Discrete Mathematics 274 (2004), 161-172,
doi:10.1016/S0012-365X(03)00086-4;
É. Sopena, "Homomorphisms and colourings of oriented graphs: An updated survey", Discrete
Mathematics 339 (2016), 1993-2005, doi:10.1016/j.disc.2015.03.018 (its section on complexity
records the result).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.Digraph.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OrientedColoring

/-!
# ORIENTED k-COLORING is NP-complete for every fixed k ≥ 4

Fix an integer `k ≥ 4`. INSTANCE: an oriented graph `D`, that is, a digraph with no loops and
no pair of opposite arcs. QUESTION: does `D` have an oriented `k`-coloring, that is, a
homomorphism to some oriented graph on `k` vertices? Equivalently: a proper `k`-coloring of the
underlying graph such that all arcs between any two color classes go in the same direction.

The vertices of `D` are `0, ..., n - 1` and its arcs are a list of ordered pairs. A target is a
Mathlib `Digraph (Fin k)` with no loops and no pair of opposite arcs, and the coloring is a map
`c` from vertices to `Fin k` sending every arc `(u, v)` of `D` to an arc `(c u, c v)` of the
target (only the values of `c` on `0, ..., n - 1` matter).

Klostermeyer and MacGillivray prove that deciding whether an oriented graph has an oriented
`k`-coloring is polynomial for `k ≤ 3` and NP-complete for every fixed `k ≥ 4`, even for
connected inputs; Sopena's survey records the result in its section on complexity. Membership
in NP: the target and the coloring are a certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **ORIENTED k-COLORING is NP-complete for every fixed `k ≥ 4`.** Source: Klostermeyer and
MacGillivray (2004); Sopena (2016). -/
public theorem_wanted orientedColoring_npComplete (k : ℕ) (hk : 4 ≤ k) :
    orientedColoringDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (orientedColoringDec k)

end MetaMathlibExt.Complexity.NPComplete.OrientedColoring
