/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE of linear size (fixed fraction r): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE, comment.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueFixedFraction

/-- An instance: vertex count, edge list. -/
abbrev CliqueFixedFractionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CliqueFixedFractionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: a simple edge list on the vertices `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : CliqueFixedFractionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The graph has a clique of size at least `(p / q) |V|`: a clique of `k` vertices with
`p * |V| ≤ q * k`. -/
def CliqueFixedFractionFeasible (p q : ℕ) (i : CliqueFixedFractionInstance) : Prop :=
  ∃ k, p * i.1 ≤ q * k ∧ ∃ s, (Graph i).IsNClique k s

open Classical in
/-- CLIQUE of size at least `(p / q) |V|` as a decision problem over bitstrings. -/
noncomputable def cliqueFixedFractionDec (p q : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CliqueFixedFractionInstance) x with
  | some i => decide (WellFormed i ∧ CliqueFixedFractionFeasible p q i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CliqueFixedFraction
