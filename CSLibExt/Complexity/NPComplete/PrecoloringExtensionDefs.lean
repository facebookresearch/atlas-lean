/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECOLORING EXTENSION: definitions

Source:
M. Biro, M. Hujter, and Z. Tuza, "Precoloring extension. I. Interval graphs", Discrete
Mathematics 100 (1992), 267-279 (NP-completeness on interval graphs, hence on general graphs);
hardness also follows directly from Garey-Johnson CHROMATIC NUMBER (GT4) by taking the
precoloring to be empty.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecoloringExtension

/-- **Instances of PRECOLORING EXTENSION.** An instance of precoloring extension is a tuple
$(n, E, c, K)$ consisting of a natural number $n$ (the number of vertices), a list $E$ of pairs
of natural numbers (the edges), a list $c$ of natural numbers (the partial coloring, where an
entry $0$ means uncolored and an entry $k + 1$ means color $k$), and a natural number $K$ (the
number of colors). -/
abbrev PrecoloringExtensionInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- **Well-formed precoloring extension instances.** An instance $(n, E, c, K)$ of precoloring
extension is well formed when the edge list $E$ has no repeated entries, every edge $(u, v)$ in
$E$ satisfies $u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E$, and the partial coloring $c$
has length $n$. -/
def WellFormed (i : PrecoloringExtensionInstance) : Prop :=
  i.2.1.Nodup ∧
    (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.length = i.1

/-- **Feasible precoloring extension instances.** An instance $(n, E, c, K)$ of precoloring
extension is feasible when there is a list $\chi = (\chi_0, \dots, \chi_{n-1})$ of $n$ natural
numbers such that $\chi_v < K$ for every vertex $v < n$, $\chi_v = c_v - 1$ for every vertex
$v < n$ with $c_v \ne 0$, and $\chi_u \ne \chi_v$ for every edge $(u, v)$ in $E$. Here $c_v$ is
the entry of $c$ at position $v$, and an entry of a list at a position beyond its length is read
as $0$. -/
def PrecoloringExtensionFeasible
    (i : PrecoloringExtensionInstance) : Prop :=
  ∃ coloring : List ℕ, coloring.length = i.1 ∧ (∀ v < i.1, coloring.getD v 0 < i.2.2.2) ∧
    (∀ v < i.1, i.2.2.1.getD v 0 ≠ 0 → coloring.getD v 0 = i.2.2.1.getD v 0 - 1) ∧
    ∀ e ∈ i.2.1, coloring.getD e.1 0 ≠ coloring.getD e.2 0

open Classical in
/-- **PRECOLORING EXTENSION as a decision problem.** The decision problem PRECOLORING EXTENSION
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
precoloring extension instance that is well formed and feasible; bitstrings that do not decode
are rejected. -/
noncomputable def precoloringExtensionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecoloringExtensionInstance) x with
  | some i => decide (WellFormed i ∧ PrecoloringExtensionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PrecoloringExtension
