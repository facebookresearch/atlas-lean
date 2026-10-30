/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECOLORING EXTENSION is NP-complete

Source:
M. Biro, M. Hujter, and Z. Tuza, "Precoloring extension. I. Interval graphs", Discrete
Mathematics 100 (1992), 267-279 (NP-completeness on interval graphs, hence on general graphs);
hardness also follows directly from Garey-Johnson CHROMATIC NUMBER (GT4) by taking the
precoloring to be empty.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecoloringExtension

/-!
# PRECOLORING EXTENSION is NP-complete

An undirected graph, a partial coloring (0 means uncolored, `k + 1` means color `k`), and a
bound `K`. The question is whether the partial coloring extends to a proper coloring with
colors `0, …, K - 1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A precoloring-extension instance: vertex count, edge list, partial coloring (0 uncolored,
k+1 color k), number of colors. -/
abbrev PrecoloringExtensionInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : PrecoloringExtensionInstance) : Prop :=
  i.2.1.Nodup ∧
    (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.length = i.1

/-- A proper extension of the partial coloring. -/
def PrecoloringExtensionFeasible
    (i : PrecoloringExtensionInstance) : Prop :=
  ∃ coloring : List ℕ, coloring.length = i.1 ∧ (∀ v < i.1, coloring.getD v 0 < i.2.2.2) ∧
    (∀ v < i.1, i.2.2.1.getD v 0 ≠ 0 → coloring.getD v 0 = i.2.2.1.getD v 0 - 1) ∧
    ∀ e ∈ i.2.1, coloring.getD e.1 0 ≠ coloring.getD e.2 0

open Classical in
/-- PRECOLORING EXTENSION as a decision problem over bitstrings. -/
noncomputable def precoloringExtensionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecoloringExtensionInstance) x with
  | some i => decide (WellFormed i ∧ PrecoloringExtensionFeasible i)
  | none => false

/-- **PRECOLORING EXTENSION is NP-complete.** Source: M. Biro, M. Hujter, and Z. Tuza,
"Precoloring extension. I. Interval graphs", Discrete Mathematics 100 (1992), 267-279 (NP-
completeness on interval graphs, hence on general graphs); hardness also follows directly
from Garey-Johnson CHROMATIC NUMBER (GT4) by taking the precoloring to be empty. -/
public theorem_wanted precoloringExtension_npComplete :
    precoloringExtensionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precoloringExtensionDec

end MetaMathlibExt.Complexity.NPComplete.PrecoloringExtension
