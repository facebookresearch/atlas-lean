/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 760
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.ENat.Lattice
public import MathlibExt.Combinatorics.SimpleGraph.Coloring.Vertex
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem760Wanted

/-! Source record `FC-ErdosProblem760`, ported from FormalConjectures
`ErdosProblems/760.lean` and checked against erdosproblems.com/760.
`SimpleGraph.Cocolorable` and `SimpleGraph.cochromaticNumber` are reused from
`MathlibExt.Combinatorics.SimpleGraph.Coloring.Vertex`. The upstream `answer(True)` is dropped.
Status: resolved
true (Alon–Krivelevich–Sudakov; formalized in Lean). -/

/-- Subgraphs of large cochromatic number, and the Erdős–Gimbel form. -/
def conjecture : Prop :=
  (∃ c > (0 : ℝ), ∀ (V : Type*) [Finite V] (G : SimpleGraph V) (m : ℕ),
    G.chromaticNumber = (m : ℕ∞) →
      ∃ H : G.Subgraph, ∃ k : ℕ, ((k : ℕ∞) ≤ H.coe.cochromaticNumber) ∧
        (c * (m : ℝ) / Real.log (m : ℝ) ≤ (k : ℝ))) ∧
  (∃ c > (0 : ℝ), ∀ (V : Type*) [Finite V] (G : SimpleGraph V) (m : ℕ),
    G.chromaticNumber = (m : ℕ∞) →
      ∃ H : G.Subgraph, ∃ k : ℕ, ((k : ℕ∞) ≤ H.coe.cochromaticNumber) ∧
        (c * Real.sqrt ((m : ℝ) / Real.log (m : ℝ)) ≤ (k : ℝ)))

/--
Resolved true: Resolved true (Alon-Krivelevich-Sudakov); formalized in Lean. Source:
plby/lean-proofs, src/v4.29.1/ErdosProblems/Erdos760.lean (theorem erdos_760, following Alon,
Krivelevich and Sudakov, Subgraphs with a large cochromatic number, 1997), pinned revision
8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos760.lean#L1306.
Moved from `OpenConjectures/Combinatorics/ErdosProblem760`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem760Wanted
