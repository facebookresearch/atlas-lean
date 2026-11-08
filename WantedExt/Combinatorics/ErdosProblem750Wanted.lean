/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 750
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

open Filter
open scoped NNReal

namespace MathlibExt.Combinatorics.ErdosProblem750Wanted

/-! Source record `FC-ErdosProblem750`, ported from FormalConjectures
`ErdosProblems/750.lean` (`theorem erdos_750` and its `variants`) and
checked against erdosproblems.com/750. The Mycielskian helpers
(`MycVerts`, `MycAdj`, `genMyc`, `IsRecursivelyBuiltMr`) need
`SimpleGraph.fromRel` (absent from pinned Mathlib), so the `stiebitz`
variant is not ported. The upstream `answer(True)` is dropped. Status:
proved; the cited formal proof is unconditional (it proves the Stiebitz theorem it uses). -/

/-- Infinite-chromatic graphs meet every prescribed independence-density bound. -/
def conjecture : Prop :=
  (∀ f : ℕ → ℝ≥0, atTop.Tendsto f atTop →
    ∃ (V : Type) (G : SimpleGraph V),
      G.chromaticNumber = ⊤ ∧
      ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
        ∃ I ⊆ S, G.IsIndepSet I ∧ (m : ℝ) / 2 - f m ≤ I.ncard) ∧
  (∀ ε : ℝ≥0, 0 < ε →
    ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
      ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
        ∃ I ⊆ S, G.IsIndepSet I ∧ (m : ℝ) / 2 - ε * m ≤ I.ncard) ∧
  (∀ c : ℝ≥0, 1 / 4 < c →
    ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
      ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
        ∃ I ⊆ S, G.IsIndepSet I ∧ (m : ℝ) / 2 - c * m ≤ I.ncard)

/--
Resolved true: Proved and formalized in Lean unconditionally: the cited development proves the
Stiebitz theorem it uses. Source: plby/lean-proofs, src/latest/ErdosProblems/Erdos750.lean
(theorem erdos_750_independence), pinned revision 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos750.lean#L41.
Moved from `OpenConjectures/Combinatorics/ErdosProblem750`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem750Wanted
