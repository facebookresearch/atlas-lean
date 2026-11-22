/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 756
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Finset.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Lattice.Nat
public import MathlibExt.Geometry.Metric

@[expose] public section

open Filter
open scoped Asymptotics

namespace MathlibExt.Geometry.ErdosProblem756Wanted

/-! Source record `FC-ErdosProblem756`, ported from FormalConjectures
`ErdosProblems/756.lean` and checked against erdosproblems.com/756.
The plane is `EuclideanSpace ℝ (Fin 2)`. The distance API
(`distanceSet`, `distanceMultiplicity`) is reused from `MathlibExt.Geometry.Metric`. The upstream
`answer(True)` is dropped. Status: resolved true by [Bh24]. This module
states the externally proved results but does not prove them; an external
Lean proof is linked in the registry. -/

/-- The distances determined by `A` occurring for at least `k` pairs. -/
noncomputable def richDistances (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (k : ℕ) : Finset ℝ :=
  (distanceSet A).filter fun d => k ≤ distanceMultiplicity A d

/-- The largest number of rich distances over `n`-point sets. -/
noncomputable def maxRichDistances (n : ℕ) : ℕ :=
  sSup {(richDistances A (n + 1)).card | (A : Finset (EuclideanSpace ℝ (Fin 2))) (_ : A.card = n)}

/-- Three externally proved rich-distance results: the linear lower bound,
Bhowmick's quarter-density construction, and its generalization. -/
def conjecture : Prop :=
  ((fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (maxRichDistances n : ℝ))) ∧
  (∀ n : ℕ, ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.card = n ∧ n / 4 ≤ (richDistances A (n + 1)).card) ∧
  (∀ m : ℕ, 1 ≤ m → ∀ᶠ n : ℕ in atTop, ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.card = n ∧ n / (2 * (m + 1)) ≤ (richDistances A (n + m)).card)

/--
Resolved true: Resolved externally by K. Bhowmick. This repository records three resulting
statements, not internal proofs; a separate pinned Lean proof is cited below. This entry
documents the statement; it registers no open claim. Source: K. Bhowmick, A problem of Erdős
about rich distances, arXiv:2407.01174 (2024), https://arxiv.org/abs/2407.01174; External Lean
proof of Erdős Problem 756,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos756.lean.
Moved from `OpenConjectures/Geometry/ErdosProblem756`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Geometry.ErdosProblem756Wanted
