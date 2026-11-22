/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 847
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Combinatorics.Additive.AP.Three.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem847Wanted

/-! Source record `FC-ErdosProblem847`, ported from FormalConjectures
`ErdosProblems/847.lean` and checked against erdosproblems.com/847.
`ThreeAPFree` is reused from `Mathlib.Combinatorics.Additive.AP.Three.Defs`.
The source proposition is preserved; its external disproof by
Reiher–Rödl–Sales [RRS24] and a pinned external Lean proof are recorded in the
registry. This module states the proposition but does not refute it. -/

/-- Every `n`-subset holds a large 3AP-free subset. -/
def HasFew3APs (A : Set ℕ) := ∃ (ε : ℝ), ε > 0 ∧
  ∀ (B : Set ℕ), B ⊆ A → Finite B →
  ∃ (C : Set ℕ), C ⊆ B ∧ C.ncard ≥ ε * B.ncard ∧ ThreeAPFree C

/-- Every infinite set with uniformly large 3AP-free subsets is a finite union
of 3AP-free sets. -/
def conjecture : Prop :=
  ∀ (A : Set ℕ), Infinite A → HasFew3APs A →
    ∃ n, ∃ (S : Fin n → Set ℕ), (∀ i, ThreeAPFree (S i)) ∧ A = ⋃ i : Fin n, S i

/--
Resolved false: Resolved false externally by Reiher, Rödl, and Sales. This repository records
the historical proposition, not a proof. Source: Christian Reiher, Vojtěch Rödl, and Marcelo
Sales, Colouring versus density in integers and Hales–Jewett cubes, Journal of the London
Mathematical Society (2024), e12987, https://doi.org/10.1112/jlms.12987. Moved from
`OpenConjectures/NumberTheory/ErdosProblem847`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.ErdosProblem847Wanted
