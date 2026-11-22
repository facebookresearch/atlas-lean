/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 539
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section

open Filter

open scoped Asymptotics

namespace MathlibExt.NumberTheory.ErdosProblem539Wanted

/-! Source record `FC-ErdosProblem539`, ported from FormalConjectures
`ErdosProblems/539.lean` (`def IsCofactorLowerBound`,
`noncomputable def cofactorThreshold`, and the `sq_isBigO` variant) and
checked against erdosproblems.com/539. The open `=Θ` problems are not ported.
Status: resolved true (Erdős–Szemerédi `n^{1/2} ≪ h(n)`). -/

/-- Every positive `n`-set has at least `m` cofactors. Members are required
positive since the source quotient `a / (a, b)` is undefined at `(0, 0)`. -/
def IsCofactorLowerBound (n m : ℕ) : Prop := ∀ A : Finset ℕ, A.card = n →
  (∀ a ∈ A, 0 < a) →
  m ≤ ((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b).card

/-- Largest cofactor lower bound for `n`. -/
noncomputable def cofactorThreshold (n : ℕ) : ℕ :=
  sSup {m | IsCofactorLowerBound n m}

/-- `√n` is big-O of the cofactor threshold. -/
def conjecture : Prop :=
  (fun n : ℕ ↦ Real.sqrt (n : ℝ)) =O[atTop]
    fun n ↦ (cofactorThreshold n : ℝ)

/--
Resolved true: Proved by Erdos-Szemeredi (sqrt lower bound).  (The open Theta-asymptotic
questions for the cofactor threshold remain unported; see formalization gaps.) Source: J.
Schmitt, T. Gehrunger, J. Dekoninck, G. Bérczi, U. Kreitner, L. Price, D. Holmes, ProofCouncil:
An LLM Agent for Solving Open Mathematical Problems, arXiv:2607.09474 (2026),
https://arxiv.org/abs/2607.09474. Moved from `OpenConjectures/NumberTheory/ErdosProblem539`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem539Wanted
