/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 729
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Real.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem729Wanted

/-! Source record `FC-ErdosProblem729`, ported from FormalConjectures
`ErdosProblems/729.lean` (`theorem erdos_729`) and checked against
erdosproblems.com/729. The upstream `answer(True)` is dropped. Status:
resolved true externally by Barreto and Leeham. This module states the result
but does not prove it; a pinned external Lean proof is in the registry. -/

/-- Smooth denominators past `n + C log n` occur infinitely often. -/
def conjecture : Prop :=
  ∀ (C : ℝ) (_ : C > 0),
    ∃ K ≥ 3, Set.Infinite {T : ℕ × ℕ × ℕ |
      let (a, b, n) := T
      a > 0 ∧ b > 0 ∧ n > 0 ∧
      (a : ℝ) + b > n + C * Real.log n ∧
      ∀ p, p.Prime → p > K →
        padicValNat p ((n.factorial / (a.factorial * b.factorial) : ℚ).den) = 0}

/--
Resolved true: Resolved externally by Barreto and Leeham. This repository records the statement,
not an internal proof; a pinned external Lean proof is cited below. Source: External Lean proof
of Erdős Problem 729,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos729.lean.
Moved from `OpenConjectures/NumberTheory/ErdosProblem729`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem729Wanted
