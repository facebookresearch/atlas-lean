/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

open Real

namespace MathlibExt.NumberTheory.ErdosProblem1Wanted

/-! Source record `FC-ErdosProblem1`, ported from FormalConjectures
`ErdosProblems/1.lean` (`theorem erdos_1`) and checked against
erdosproblems.com/1. The conjecture is disproved; this records the
historical uniform-bound statement. -/

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

def conjecture : Prop :=
  ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),
    N ≠ 0 → C * 2 ^ A.card < N

/-- **Disproof of Erdős Problem 1 on distinct subset sums.** There is no real number $C > 0$
such that for every natural number $N \ne 0$ and every finite set $A \subseteq \{1, \dots, N\}$
whose distinct subsets have distinct sums, $C \cdot 2^{|A|} < N$.

Resolved false: Disproved: machine-checked disproof recorded in the FormalConjectures source
record. Source: Lean 4 disproof of Erdos Problem 1 (proof by GPT-6 Astra in the FrontierMath
Erdos benchmark; repository by T. Adamczewski), tadamcz/erdos1 at commit
0e395153306f34b3829d118b85bdd704136f2843, theorem Erdos1.erdos_1.disproof,
https://github.com/tadamcz/erdos1/blob/0e395153306f34b3829d118b85bdd704136f2843/Erdos1/Resolutions/Erdos1_219usd_38h.lean#L2419.
Moved from `OpenConjectures/NumberTheory/ErdosProblem1`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.ErdosProblem1Wanted
