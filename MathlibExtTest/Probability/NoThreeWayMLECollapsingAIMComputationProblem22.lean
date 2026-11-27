/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.NoThreeWayMLECollapsingAIMComputationProblem22
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for MLE existence and binary collapsing

These examples compute a binary collapsing, exhibit a positive table with the prescribed
margins, rule out a positive witness for a zero margin, and derive a detector corollary.

Source: AIM workshop Computational algebraic statistics, problem list, Conjecture 8 and
N. Eriksson, S. E. Fienberg, A. Rinaldo and S. Sullivant, *Polyhedral conditions for the
nonexistence of the MLE for hierarchical log-linear models*, J. Symbolic Comput. 41 (2006),
222-233, DOI 10.1016/j.jsc.2005.04.003, arXiv:math/0405044.
-/

namespace MathlibExtTest.Probability.NoThreeWayMLECollapsingAIMComputationProblem22

open MathlibExt.Probability.NoThreeWayMLECollapsingAIMComputationProblem22Wanted
open Function

example :
    collapse ![0, 0, 1] ![0, 1, 1] ![1, 0, 1]
      (fun i j k : Fin 3 => 9 * i.val + 3 * j.val + k.val + 1) 0 1 1 = 88 ∧
    collapse ![0, 0, 1] ![0, 1, 1] ![1, 0, 1]
      (fun i j k : Fin 3 => 9 * i.val + 3 * j.val + k.val + 1) 1 0 0 = 20 := by
  decide

example : MLEExists (fun _ _ _ : Fin 2 => 1) := by
  refine ⟨fun _ _ _ => 1, ?_, ?_, ?_, ?_⟩
  · intro i j k
    norm_num
  · intro i j
    norm_num [Fin.sum_univ_two]
  · intro i k
    norm_num [Fin.sum_univ_two]
  · intro j k
    norm_num [Fin.sum_univ_two]

example : ¬ MLEExists (fun i j _ : Fin 2 => if i = 0 ∧ j = 0 then 0 else 1) := by
  rintro ⟨m, hp, hij, _, _⟩
  have h := hij 0 0
  norm_num [Fin.sum_univ_two] at h
  linarith only [h, hp 0 0 0, hp 0 0 1]

example : ¬ ∃ detector : (Fin 3 → Fin 3 → Fin 3 → ℕ) → Bool,
    (∀ n, detector n = true ↔ ¬ MLEExists n) ∧
    (∀ n, detector n = true ↔ ∃ (a b c : Fin 3 → Fin 2),
      Surjective a ∧ Surjective b ∧ Surjective c ∧ ¬ MLEExists (collapse a b c n)) := by
  rintro ⟨detector, hmle, hcollapse⟩
  apply mleNonexistenceDetectedByCollapsing333_refuted
  intro n
  exact (hmle n).symm.trans (hcollapse n)

end MathlibExtTest.Probability.NoThreeWayMLECollapsingAIMComputationProblem22
