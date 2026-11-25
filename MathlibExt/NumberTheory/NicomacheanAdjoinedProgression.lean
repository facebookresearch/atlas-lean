/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.NumberTheory.NicomacheanTranslations
import Mathlib.Tactic.LinearCombination

/-!
# Adjoined Nicomachean sequences

If adjoining each successive term preserves zero Nicomachean defect, the adjoined terms
form a progression with difference one from the second term, provided the terms are nonzero
and consecutive terms are never negatives of one another.
-/

namespace MetaMathlibExt

/-- **Adjoined Nicomachean sequences are eventually arithmetic progressions.** Write
$\nu(a_1, \dots, a_n) = (a_1 + \dots + a_n)^2 - (a_1^3 + \dots + a_n^3)$ for the Nicomachean defect
of a finite sequence. Let $(a_1, \dots, a_n)$ be a finite, possibly empty, sequence of real numbers
and let $x_1, x_2, x_3, \dots$ be nonzero real numbers with $x_{j+1} \ne -x_j$ for every $j \ge 1$.
If $\nu(a_1, \dots, a_n, x_1, \dots, x_l) = 0$ for every $l \ge 1$, then $x_{j+1} = x_j + 1$ for
every $j \ge 2$; that is, $x_2, x_3, \dots$ is an arithmetic progression with difference $1$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 8
(`jis-2024-24.6.3-prop-8`). -/
public theorem nicomachean_adjoined_arithmeticProgression (a : List ℝ) (x : ℕ → ℝ)
    (hx : ∀ j, x j ≠ 0) (hneg : ∀ j, x (j + 1) ≠ -x j)
    (hν : ∀ l, nicomacheanNu (a ++ (List.range (l + 1)).map x) = 0) :
    ∀ j, 1 ≤ j → x (j + 1) = x j + 1 := by
  let p (n : ℕ) := a ++ (List.range n).map x
  have hp (n : ℕ) : p (n + 1) = p n ++ [x n] := by
    simp only [p, List.range_succ (n := n), List.map_append, List.map_singleton,
      List.append_assoc]
  -- Subtract the defects of two successive prefixes and cancel the nonzero new term.
  have hsquare (n : ℕ) (hn : 1 ≤ n) : x n ^ 2 = x n + 2 * (p n).sum := by
    have hprev : nicomacheanNu (p n) = 0 := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      exact hν m
    have hnext : nicomacheanNu (p (n + 1)) = 0 := hν n
    rw [hp] at hnext
    simp only [nicomacheanNu, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton] at hprev hnext
    have hfactor : x n * (x n ^ 2 - (x n + 2 * (p n).sum)) = 0 := by
      linear_combination hprev - hnext
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left (hx n))
  intro j hj
  have hprev := hsquare j hj
  have hnext := hsquare (j + 1) (Nat.le_succ_of_le hj)
  rw [hp, List.sum_append, List.sum_singleton] at hnext
  have hfactor : (x (j + 1) + x j) * (x (j + 1) - (x j + 1)) = 0 := by
    linear_combination hnext - hprev
  have hsum : x (j + 1) + x j ≠ 0 := fun h => hneg j (eq_neg_of_add_eq_zero_left h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hsum)

end MetaMathlibExt
