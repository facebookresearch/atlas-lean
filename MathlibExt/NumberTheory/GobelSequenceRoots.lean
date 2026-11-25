/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GobelSequence
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Strict decrease of the normalized Göbel roots

For positive indices, the normalized roots of a $(k,l)$-Göbel sequence with $k,l ≥ 2$
decrease strictly and stay above one.
-/

namespace MetaMathlibExt

namespace gobelSequence_root_strictAnti

-- The recurrence expresses the next term as a weighted average of the term and its power.
private theorem step_bounds {k l n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n)
    (hg : 1 < gobelSequence k l n) :
    gobelSequence k l n < gobelSequence k l (n + 1) ∧
      gobelSequence k l (n + 1) < gobelSequence k l n ^ k := by
  have hpow := lt_self_pow₀ hg hk
  have hrec := gobelSequence_succ k l n hn
  rw [mul_add, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k),
    mul_comm (gobelSequence k l n) (n : ℚ)] at hrec
  have hn' : 0 < (n : ℚ) := Nat.cast_pos.mpr hn
  constructor <;> apply (mul_lt_mul_iff_right₀ (show 0 < (n : ℚ) + 1 by positivity)).mp
  · rw [hrec, add_mul, one_mul]
    gcongr
  · rw [hrec, add_mul, one_mul]
    gcongr

end gobelSequence_root_strictAnti

/-- **Strict decrease of the normalized Göbel roots.** Let $k, l \ge 2$ be natural numbers, let
$g_{k,l}$ be the $(k, l)$-Göbel sequence, and let $C_{k,l}(n) = g_{k,l}(n)^{1/k^n}$, a real
number. Then $C_{k,l}(n) > C_{k,l}(n + 1) > 1$ for every natural number $n \ge 1$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 7 (`jis-2024-24.8.1-lem-7`). -/
public theorem gobelSequence_root_strictAnti (k l n : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (hn : 1 ≤ n) :
    (gobelSequence k l (n + 1) : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ (n + 1))
        < (gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n) ∧
      1 < (gobelSequence k l (n + 1) : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ (n + 1)) := by
  have hg : 1 < gobelSequence k l n := by
    induction n, hn using Nat.le_induction with
    | base =>
      rw [gobelSequence_one]
      exact_mod_cast (show 1 < l from hl)
    | succ m hm ih => exact ih.trans (gobelSequence_root_strictAnti.step_bounds hk hm ih).1
  obtain ⟨hincr, hlt⟩ := gobelSequence_root_strictAnti.step_bounds hk hn hg
  have hg' : (1 : ℝ) < gobelSequence k l n := by exact_mod_cast hg
  have hnext : (1 : ℝ) < gobelSequence k l (n + 1) := by exact_mod_cast hg.trans hincr
  have hpow : (gobelSequence k l (n + 1) : ℝ) < (gobelSequence k l n : ℝ) ^ k := by
    exact_mod_cast hlt
  have hk' : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hexp : 0 < (1 : ℝ) / (k : ℝ) ^ (n + 1) := by positivity
  refine ⟨?_, Real.one_lt_rpow hnext hexp⟩
  calc
    _ < ((gobelSequence k l n : ℝ) ^ k) ^ ((1 : ℝ) / (k : ℝ) ^ (n + 1)) :=
      Real.rpow_lt_rpow (zero_le_one.trans hnext.le) hpow hexp
    _ = _ := by
      rw [← Real.rpow_natCast_mul (zero_le_one.trans hg'.le)]
      congr 1
      rw [pow_succ]
      field_simp

end MetaMathlibExt
