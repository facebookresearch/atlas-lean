/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Classical.XLinked

/-!
# Tests for X-linked allele frequency dynamics

The source example starts with `p_f = 0`, `p_m = 1`: the weighted mean is `1/3`, and the
female frequency begins `0, 1/2, 1/4`, approaching it with alternating sign in the sex
difference. Equal frequencies are fixed.
-/

@[expose] public section

open MathlibExt.Biology.PopulationGenetics.Classical.XLinked

namespace MathlibExtTest.Biology.PopulationGenetics.Classical.XLinked

-- The invariant, checked directly on the recursion.
example (pf pm : ℝ) : (2 * ((pf + pm) / 2) + pf) / 3 = (2 * pf + pm) / 3 := by ring

example : pbar (0, 1) = 1 / 3 := by norm_num [pbar]

example : step (0, 1) = (1 / 2, 0) ∧ step (step (0, 1)) = (1 / 4, 1 / 2) := by
  norm_num [step]

-- Oscillation: if `p_f(0) > p_m(0)`, the sign of `p_f - p_m` alternates every generation.
example (x : ℝ × ℝ) (h : x.1 - x.2 > 0) (t : ℕ) :
    0 < (step^[2 * t] x).1 - (step^[2 * t] x).2 ∧
      (step^[2 * t + 1] x).1 - (step^[2 * t + 1] x).2 < 0 := by
  rw [sub_iterate, sub_iterate, pow_succ, pow_mul]
  constructor
  · exact mul_pos (pow_pos (by norm_num) t) h
  · have hpos : (0 : ℝ) < ((-1 / 2) ^ 2) ^ t := pow_pos (by norm_num) t
    nlinarith

-- Equal frequencies in the sexes are a fixed point.
example (q : ℝ) : step (q, q) = (q, q) := by ext <;> simp [step]

-- Fixation boundary: `(1, 1)` and `(0, 0)` are fixed.
example : step (1, 1) = (1, 1) ∧ step (0, 0) = (0, 0) := by norm_num [step]

#print axioms fst_iterate_sub_pbar
#print axioms snd_iterate_sub_pbar
#print axioms tendsto_fst_iterate
#print axioms tendsto_snd_iterate
#print axioms sub_iterate
#print axioms pbar_iterate

end MathlibExtTest.Biology.PopulationGenetics.Classical.XLinked
