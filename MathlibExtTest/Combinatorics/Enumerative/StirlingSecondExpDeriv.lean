/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StirlingSecondExpDeriv

namespace MetaMathlibExt

-- The empty power leaves the exponential, including the zeroth derivative at v = 0.
example (r v : ℕ) :
    iteratedDeriv r (fun x : ℝ => (1 - Real.exp x) ^ 0 * Real.exp (v * x)) 0 = (v : ℝ) ^ r := by
  rw [(iteratedDeriv_one_sub_exp_pow 0 r v).2.1]
  simp

-- All derivative orders below the multiplicity of the zero vanish.
example {k r : ℕ} (h : r < k) :
    iteratedDeriv r (fun x : ℝ => (1 - Real.exp x) ^ k) 0 = 0 := by
  obtain ⟨hderiv, hsum⟩ := (iteratedDeriv_one_sub_exp_pow k r 0).1
  simpa [Nat.stirlingSecond_eq_zero_of_lt h] using hderiv.trans hsum

-- The second derivative of exp(2x) - exp(3x) at zero is 4 - 9.
example :
    iteratedDeriv 2 (fun x : ℝ => (1 - Real.exp x) * Real.exp (2 * x)) 0 = -5 := by
  have h := (iteratedDeriv_one_sub_exp_pow 1 2 2).2.1
  norm_num [Finset.sum_range_succ] at h
  exact h

end MetaMathlibExt
