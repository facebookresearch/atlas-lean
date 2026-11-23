/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Series.TwoAdicNonmultiples

/-!
# Tests for regrouping the non-multiples of a power of two
-/

namespace MetaMathlibExt.tsum_twoAdic_low_regroup

-- At cutoff zero, the empty exponent range gives the empty sum for every sequence.
example (c : ℕ → ℂ) : (∑' p : {p : ℕ // 0 < p ∧ ¬ 2 ^ 0 ∣ p}, c p) = 0 := by
  rw [← tsum_twoAdic_low_regroup 0 c]
  exact tsum_empty

-- At cutoff two the term at 6 contributes once, while the term at 4 is excluded.
example :
    (∑' x : Fin 2 × ℕ, if (2 * x.2 + 1) * 2 ^ (x.1 : ℕ) ∈ ({4, 6} : Finset ℕ)
      then (1 : ℂ) else 0) = 1 := by
  let c (p : ℕ) : ℂ := if p ∈ ({4, 6} : Finset ℕ) then 1 else 0
  rw [tsum_twoAdic_low_regroup 2 c]
  let six : {p : ℕ // 0 < p ∧ ¬ 2 ^ 2 ∣ p} := ⟨6, by decide⟩
  have h (p : {p : ℕ // 0 < p ∧ ¬ 2 ^ 2 ∣ p}) : c p = if p = six then 1 else 0 := by
    have hfour : (p : ℕ) ≠ 4 := by
      intro heq
      exact p.2.2 (heq ▸ by decide)
    simp [c, six, hfour, Subtype.ext_iff]
  simp_rw [h]
  exact tsum_ite_eq _ _

end MetaMathlibExt.tsum_twoAdic_low_regroup
