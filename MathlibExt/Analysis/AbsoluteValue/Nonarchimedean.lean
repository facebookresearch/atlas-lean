/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Field.Ultra

/-!
# Nonarchimedean absolute values and natural-number casts

This module ports ATLAS `NumberTheoryI` Lemma 1.4 (Section 1.2,
`v1/Atlas/NumberTheoryI/targets.yaml`): an absolute value on a field is
nonarchimedean if and only if every natural-number cast has absolute value at
most `1`. The proof specializes Mathlib's norm characterizations using
`AbsoluteValue.toNormedField`.

The companion statements of Corollary 1.5 are already in MathlibExt, in
`MathlibExt/Analysis/AbsoluteValue/FiniteField.lean`
(`AbsoluteValue.isNonarchimedean_of_charP` and
`AbsoluteValue.eq_one_of_ne_zero_of_finite`), so they are not repeated here.
-/

@[expose] public section

namespace AbsoluteValue

variable {K : Type*} [Field K]

/-- An absolute value on a field is nonarchimedean if and only if every
natural-number cast has absolute value at most `1`. This is Lemma 1.4. -/
public theorem isNonarchimedean_iff_natCast_le_one (v : AbsoluteValue K ℝ) :
    IsNonarchimedean v ↔ ∀ n : ℕ, v (n : K) ≤ 1 := by
  let _ : NormedField K := v.toNormedField
  change IsNonarchimedean (norm : K → ℝ) ↔ ∀ n : ℕ, ‖(n : K)‖ ≤ 1
  exact IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.symm.trans
    isUltrametricDist_iff_forall_norm_natCast_le_one

/-- If every natural-number cast has absolute value at most `1`, then the
absolute value is nonarchimedean. This is the backward direction of
Lemma 1.4. -/
public theorem isNonarchimedean_of_natCast_le_one (v : AbsoluteValue K ℝ)
    (hv : ∀ n : ℕ, v (n : K) ≤ 1) : IsNonarchimedean v :=
  (v.isNonarchimedean_iff_natCast_le_one).mpr hv

/-- Lemma 1.4 in the book's form, with the bound required only for positive
`n` (the `n = 0` case is `v 0 = 0 ≤ 1` anyway). -/
public theorem isNonarchimedean_iff_natCast_le_one_of_pos
    (v : AbsoluteValue K ℝ) :
    IsNonarchimedean v ↔ ∀ n : ℕ, 0 < n → v (n : K) ≤ 1 := by
  rw [v.isNonarchimedean_iff_natCast_le_one]
  constructor
  · intro h n _
    exact h n
  · intro h n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [v.map_zero]
    · exact h n hn

end AbsoluteValue

end
