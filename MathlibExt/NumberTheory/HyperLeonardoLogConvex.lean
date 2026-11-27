/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HyperLeonardo
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Log-convexity and log-concavity of the hyper-Leonardo numbers at index one

Statements from Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino,
*A Note on Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48.

The first three hyper-Leonardo numbers of order `r` are `Le^{(r)}_0 = 1`, `Le^{(r)}_1 = r + 1`
and `2 Le^{(r)}_2 = r^2 + 3r + 6`, so `Le^{(r)}_0 Le^{(r)}_2 ≤ (Le^{(r)}_1)^2` amounts to
`r^2 + r ≥ 4`, which holds exactly for `r ≥ 2`; at `r = 1` the reverse inequality `4 ≤ 5` holds.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem hyperLeonardo_logConvex_logConcave_one_zero (r : ℕ) :
    hyperLeonardo r 0 = 1 := by
  induction r with
  | zero => rfl
  | succ r ih => simpa [hyperLeonardo_succ] using ih

private theorem hyperLeonardo_logConvex_logConcave_one_one (r : ℕ) :
    hyperLeonardo r 1 = r + 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [hyperLeonardo_succ, Finset.sum_range_succ, Finset.sum_range_one,
      hyperLeonardo_logConvex_logConcave_one_zero, ih]
    push_cast
    ring

private theorem hyperLeonardo_logConvex_logConcave_one_two (r : ℕ) :
    2 * hyperLeonardo r 2 = r ^ 2 + 3 * r + 6 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have h : hyperLeonardo (r + 1) 2 = hyperLeonardo r 0 + hyperLeonardo r 1 +
        hyperLeonardo r 2 := by
      rw [hyperLeonardo_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
    rw [h, hyperLeonardo_logConvex_logConcave_one_zero,
      hyperLeonardo_logConvex_logConcave_one_one]
    push_cast
    linarith

/-- **Log-convexity and log-concavity of the hyper-Leonardo numbers at index one.** The
hyper-Leonardo numbers $\mathrm{Le}^{(r)}_n$ satisfy
$\left(\mathrm{Le}^{(1)}_1\right)^2 \le \mathrm{Le}^{(1)}_0 \mathrm{Le}^{(1)}_2$, and for every
natural number $r \ge 2$ they satisfy
$\mathrm{Le}^{(r)}_0 \mathrm{Le}^{(r)}_2 \le \left(\mathrm{Le}^{(r)}_1\right)^2$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 12
(`integers-2026-A48-prop-12`). -/
theorem hyperLeonardo_logConvex_logConcave_one :
    hyperLeonardo 1 1 ^ 2 ≤ hyperLeonardo 1 0 * hyperLeonardo 1 2 ∧
      ∀ r, 2 ≤ r → hyperLeonardo r 0 * hyperLeonardo r 2 ≤ hyperLeonardo r 1 ^ 2 := by
  refine ⟨?_, fun r hr => ?_⟩
  · have h2 := hyperLeonardo_logConvex_logConcave_one_two 1
    rw [hyperLeonardo_logConvex_logConcave_one_zero, hyperLeonardo_logConvex_logConcave_one_one]
    norm_num at h2 ⊢
    linarith
  · have h2 := hyperLeonardo_logConvex_logConcave_one_two r
    rw [hyperLeonardo_logConvex_logConcave_one_zero, hyperLeonardo_logConvex_logConcave_one_one,
      one_mul]
    have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
    nlinarith

end

end MetaMathlibExt
