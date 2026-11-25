/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Approximation.SparseRecoveryRIP

open Finset Matrix MathlibExt.Analysis.Approximation.SparseRestrictedIsometry
  MathlibExt.Analysis.Approximation.SparseRecoveryRIPWanted

namespace MathlibExtTest.Analysis.Approximation.SparseRecoveryRIP

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m s : ℕ} {Φ : Matrix (Fin m) ι ℝ}
  {δ : ℝ} (hs : 1 ≤ s) (hΦ : HasRIP Φ (2 * s) δ) (hδ : δ < √2 - 1)
  {x xhat : ι → ℝ} (hfeas : Φ *ᵥ xhat = Φ *ᵥ x)
  (hmin : ∀ w : ι → ℝ, Φ *ᵥ w = Φ *ᵥ x → ∑ j, |xhat j| ≤ ∑ j, |w j|)
  {S : Finset ι} (hS : #S ≤ s)

-- A single omitted coefficient controls the whole recovery error.
example {k : ι} (hk : k ∉ S) (hx : ∀ j ∉ S, j ≠ k → x j = 0) :
    ∑ j, |xhat j - x j| ≤
      2 * (1 + √2 * δ / (1 - δ)) / (1 - √2 * δ / (1 - δ)) * |x k| := by
  have htail : ∑ j ∈ Sᶜ, |x j| = |x k| :=
    sum_eq_single_of_mem k (mem_compl.mpr hk) fun j hj hjk => by
      simp [hx j (mem_compl.mp hj) hjk]
  simpa only [htail] using sum_abs_sub_le_of_hasRIP hs hΦ hδ hfeas hmin hS

-- If the tail vanishes, every coordinate of the minimizer agrees with the signal.
example (hx : ∀ j ∉ S, x j = 0) : xhat = x := by
  have htail : ∑ j ∈ Sᶜ, |x j| = 0 :=
    sum_eq_zero fun j hj => by simp [hx j (mem_compl.mp hj)]
  have hbound := sum_abs_sub_le_of_hasRIP hs hΦ hδ hfeas hmin hS
  rw [htail, mul_zero] at hbound
  have hzero := hbound.antisymm (sum_nonneg fun j _ => abs_nonneg (xhat j - x j))
  funext j
  have := (sum_eq_zero_iff_of_nonneg (fun k _ => abs_nonneg (xhat k - x k))).mp hzero j (mem_univ j)
  exact sub_eq_zero.mp (abs_eq_zero.mp this)

end MathlibExtTest.Analysis.Approximation.SparseRecoveryRIP
