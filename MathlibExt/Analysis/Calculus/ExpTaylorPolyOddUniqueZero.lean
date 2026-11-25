/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_19.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029), by L. Pu et al. The main theorem's statement and
informal description are adapted from that problem, distributed under the MIT License.

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
module

public import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Real zeros of odd exponential Taylor polynomials

An even truncation is positive term by term on positive inputs. On negative inputs it lies
above the exponential by Taylor's remainder formula. Each odd truncation therefore has a
positive derivative. The same remainder formula gives a nonpositive value at `-(n + 1)!`,
so the intermediate value theorem gives a zero between that point and zero.
-/

namespace MathlibExt.Analysis.Calculus.ExpTaylorPolyOddUniqueZeroWanted

open Finset Set

private noncomputable def partialSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), x ^ k / k.factorial

private theorem exp_sub_partialSum (n : ℕ) {x : ℝ} (hx : x < 0) :
    ∃ c ∈ Ioo x 0,
      Real.exp x - partialSum n x = Real.exp c * x ^ (n + 1) / (n + 1).factorial := by
  obtain ⟨c, hc, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := n) hx.ne'
    Real.contDiff_exp.contDiffOn
  have hd (k : ℕ) : iteratedDerivWithin k Real.exp (uIcc 0 x) 0 = 1 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx.ne')
      Real.contDiff_exp.contDiffAt left_mem_uIcc, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
      Real.exp_zero]
  refine ⟨c, by simpa [uIoo_of_ge hx.le] using hc, ?_⟩
  simpa [taylor_within_apply, hd, partialSum, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    div_eq_mul_inv, mul_comm] using h

private theorem hasDerivAt_partialSum_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (partialSum (n + 1)) (partialSum n x) x := by
  have h (y : ℝ) : partialSum (n + 1) y =
      (∑ k ∈ range (n + 1), y ^ (k + 1) / (k + 1).factorial) + 1 := by
    rw [partialSum, sum_range_succ']
    simp
  rw [funext h]
  apply HasDerivAt.add_const
  apply HasDerivAt.fun_sum
  intro k _
  apply ((hasDerivAt_pow (k + 1) x).div_const ((k + 1).factorial : ℝ)).congr_deriv
  simp [Nat.factorial_succ, field]

private theorem partialSum_pos_of_odd_succ (n : ℕ) (hn : Odd (n + 1)) (x : ℝ) :
    0 < partialSum n x := by
  by_cases hx : x < 0
  · obtain ⟨c, _, hc⟩ := exp_sub_partialSum n hx
    have hs := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos c).le (hn.pow_nonpos hx.le))
      (Nat.cast_nonneg (n + 1).factorial : (0 : ℝ) ≤ _)
    exact (Real.exp_pos x).trans_le (sub_nonpos.mp (hc.trans_le hs))
  · have hx' := le_of_not_gt hx
    apply Finset.sum_pos' (fun k _ ↦ div_nonneg (pow_nonneg hx' k) (Nat.cast_nonneg _))
    exact ⟨0, by simp, by simp⟩

private theorem exists_nonpos (n : ℕ) (hn : Odd n) : ∃ x, partialSum n x ≤ 0 := by
  let a : ℝ := (n + 1).factorial
  have ha : 1 ≤ a := by
    dsimp [a]
    exact_mod_cast (Nat.factorial_pos (n + 1) : 1 ≤ (n + 1).factorial)
  obtain ⟨c, hc, h⟩ := exp_sub_partialSum n (x := -a) (by linarith)
  rw [(hn.add_odd odd_one).neg_pow] at h
  have hp : a ≤ a ^ (n + 1) := le_self_pow₀ ha (Nat.succ_ne_zero n)
  have he : Real.exp (-a) ≤ Real.exp c := Real.exp_le_exp.mpr hc.1.le
  have hle : Real.exp (-a) ≤ Real.exp c * a ^ (n + 1) / a := by
    apply (le_div_iff₀ (by linarith : 0 < a)).mpr
    exact mul_le_mul he hp (by linarith) (Real.exp_pos c).le
  exact ⟨-a, by linarith⟩

/-- **Odd Taylor polynomials of the exponential have exactly one real zero.** For every odd
positive integer $n$, the polynomial $1+x+x^2/2!+\cdots+x^n/n!$ has exactly one real zero.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Polynomials,
rational functions in real analysis), `benchmark/level1/ma_proofbench_l1_19.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem existsUnique_sum_pow_div_factorial_eq_zero_of_odd
    (n : ℕ) (hnpos : 0 < n) (hnodd : Odd n) :
    ∃! x : ℝ, (∑ k ∈ Finset.range (n + 1), x ^ k / (Nat.factorial k)) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
  have hmono := strictMono_of_hasDerivAt_pos (hasDerivAt_partialSum_succ m)
    (partialSum_pos_of_odd_succ m hnodd)
  obtain ⟨a, ha⟩ := exists_nonpos (m + 1) hnodd
  have hcont : Continuous (partialSum (m + 1)) :=
    continuous_iff_continuousAt.mpr fun x ↦ (hasDerivAt_partialSum_succ m x).continuousAt
  obtain ⟨x, hx⟩ := intermediate_value_univ a 0 hcont (show 0 ∈ Set.Icc _ _ from
    ⟨ha, by simp [partialSum, sum_range_succ']⟩)
  exact ⟨x, hx, fun y hy ↦ hmono.injective (hy.trans hx.symm)⟩

end MathlibExt.Analysis.Calculus.ExpTaylorPolyOddUniqueZeroWanted
