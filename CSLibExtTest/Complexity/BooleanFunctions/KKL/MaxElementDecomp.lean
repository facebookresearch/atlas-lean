/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.MaxElementDecomp
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.FSPerEdge

/-!
# Tests for the maximal-element decomposition of the variance

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.MaxElementDecomp` on `{0, 1}^Bool` (ordered
by `false < true`):

* `mxd_maxE` on the nonempty subsets of `Bool`, and the fibers `mxd_fiber false = {{false}}`,
  `mxd_fiber true = {{true}, {true, false}}`;
* `mxd_fiberWeight` of `AND` under `μ_p` is `p³(1-p)` at `false` and `p³(1-p) + p²(1-p)²` at
  `true`, and `mxd_var_decomp` reproduces `Var_p(AND) = p²(1-p²)`;
* `mxd_logSum_gain` instantiated at `p = 3/4`, `q = 2`, `ρ = √3/2` with its positivity
  hypotheses discharged from explicit values, and `mxd_martingaleHC_c0`;
* `mxd_martingaleHC_statement q` is proved here for no `q > 1/2`; it holds for `q ≤ 1/2` because
  `(1/2, q)` is empty, and `mxd_rhoOptimise_of_martingaleHC` transfers it to `ptn_RhoOptimise`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

lemma mxd_maxE_singleton (b : Bool) : mxd_maxE ({b} : Finset Bool) = b := by
  simp [mxd_maxE]

lemma mxd_maxE_pair : mxd_maxE ({true, false} : Finset Bool) = true := by
  simp [mxd_maxE]

lemma mxd_fiber_false : mxd_fiber false = {{false}} := by
  rw [mxd_fiber, univ_finset_bool]
  ext S
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hne, rfl | rfl | rfl | rfl⟩, h⟩
    · exact absurd rfl hne
    · simp [mxd_maxE_singleton] at h
    · rfl
    · simp [mxd_maxE_pair] at h
  · rintro rfl
    exact ⟨⟨by decide, by simp⟩, mxd_maxE_singleton false⟩

lemma mxd_fiber_true : mxd_fiber true = {{true}, {true, false}} := by
  rw [mxd_fiber, univ_finset_bool]
  ext S
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hne, rfl | rfl | rfl | rfl⟩, h⟩
    · exact absurd rfl hne
    · simp
    · simp [mxd_maxE_singleton] at h
    · simp
  · rintro (rfl | rfl)
    · exact ⟨⟨by decide, by simp⟩, mxd_maxE_singleton true⟩
    · exact ⟨⟨by decide, by simp⟩, mxd_maxE_pair⟩

lemma mxd_fiberWeight_andFun {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    mxd_fiberWeight p andFun false = p ^ 3 * (1 - p) ∧
      mxd_fiberWeight p andFun true = p ^ 3 * (1 - p) + p ^ 2 * (1 - p) ^ 2 := by
  constructor
  · rw [mxd_fiberWeight, mxd_fiber_false, Finset.sum_singleton]
    exact ptn_coeff_andInd_false_sq hp0 hp1
  · rw [mxd_fiberWeight, mxd_fiber_true, Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [ptn_coeff_andInd_true_sq hp0 hp1, ptn_coeff_andInd_univ_sq hp0 hp1]

/-- `mxd_var_decomp` at `AND`: `p²(1-p²) = p³(1-p) + (p³(1-p) + p²(1-p)²)`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    p ^ 2 * (1 - p ^ 2) = p ^ 3 * (1 - p) + (p ^ 3 * (1 - p) + p ^ 2 * (1 - p) ^ 2) := by
  have h := mxd_var_decomp hp0 hp1 andFun
  rw [var_andInd, Fintype.sum_bool, (mxd_fiberWeight_andFun hp0 hp1).1,
    (mxd_fiberWeight_andFun hp0 hp1).2] at h
  linarith

example :
    var (bernoulliWeight (3 / 4)) andInd
        * Real.log (var (bernoulliWeight (3 / 4)) andInd
          / ((Real.sqrt 3 / 2) ^ 2 * (ptn_sigma (3 / 4)) ^ 2
            * ((maxInfl (bernoulliWeight (3 / 4)) andInd) ^ (2 / 2 - 1 : ℝ)
              * totalInfl (bernoulliWeight (3 / 4)) andInd)))
      ≤ ∑ e ∈ Finset.univ.filter (fun e : Bool => 0 < mxd_fiberWeight (3 / 4) andFun e),
        mxd_fiberWeight (3 / 4) andFun e
          * Real.log (mxd_fiberWeight (3 / 4) andFun e / mxd_dampFiber (3 / 4) (Real.sqrt 3 / 2)
            andFun e) :=
  mxd_logSum_gain (by norm_num) (by norm_num) (by positivity) rho_le_one (by norm_num) le_rfl
    rho_sq andFun (by rw [var_andInd]; norm_num) (by rw [maxInfl_andInd_p]; norm_num)
    (by rw [totalInfl_andInd_p]; norm_num)

example (u : ℝ) :
    (∑ S : Finset Bool, (0 : ℝ) * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff (3 / 4) andInd S) ^ 2)
      ≤ (maxInfl (bernoulliWeight (3 / 4)) andInd) ^ (u / (2 - u))
        * totalInfl (bernoulliWeight (3 / 4)) andInd :=
  mxd_martingaleHC_c0 (by norm_num) (by norm_num) andFun u

/-- `mxd_martingaleHC_statement q` for `q ≤ 1/2` holds vacuously. -/
lemma mxd_martingaleHC_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : mxd_martingaleHC_statement q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : ptn_RhoOptimise (1 / 2) :=
  mxd_rhoOptimise_of_martingaleHC (mxd_martingaleHC_of_le_half le_rfl)

end StatMechTest.BooleanFunctions
