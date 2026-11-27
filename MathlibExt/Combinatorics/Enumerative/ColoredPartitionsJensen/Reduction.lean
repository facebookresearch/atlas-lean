/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`PartitionsJensen/Reduction.lean`
(ChironTheCentaur/rh-lab-partitions-jensen, commit 57beb8dbff7b84e125931fe2e53080f325f4f108):
Copyright (c) 2026 Sky (GitHub: ChironTheCentaur). All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Sky (GitHub: ChironTheCentaur)
-/

module

public import MathlibExt.Combinatorics.Enumerative.ColoredPartitionsJensen.Bridge
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.IntervalCases

/-!
# The log-ratio expansion from finite differences

The log-ratio expansion only looks at `j = 0, …, d`, and on those points every function of `j` is a
polynomial of degree `≤ d` in `j` (Gregory–Newton). So it holds with **zero** interpolation
error as soon as the forward differences of `L n = log α(n)` have the right sizes:

* `hasLogRatioExpansion_of_fwdDiff`: `δ → 0`, `δ > 0` eventually,
  `Δ²L(n) + 2 δ(n)² = o(δ(n)²)` and `Δ^k L(n) = o(δ(n)^k)` for `3 ≤ k ≤ d` give
  `HasLogRatioExpansion α d` (`2 ≤ d`; `d ≤ 1` is `hasLogRatioExpansion_of_le_one`).
* `exists_fwdDiff_iter_eq_iteratedDeriv`: `Δ^k f(x) = f^{(k)}(ξ)` for some
  `ξ ∈ [x, x + k]` (mean value form of the `k`-th difference), `f` of class `C^k` on `ℝ`.
* `hasLogRatioExpansion_of_smooth_model`: if `log α(n) = Λ(n) + ε(n)` with
  `|Λ^{(k)}(x)| ≤ C x^{β−k}` (`2 ≤ k ≤ d`), `Λ''(x) ≤ −c x^{β−2}`, `0 < β < 2`, and
  `ε(n) = o(n^{(β−2)d/2})`, then `HasLogRatioExpansion α d`.
-/

open Polynomial Finset Filter Topology Asymptotics
open scoped fwdDiff Nat

namespace MetaMathlibExt.ColoredPartitionsJensen

@[expose] public section

/-! ### Gregory–Newton interpolation on `0, …, d` -/

/-- The Newton interpolant of `j ↦ L(n+j) − L(n)` on `0, …, d`, as a polynomial in `j`. -/
noncomputable def newtonPoly (L : ℕ → ℝ) (d n : ℕ) : ℝ[X] :=
  ∑ k ∈ Icc 1 d, C ((fwdDiff 1)^[k] L n / (k ! : ℝ)) * descPochhammer ℝ k

theorem eval_descPochhammer_div (j k : ℕ) :
    (descPochhammer ℝ k).eval (j : ℝ) / (k ! : ℝ) = (j.choose k : ℝ) := by
  rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

theorem Icc_one_eq_map (d : ℕ) : Icc 1 d = (range d).map ⟨(· + 1), add_left_injective 1⟩ := by
  ext k
  simp only [mem_Icc, Finset.mem_map, mem_range, Function.Embedding.coeFn_mk]
  constructor
  · intro h; exact ⟨k - 1, by omega, by omega⟩
  · rintro ⟨a, ha, rfl⟩; omega

/- Gregory–Newton: for `j ≤ d`, `L(n+j) − L(n)` is the Newton interpolant at `j`. -/
private theorem eval_newtonPoly (L : ℕ → ℝ) {d j : ℕ} (hj : j ≤ d) (n : ℕ) :
    (newtonPoly L d n).eval (j : ℝ) = L (n + j) - L n := by
  have hN := shift_eq_sum_fwdDiff_iter (1 : ℕ) L j n
  simp only [smul_eq_mul, mul_one, nsmul_eq_mul] at hN
  have hext : ∑ k ∈ range (j + 1), (j.choose k : ℝ) * (fwdDiff 1)^[k] L n =
      ∑ k ∈ range (d + 1), (j.choose k : ℝ) * (fwdDiff 1)^[k] L n := by
    refine sum_subset (range_subset_range.2 (by omega)) fun k _ hk => ?_
    rw [mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  rw [hN, hext, sum_range_succ', Nat.choose_zero_right, Nat.cast_one, one_mul,
    Function.iterate_zero, id, add_sub_cancel_right, newtonPoly, eval_finsetSum]
  rw [Icc_one_eq_map, sum_map]
  refine sum_congr rfl fun k _ => ?_
  simp only [Function.Embedding.coeFn_mk, eval_mul, eval_C]
  rw [← eval_descPochhammer_div j (k + 1)]
  ring

theorem natDegree_newtonPoly_le (L : ℕ → ℝ) (d n : ℕ) : (newtonPoly L d n).natDegree ≤ d :=
  natDegree_sum_le_of_forall_le _ _ fun k hk =>
    (natDegree_C_mul_le _ _).trans ((descPochhammer_natDegree ℝ k).le.trans (mem_Icc.1 hk).2)

theorem coeff_zero_newtonPoly (L : ℕ → ℝ) (d n : ℕ) : (newtonPoly L d n).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, newtonPoly, eval_finsetSum]
  refine sum_eq_zero fun k hk => ?_
  rw [eval_mul, descPochhammer_eval_zero, ite_eq_right (by rw [mem_Icc] at hk; omega), mul_zero]

theorem coeff_newtonPoly (L : ℕ → ℝ) (d n i : ℕ) :
    (newtonPoly L d n).coeff i =
      ∑ k ∈ Icc 1 d, (fwdDiff 1)^[k] L n * ((descPochhammer ℝ k).coeff i / (k ! : ℝ)) := by
  rw [newtonPoly, finsetSum_coeff]
  refine sum_congr rfl fun k _ => ?_
  rw [coeff_C_mul]
  ring

theorem coeff_descPochhammer_of_lt {k i : ℕ} (h : k < i) : (descPochhammer ℝ k).coeff i = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [descPochhammer_natDegree]; exact h)

/- `δ^k = O(δ^i)` for `i ≤ k` when `δ → 0`. -/
private theorem isBigO_pow_pow_of_le {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) {i k : ℕ} (h : i ≤ k)
    :
    (fun n => δ n ^ k) =O[atTop] (fun n => δ n ^ i) := by
  have h1 : (fun n => δ n ^ (k - i)) =O[atTop] (fun _ => (1 : ℝ)) := by
    have : Tendsto (fun n => δ n ^ (k - i)) atTop (𝓝 (0 ^ (k - i))) := hδ.pow _
    exact this.isBigO_one ℝ
  refine (h1.mul (isBigO_refl (fun n => δ n ^ i) atTop)).congr' ?_ ?_
  · exact Eventually.of_forall fun n => by
      simp only; rw [← pow_add, Nat.sub_add_cancel h]
  · exact Eventually.of_forall fun n => one_mul _

/- **Interpolation step.** Finite-difference bounds on `L = log α` give the GORZ
log-ratio expansion. The second difference fixes `δ` (`Δ²L ≈ −2δ²`), the higher ones are
`o(δ^k)`, and
the Newton interpolant on `0, …, d` matches `log(α(n+j)/α(n))` exactly. -/
private theorem hasLogRatioExpansion_of_fwdDiff {α : ℕ → ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hα : ∀ᶠ n in atTop, 0 < α n) {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (h2 : (fun n => (fwdDiff 1)^[2] (fun m => Real.log (α m)) n + 2 * δ n ^ 2) =o[atTop]
      (fun n => δ n ^ 2))
    (hk : ∀ k ∈ Icc 3 d, (fun n => (fwdDiff 1)^[k] (fun m => Real.log (α m)) n) =o[atTop]
      (fun n => δ n ^ k)) :
    HasLogRatioExpansion α d := by
  set L : ℕ → ℝ := fun m => Real.log (α m) with hL
  -- patch `δ` to be positive everywhere
  set δ₁ : ℕ → ℝ := fun n => if 0 < δ n then δ n else 1 with hδ₁def
  have hδe : δ₁ =ᶠ[atTop] δ := hδpos.mono fun n hn => by simp only [hδ₁def, ite_eq_left hn]
  have hδe' : ∀ i, (fun n => δ₁ n ^ i) =ᶠ[atTop] (fun n => δ n ^ i) := fun i =>
    hδe.mono fun n hn => by simp only [hn]
  have hδ₁ : Tendsto δ₁ atTop (𝓝 0) := hδ.congr' hδe.symm
  have hδ₁pos : ∀ n, 0 < δ₁ n := fun n => by
    simp only [hδ₁def]; split_ifs with h
    · exact h
    · exact one_pos
  -- `F k` is `o(δ^k)` for every `2 ≤ k ≤ d`
  set F : ℕ → ℕ → ℝ := fun k n => (fwdDiff 1)^[k] L n + (if k = 2 then 2 * δ₁ n ^ 2 else 0) with hF
  have hFo : ∀ k ∈ Icc 2 d, (fun n => F k n) =o[atTop] (fun n => δ₁ n ^ k) := by
    intro k hkd
    rcases (show k = 2 ∨ 3 ≤ k by rw [mem_Icc] at hkd; omega) with rfl | h3
    · refine h2.congr' ?_ (hδe' 2).symm
      filter_upwards [hδe] with n hn
      simp [hF, hn]
    · refine ((hk k (mem_Icc.2 ⟨h3, (mem_Icc.1 hkd).2⟩)).congr' ?_ (hδe' k).symm)
      exact Eventually.of_forall fun n => by
        simp only [hF, ite_eq_right (by omega : k ≠ 2), add_zero]
  set R := newtonPoly L d with hR
  set g : ℕ → ℕ → ℝ := fun i n => if i = 1 then 0 else
    (R n).coeff i + (if i = 2 then δ₁ n ^ 2 else 0) with hg
  -- the coefficients `g i` as sums of the `F k`
  have hgF : ∀ i, 2 ≤ i → ∀ n, g i n =
      ∑ k ∈ Icc 1 d, (if 2 ≤ k then F k n else 0) * ((descPochhammer ℝ k).coeff i / (k ! : ℝ)) := by
    intro i hi n
    have h1 : ∀ k ∈ Icc 1 d, (fwdDiff 1)^[k] L n * ((descPochhammer ℝ k).coeff i / (k ! : ℝ)) =
        (if 2 ≤ k then F k n else 0) * ((descPochhammer ℝ k).coeff i / (k ! : ℝ)) -
          (if k = 2 then 2 * δ₁ n ^ 2 else 0) * ((descPochhammer ℝ k).coeff i / (k ! : ℝ)) := by
      intro k hk
      by_cases hk2 : 2 ≤ k
      · simp only [hF, ite_eq_left hk2]; ring
      · have hk1 : k = 1 := by rw [mem_Icc] at hk; omega
        subst hk1
        rw [coeff_descPochhammer_of_lt (by omega)]
        simp
    simp only [hg, ite_eq_right (by omega : i ≠ 1), hR, coeff_newtonPoly, sum_congr rfl h1,
      sum_sub_distrib]
    have h2' : ∑ k ∈ Icc 1 d, (if k = 2 then 2 * δ₁ n ^ 2 else 0) *
        ((descPochhammer ℝ k).coeff i / (k ! : ℝ)) =
        2 * δ₁ n ^ 2 * ((descPochhammer ℝ 2).coeff i / (2 ! : ℝ)) := by
      rw [Finset.sum_eq_single_of_mem 2 (mem_Icc.2 ⟨by norm_num, hd⟩)
        (fun k _ hk => by simp [hk])]
      simp
    rw [h2']
    by_cases hi2 : i = 2
    · subst hi2
      have hc : (descPochhammer ℝ 2).coeff 2 = 1 := by
        have := (monic_descPochhammer ℝ 2).coeff_natDegree
        rwa [descPochhammer_natDegree] at this
      rw [ite_eq_left rfl, hc]
      norm_num [Nat.factorial]
      ring
    · rw [ite_eq_right hi2, coeff_descPochhammer_of_lt (by omega)]
      ring
  refine hasLogRatioExpansion_of_Icc_one (A := fun n => (R n).coeff 1) hδ₁ hδ₁pos (g := g)
    (fun i hi => ?_) (fun j hj => ?_)
  · -- `g i = o(δ^i)`
    by_cases hi1 : i = 1
    · subst hi1; simp only [hg, ite_true]; exact isLittleO_zero _ _
    have hi2 : 2 ≤ i := by rw [mem_Icc] at hi; omega
    simp only [hgF i hi2]
    apply IsLittleO.fun_sum
    intro k hk
    by_cases hki : i ≤ k
    · have hk2 : 2 ≤ k := le_trans hi2 hki
      simp only [ite_eq_left hk2]
      exact ((hFo k (mem_Icc.2 ⟨hk2, (mem_Icc.1 hk).2⟩)).trans_isBigO
        (isBigO_pow_pow_of_le hδ₁ hki)).mul_isBigO (isBigO_const_const _ one_ne_zero _)
        |>.congr_right fun _ => mul_one _
    · rw [not_le] at hki
      simp only [coeff_descPochhammer_of_lt hki, zero_div, mul_zero]
      exact isLittleO_zero _ _
  · -- the error is eventually zero
    refine (isLittleO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [hα, (tendsto_add_atTop_nat j).eventually hα] with n hn hnj
    have he := eval_newtonPoly L hj n
    rw [eval_eq_sum_range' (n := d + 1) (by have := natDegree_newtonPoly_le L d n; omega),
      sum_range_succ', coeff_zero_newtonPoly, zero_mul, add_zero] at he
    have hI : ∑ i ∈ Icc 1 d, g i n * (j : ℝ) ^ i =
        ∑ i ∈ range d, g (i + 1) n * (j : ℝ) ^ (i + 1) := by
      rw [Icc_one_eq_map, sum_map]; rfl
    have hsplit : ∀ m : ℕ, 1 ≤ m → ∑ i ∈ range m, g (i + 1) n * (j : ℝ) ^ (i + 1) =
        ∑ i ∈ range m, (R n).coeff (i + 1) * (j : ℝ) ^ (i + 1) - (R n).coeff 1 * j +
          (if 2 ≤ m then δ₁ n ^ 2 * (j : ℝ) ^ 2 else 0) := by
      intro m hm
      induction m with
      | zero => omega
      | succ m ih =>
        rcases Nat.eq_zero_or_pos m with rfl | hm0
        · simp [hg]
        · rw [sum_range_succ, ih hm0, sum_range_succ]
          simp only [hg, ite_eq_right (by omega : m + 1 ≠ 1)]
          by_cases hm1 : m = 1
          · subst hm1; norm_num; ring
          · rw [ite_eq_right (by omega : m + 1 ≠ 2), ite_eq_left (by omega : 2 ≤ m),
              ite_eq_left (by omega : 2 ≤ m + 1)]
            ring
    rw [hI, hsplit d (by omega), ite_eq_left hd]
    change (0 : ℝ) = Real.log (α (n + j) / α n) - _
    rw [Real.log_div hnj.ne' hn.ne']
    simp only [hL] at he
    rw [← he]
    ring

/-! ### Mean value form of the `k`-th difference -/

/-- `Δ^k f(x) = f^{(k)}(ξ)` for some `ξ ∈ [x, x + k]`, for `f` of class `C^k` on `ℝ`. -/
theorem exists_fwdDiff_iter_eq_iteratedDeriv (k : ℕ) :
    ∀ {f : ℝ → ℝ}, ContDiff ℝ k f → ∀ x : ℝ,
      ∃ ξ ∈ Set.Icc x (x + k), (fwdDiff (1 : ℝ))^[k] f x = iteratedDeriv k f ξ := by
  induction k with
  | zero => intro f _ x; exact ⟨x, by simp, by simp⟩
  | succ k ih =>
    intro f hf x
    have hshift : ContDiff ℝ (k + 1 : ℕ) (fun y => f (y + 1)) :=
      hf.comp (contDiff_id.add contDiff_const)
    have hle : ((k : ℕ) : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast Nat.le_succ k
    have hg : ContDiff ℝ k (fwdDiff 1 f) := (hshift.sub hf).of_le hle
    obtain ⟨ξ', hξ', heq⟩ := ih hg x
    have hdiff : Differentiable ℝ (iteratedDeriv k f) :=
      hf.differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)
    obtain ⟨ξ, hξ, hmv⟩ := exists_deriv_eq_slope (f := iteratedDeriv k f) (lt_add_one ξ')
      hdiff.continuous.continuousOn hdiff.differentiableOn
    refine ⟨ξ, ⟨by linarith [hξ'.1, hξ.1], ?_⟩, ?_⟩
    · push_cast; linarith [hξ'.2, hξ.2]
    · have hsub : iteratedDeriv k (fwdDiff 1 f) ξ' =
          iteratedDeriv k f (ξ' + 1) - iteratedDeriv k f ξ' := by
        have h1 : fwdDiff 1 f = (fun y => f (y + 1)) - f := rfl
        rw [h1, iteratedDeriv_sub ((hshift.of_le hle).contDiffAt) ((hf.of_le hle).contDiffAt),
          iteratedDeriv_comp_add_const]
      rw [Function.iterate_succ_apply, heq, iteratedDeriv_succ, hmv, hsub]
      ring

/-! ### Power comparisons -/

theorem natCast_rpow_le_of_le {a b : ℝ} (h : a ≤ b) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ a ≤ (n : ℝ) ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) h

/- `n^a = O(n^b)` for `a ≤ b`. -/
private theorem isBigO_natCast_rpow {a b : ℝ} (h : a ≤ b) :
    (fun n : ℕ => (n : ℝ) ^ a) =O[atTop] (fun n : ℕ => (n : ℝ) ^ b) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), one_mul]
  exact natCast_rpow_le_of_le h hn

/- `n^a = o(n^b)` for `a < b`. -/
private theorem isLittleO_natCast_rpow {a b : ℝ} (h : a < b) :
    (fun n : ℕ => (n : ℝ) ^ a) =o[atTop] (fun n : ℕ => (n : ℝ) ^ b) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (a - b)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by linarith : 0 < b - a)).comp tendsto_natCast_atTop_atTop
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, neg_sub]
  refine ((isLittleO_one_iff ℝ).2 ht).mul_isBigO (isBigO_refl (fun n : ℕ => (n : ℝ) ^ b) atTop)
    |>.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← Real.rpow_add (by exact_mod_cast hn), sub_add_cancel]
  · exact Eventually.of_forall fun _ => one_mul _

/- `a² ≤ K b²` eventually gives `a^i = O(b^i)`. -/
private theorem isBigO_pow_of_sq_le_mul {a b : ℕ → ℝ} {K : ℝ}
    (h : ∀ᶠ n in atTop, a n ^ 2 ≤ K * b n ^ 2) (i : ℕ) :
    (fun n => a n ^ i) =O[atTop] (fun n => b n ^ i) := by
  have h1 : a =O[atTop] b := by
    refine IsBigO.of_bound (Real.sqrt K) ?_
    filter_upwards [h] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs,
      ← Real.sqrt_mul' _ (sq_nonneg _)]
    exact Real.sqrt_le_sqrt hn
  exact h1.pow i

/- Finite differences of a sequence that is `o(n^γ)`, `γ ≤ 0`, are `o(n^γ)`. -/
private theorem fwdDiff_iter_isLittleO {ε : ℕ → ℝ} {γ : ℝ} (hγ : γ ≤ 0)
    (hε : ε =o[atTop] (fun n : ℕ => (n : ℝ) ^ γ)) (k : ℕ) :
    (fun n => (fwdDiff 1)^[k] ε n) =o[atTop] (fun n : ℕ => (n : ℝ) ^ γ) := by
  simp only [fwdDiff_iter_eq_sum_shift, smul_eq_mul, mul_one, zsmul_eq_mul]
  apply IsLittleO.fun_sum
  intro i _
  refine IsLittleO.const_mul_left ?_ _
  refine (hε.comp_tendsto (tendsto_add_atTop_nat i)).trans_isBigO ?_
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp_apply, Real.norm_eq_abs, one_mul]
  rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact Real.rpow_le_rpow_of_nonpos hn'
    (by push_cast; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]) hγ

/- The `k`-th difference of `log α` splits into the model's and the error's. -/
private theorem fwdDiff_iter_log_split (α : ℕ → ℝ) (Λ : ℝ → ℝ) (k n : ℕ) :
    (fwdDiff 1)^[k] (fun m => Real.log (α m)) n =
      (fwdDiff (1 : ℝ))^[k] Λ n + (fwdDiff 1)^[k] (fun m : ℕ => Real.log (α m) - Λ m) n := by
  simp only [fwdDiff_iter_eq_sum_shift, ← sum_add_distrib, zsmul_eq_mul, smul_eq_mul, mul_one,
    nsmul_eq_mul]
  refine sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-! ### From a smooth model -/

/-- **Smooth-model form.** Let `d ≥ 2`, let `α(n) > 0` eventually, and let `Λ` be `C^d` on `ℝ` with
`|Λ^{(k)}(x)| ≤ C x^{β−k}` for `2 ≤ k ≤ d` and `Λ''(x) ≤ −c x^{β−2}` for large `x`, where
`0 < β < 2` and `c > 0`. If `log α(n) − Λ(n) = o(n^{(β−2)d/2})`, then `α` has the log-ratio
expansion in degree `d`. -/
theorem hasLogRatioExpansion_of_smooth_model {α : ℕ → ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hα : ∀ᶠ n in atTop, 0 < α n) {Λ : ℝ → ℝ} (hΛ : ContDiff ℝ d Λ)
    {β c C : ℝ} (hβ0 : 0 < β) (hβ2 : β < 2) (hc : 0 < c)
    (hupper : ∀ k ∈ Icc 2 d, ∀ᶠ x in atTop, |iteratedDeriv k Λ x| ≤ C * x ^ (β - k))
    (hlower : ∀ᶠ x in atTop, iteratedDeriv 2 Λ x ≤ -c * x ^ (β - 2))
    (hε : (fun n : ℕ => Real.log (α n) - Λ n) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((β - 2) * d / 2))) :
    HasLogRatioExpansion α d := by
  set ε : ℕ → ℝ := fun n => Real.log (α n) - Λ n with hεdef
  set D : ℕ → ℕ → ℝ := fun k n => (fwdDiff (1 : ℝ))^[k] Λ n with hD
  set δ : ℕ → ℝ := fun n => Real.sqrt (-D 2 n / 2) with hδdef
  set u : ℕ → ℝ := fun n => (n : ℝ) ^ ((β - 2) / 2) with hudef
  have hmv : ∀ k ≤ d, ∀ x : ℝ, ∃ ξ ∈ Set.Icc x (x + k),
      (fwdDiff (1 : ℝ))^[k] Λ x = iteratedDeriv k Λ ξ := fun k hk x =>
    exists_fwdDiff_iter_eq_iteratedDeriv k (hΛ.of_le (by exact_mod_cast hk)) x
  -- one threshold for all the bounds
  obtain ⟨X, hX⟩ := eventually_atTop.1
    (((eventually_all_finset (Icc 2 d)).2 hupper).and hlower)
  set X' := max X 1 with hX'
  have hn : ∀ᶠ n : ℕ in atTop, X' ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop X'
  have hpos' : ∀ ξ : ℝ, X' ≤ ξ → 0 < ξ := fun ξ h => by linarith [le_max_right X 1]
  have hC : 0 ≤ C := by
    have h := (hX X' (le_max_left _ _)).1 2 (mem_Icc.2 ⟨le_rfl, hd⟩)
    have hp : 0 < X' ^ (β - (2 : ℕ)) := Real.rpow_pos_of_pos (hpos' X' le_rfl) _
    exact (mul_nonneg_iff_of_pos_right hp).1 ((abs_nonneg _).trans h)
  -- bounds on `Δ^k Λ(n)`
  have hDk : ∀ k ∈ Icc 2 d, ∀ n : ℕ, X' ≤ (n : ℝ) → |D k n| ≤ C * (n : ℝ) ^ (β - k) := by
    intro k hk n hnX
    obtain ⟨ξ, hξ, heq⟩ := hmv k (mem_Icc.1 hk).2 n
    have hξX : X' ≤ ξ := hnX.trans hξ.1
    simp only [hD, heq]
    refine ((hX ξ ((le_max_left _ _).trans hξX)).1 k hk).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC
    have hk2 : (β - k) ≤ 0 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.1 hk).1
      linarith
    exact Real.rpow_le_rpow_of_nonpos (hpos' _ hnX) hξ.1 hk2
  have hD2 : ∀ n : ℕ, X' ≤ (n : ℝ) → D 2 n ≤ -c * ((n : ℝ) + 2) ^ (β - 2) := by
    intro n hnX
    obtain ⟨ξ, hξ, heq⟩ := hmv 2 hd n
    have hξX : X' ≤ ξ := hnX.trans hξ.1
    simp only [hD, heq]
    refine ((hX ξ ((le_max_left _ _).trans hξX)).2).trans ?_
    have : ((n : ℝ) + 2) ^ (β - 2) ≤ ξ ^ (β - 2) :=
      Real.rpow_le_rpow_of_nonpos (hpos' _ hξX) (by push_cast at hξ; exact hξ.2) (by linarith)
    nlinarith
  have hu2 : ∀ n : ℕ, 0 < n → u n ^ 2 = (n : ℝ) ^ (β - 2) := by
    intro n hn0
    simp only [hudef]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    congr 1; push_cast; ring
  have hev1 : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  -- `δ² = −Δ²Λ/2`, and two-sided comparison with `u²`
  have hδsq : ∀ᶠ n in atTop, δ n ^ 2 = -D 2 n / 2 ∧ 0 < δ n := by
    filter_upwards [hn] with n hnX
    have h1 := hD2 n hnX
    have h2 : 0 < ((n : ℝ) + 2) ^ (β - 2) := Real.rpow_pos_of_pos (by positivity) _
    have h3 : 0 < -D 2 n / 2 := by nlinarith
    exact ⟨Real.sq_sqrt h3.le, Real.sqrt_pos.2 h3⟩
  have hδu : ∀ᶠ n in atTop, δ n ^ 2 ≤ (C / 2) * u n ^ 2 := by
    filter_upwards [hn, hδsq, hev1] with n hnX ⟨h1, _⟩ hn0
    rw [h1, hu2 n hn0]
    have := hDk 2 (mem_Icc.2 ⟨le_rfl, hd⟩) n hnX
    rw [abs_le] at this
    push_cast at this
    linarith [this.1]
  have hthree : ∀ n : ℕ, X' ≤ (n : ℝ) →
      (3 : ℝ) ^ (β - 2) * (n : ℝ) ^ (β - 2) ≤ ((n : ℝ) + 2) ^ (β - 2) := by
    intro n hnX
    have hn1 : (1 : ℝ) ≤ n := (le_max_right X 1).trans hnX
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have huδ : ∀ᶠ n in atTop, u n ^ 2 ≤ (2 / (c * (3 : ℝ) ^ (β - 2))) * δ n ^ 2 := by
    filter_upwards [hn, hδsq, hev1] with n hnX ⟨h1, _⟩ hn0
    rw [h1, hu2 n hn0]
    have h3 := hthree n hnX
    have h4 := hD2 n hnX
    have hp : 0 < (3 : ℝ) ^ (β - 2) := Real.rpow_pos_of_pos (by norm_num) _
    have hcp : 0 < c * (3 : ℝ) ^ (β - 2) := mul_pos hc hp
    rw [div_mul_eq_mul_div, le_div_iff₀ hcp]
    nlinarith
  have hOδu : ∀ i, (fun n => δ n ^ i) =O[atTop] (fun n => u n ^ i) :=
    isBigO_pow_of_sq_le_mul hδu
  have hOuδ : ∀ i, (fun n => u n ^ i) =O[atTop] (fun n => δ n ^ i) :=
    isBigO_pow_of_sq_le_mul huδ
  have hupow : ∀ k : ℕ, (fun n => u n ^ k) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((β - 2) / 2 * k)) :=
    fun k => Eventually.of_forall fun n => by
      simp only [hudef]; rw [Real.rpow_mul_natCast (Nat.cast_nonneg _)]
  -- `Δ^k ε = o(δ^k)` for `k ≤ d`
  have hεk : ∀ k ≤ d, (fun n => (fwdDiff 1)^[k] ε n) =o[atTop] (fun n => δ n ^ k) := by
    intro k hk
    have hγ : (β - 2) * d / 2 ≤ 0 := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      nlinarith
    refine ((fwdDiff_iter_isLittleO hγ hε k).trans_isBigO ?_).trans_isBigO (hOuδ k)
    refine (isBigO_natCast_rpow ?_).congr' EventuallyEq.rfl (hupow k).symm
    have : (k : ℝ) ≤ d := by exact_mod_cast hk
    nlinarith
  refine hasLogRatioExpansion_of_fwdDiff hd hα (δ := δ) ?_ (hδsq.mono fun n h => h.2) ?_ ?_
  · -- `δ → 0`
    have hu0 : Tendsto (fun n => u n ^ 1) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (by linarith : 0 < (2 - β) / 2)).comp
        tendsto_natCast_atTop_atTop
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, hudef, pow_one]
      congr 1; ring
    simpa using (hOδu 1).trans_tendsto hu0
  · -- second difference
    refine (hεk 2 hd).congr' ?_ EventuallyEq.rfl
    filter_upwards [hδsq] with n ⟨h1, _⟩
    rw [fwdDiff_iter_log_split α Λ 2 n, h1]
    simp only [hD, hεdef]
    ring
  · -- higher differences
    intro k hk
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.1 hk).1
    have hkd : k ≤ d := (mem_Icc.1 hk).2
    have hΛk : (fun n => D k n) =o[atTop] (fun n => δ n ^ k) := by
      have hO : (fun n => D k n) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (β - k)) := by
        refine IsBigO.of_bound C ?_
        filter_upwards [hn] with n hnX
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
        exact hDk k (mem_Icc.2 ⟨by have := (mem_Icc.1 hk).1; omega, hkd⟩) n hnX
      refine (hO.trans_isLittleO ?_).trans_isBigO (hOuδ k)
      refine (isLittleO_natCast_rpow ?_).congr' EventuallyEq.rfl (hupow k).symm
      nlinarith
    refine (hΛk.add (hεk k hkd)).congr' (Eventually.of_forall fun n => ?_) EventuallyEq.rfl
    exact (fwdDiff_iter_log_split α Λ k n).symm

/- **Smooth model, assembled.** Under the hypotheses of `hasLogRatioExpansion_of_smooth_model`
(for `d ≥ 2`; every sequence has the expansion when `d = 1`), if `α` is eventually positive and
`log (α (n + 1) / α n)` is eventually bounded below, then for all large `n` the Jensen polynomial
of degree `d` and shift `n` of `α` has as many real roots, with multiplicity, as its degree. -/
private theorem eventually_card_roots_of_smooth_model {α : ℕ → ℝ} {d : ℕ} (hd : 1 ≤ d)
    (hα : ∀ᶠ n in atTop, 0 < α n)
    (hlow : ∃ c, ∀ᶠ n in atTop, -c ≤ Real.log (α (n + 1) / α n))
    {Λ : ℝ → ℝ} (hΛ : ContDiff ℝ d Λ)
    {β c K : ℝ} (hβ0 : 0 < β) (hβ2 : β < 2) (hc : 0 < c)
    (hupper : ∀ k ∈ Icc 2 d, ∀ᶠ x in atTop, |iteratedDeriv k Λ x| ≤ K * x ^ (β - k))
    (hlower : ∀ᶠ x in atTop, iteratedDeriv 2 Λ x ≤ -c * x ^ (β - 2))
    (hε : (fun n : ℕ => Real.log (α n) - Λ n) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((β - 2) * d / 2))) :
    ∀ᶠ n in atTop,
      (∑ j ∈ range (d + 1), C ((d.choose j : ℝ) * α (n + j)) * X ^ j).roots.card =
        (∑ j ∈ range (d + 1), C ((d.choose j : ℝ) * α (n + j)) * X ^ j).natDegree := by
  rcases le_or_gt d 1 with h | h
  · exact (hasLogRatioExpansion_of_le_one α h).eventually_card_roots hd hα hlow
  · exact (hasLogRatioExpansion_of_smooth_model (by omega) hα hΛ hβ0 hβ2 hc hupper hlower
      hε).eventually_card_roots hd hα hlow

end

end MetaMathlibExt.ColoredPartitionsJensen
