/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeCounting.MertensFunctionBound
public import MathlibExt.NumberTheory.ArithmeticFunction.MoebiusSummatory
public import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Consequences of the bound for the Mertens function

From `M(x) = O(x exp(-c (log x) ^ (1 / 10)))` we deduce the same bound for the summatory
function of the Liouville function, and the convergence of `∑ μ(n) n ^ (-s)` on the line
`re s = 1`.

## Main statements

* `ArithmeticFunction.sum_liouville_isBigO_mul_exp_neg_mul_log_rpow`: there is `c > 0` with
  `∑_{n ≤ x} λ(n) = O(x exp(-c (log x) ^ (1 / 10)))`.
* `ArithmeticFunction.exists_tendsto_sum_moebius_div_cpow_of_re_eq_one`: for `re s = 1` the
  partial sums of `∑ μ(n) / n ^ s` converge.
-/

@[expose] public section

open Asymptotics Filter

namespace ArithmeticFunction

/-- **A bound for the summatory function of the Liouville function.** There is `c > 0` with
`∑_{n ≤ x} λ(n) = O(x exp(-c (log x) ^ (1 / 10)))`. It follows from the bound for the Mertens
function through `λ(n) = ∑_{d² e = n} μ(e)`. -/
theorem sum_liouville_isBigO_mul_exp_neg_mul_log_rpow :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.liouville n : ℤ) : ℝ))
        =O[atTop] fun x : ℝ => x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) := by
  classical
  -- ## Step 1: `λ = B * μ`, where `B = ζ * λ` is the indicator function of the squares
  set B : ArithmeticFunction ℤ := (ArithmeticFunction.zeta : ArithmeticFunction ℤ) *
    ArithmeticFunction.liouville with hBdef
  have hmulB : B.IsMultiplicative :=
    hBdef ▸ ArithmeticFunction.isMultiplicative_zeta.natCast.mul
      ArithmeticFunction.isMultiplicative_liouville
  have hsq : ∀ {n : ℕ}, n ≠ 0 → (IsSquare n ↔ ∀ p, Even (n.factorization p)) := by
    intro n hn
    constructor
    · rintro ⟨m, rfl⟩ p
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      rw [Nat.factorization_mul hm hm]
      simp
    · intro h
      refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
      conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← pow_add]
      congr 1
      have := h p
      rw [Nat.even_iff] at this
      omega
  have hBpp : ∀ p k : ℕ, p.Prime → B (p ^ k) = if Even k then 1 else 0 := by
    intro p k hp
    rw [hBdef, ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
    have hval : ∀ i ∈ Finset.range (k + 1),
        ArithmeticFunction.liouville (p ^ i) = (-1 : ℤ) ^ i := fun i _ => by
      rw [ArithmeticFunction.liouville_apply (pow_ne_zero i hp.ne_zero),
        ArithmeticFunction.cardFactors_apply_prime_pow hp]
    rw [Finset.sum_congr rfl hval, neg_one_geom_sum]
    by_cases hk : Even k <;> simp [hk, Nat.even_add_one]
  have hBsq : ∀ n : ℕ, n ≠ 0 → B n = if IsSquare n then 1 else 0 := by
    intro n hn
    rw [IsMultiplicative.multiplicative_factorization B hmulB hn, Finsupp.prod,
      Nat.support_factorization]
    by_cases hn2 : IsSquare n
    · rw [ite_eq_left hn2]
      refine Finset.prod_eq_one fun p hp => ?_
      rw [hBpp p _ (Nat.prime_of_mem_primeFactors hp), ite_eq_left ((hsq hn).mp hn2 p)]
    · rw [ite_eq_right hn2]
      obtain ⟨p, hp⟩ : ∃ p, ¬ Even (n.factorization p) := by
        by_contra hc
        exact hn2 ((hsq hn).mpr fun p => not_not.mp fun h => hc ⟨p, h⟩)
      have hpmem : p ∈ n.primeFactors := by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff]
        intro h
        exact hp (by simp [h])
      refine Finset.prod_eq_zero hpmem ?_
      rw [hBpp p _ (Nat.prime_of_mem_primeFactors hpmem), ite_eq_right hp]
  have hlam : (ArithmeticFunction.liouville : ArithmeticFunction ℤ)
      = B * ArithmeticFunction.moebius := by
    rw [hBdef, mul_comm, ← mul_assoc, ArithmeticFunction.moebius_mul_coe_zeta, one_mul]
  -- ## Step 2: `∑_{n ≤ N} λ (n) = ∑_{k ≤ √N} M (N / k ^ 2)`
  have hS : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.liouville n
      = ∑ k ∈ Finset.Icc 1 N.sqrt,
          ∑ m ∈ Finset.Icc 1 (N / (k * k)), ArithmeticFunction.moebius m := by
    intro N
    have himage : (Finset.Icc 1 N.sqrt).image (fun k => k * k)
        = (Finset.Icc 1 N).filter IsSquare := by
      ext d
      simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_filter]
      constructor
      · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
        refine ⟨⟨Nat.one_le_iff_ne_zero.2 (by positivity), Nat.le_sqrt.1 hk2⟩, ⟨k, rfl⟩⟩
      · rintro ⟨⟨hd1, hd2⟩, ⟨k, rfl⟩⟩
        refine ⟨k, ⟨?_, Nat.le_sqrt.2 hd2⟩, rfl⟩
        rcases Nat.eq_zero_or_pos k with rfl | h
        · simp at hd1
        · exact h
    calc ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.liouville n
        = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, B d * ArithmeticFunction.moebius (n / d) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hlam, ArithmeticFunction.mul_apply,
            Nat.sum_divisorsAntidiagonal (fun a b => B a * ArithmeticFunction.moebius b)]
      _ = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), B d * ArithmeticFunction.moebius m :=
          (Nat.sum_Icc_sum_Icc_div_eq_sum_Icc_sum_divisors N
            (fun d m => B d * ArithmeticFunction.moebius m)).symm
      _ = ∑ d ∈ Finset.Icc 1 N, B d * ∑ m ∈ Finset.Icc 1 (N / d), ArithmeticFunction.moebius m := by
          simp only [Finset.mul_sum]
      _ = ∑ d ∈ (Finset.Icc 1 N).filter IsSquare,
            ∑ m ∈ Finset.Icc 1 (N / d), ArithmeticFunction.moebius m := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun d hd => ?_
          have hd0 : d ≠ 0 := by
            have := (Finset.mem_Icc.1 hd).1
            omega
          rw [hBsq d hd0]
          split_ifs <;> simp
      _ = ∑ k ∈ Finset.Icc 1 N.sqrt,
            ∑ m ∈ Finset.Icc 1 (N / (k * k)), ArithmeticFunction.moebius m := by
          rw [← himage, Finset.sum_image]
          intro a _ b _ hab
          exact Nat.mul_self_inj.1 hab
  -- ## Step 3: insert the bound for the Mertens function
  set Mr : ℝ → ℝ := fun y => ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ)
    with hMr
  have htriv : ∀ y : ℝ, 0 ≤ y → |Mr y| ≤ y := by
    intro y hy
    calc |Mr y| ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, |((ArithmeticFunction.moebius n : ℤ) : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (1 : ℝ) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [← Int.cast_abs]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      _ = (⌊y⌋₊ : ℝ) := by simp
      _ ≤ y := Nat.floor_le hy
  obtain ⟨c, hc, hM⟩ := sum_moebius_isBigO_mul_exp_neg_mul_log_rpow
  obtain ⟨C, hC, hCw⟩ := hM.exists_pos
  obtain ⟨y0, hy0⟩ := eventually_atTop.1 (isBigOWith_iff.1 hCw)
  set c' : ℝ := min (c / 3) (1 / 6) with hc'
  have hc'pos : 0 < c' := by positivity
  refine ⟨c', hc'pos, ?_⟩
  refine IsBigO.of_bound (2 * C + 1) ?_
  filter_upwards [eventually_ge_atTop (max (max y0 1 ^ 3) (Real.exp 1))] with x hx
  have hxe : Real.exp 1 ≤ x := le_of_max_le_right hx
  have hxm : max y0 1 ^ 3 ≤ x := le_of_max_le_left hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  set L := Real.log x with hL
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hxe
  set t : ℝ := x ^ (1 / 3 : ℝ) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hxpos _
  have ht3 : t ^ 3 = x := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    norm_num
  have htm : max y0 1 ≤ t := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) htpos.le ?_
    rw [ht3]
    exact hxm
  have hlogt : Real.log t = L / 3 := by
    rw [ht, Real.log_rpow hxpos]
    ring
  set E : ℝ := Real.exp (-c' * L ^ (1 / 10 : ℝ)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  -- the per-term bound
  have hterm : ∀ k ∈ Finset.Icc 1 (⌊x⌋₊).sqrt,
      |Mr (x / ((k * k : ℕ) : ℝ))| ≤ C * x * E * ((k : ℝ) ^ 2)⁻¹ + t := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by
      have := (Finset.mem_Icc.1 hk).1
      exact_mod_cast this
    have hkpos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    have hcast : ((k * k : ℕ) : ℝ) = (k : ℝ) ^ 2 := by push_cast; ring
    rw [hcast]
    have hfirst : 0 ≤ C * x * E * ((k : ℝ) ^ 2)⁻¹ := by positivity
    by_cases hkt : (k : ℝ) ≤ t
    · set y := x / (k : ℝ) ^ 2 with hy
      have hk2 : (k : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by linarith) hkt 2
      have hyt : t ≤ y := by
        rw [hy, le_div_iff₀ hkpos, ← ht3]
        nlinarith
      have hy0' : y0 ≤ y := le_trans (le_trans (le_max_left _ _) htm) hyt
      have hy1 : 1 ≤ y := le_trans (le_trans (le_max_right _ _) htm) hyt
      have hypos : 0 < y := by linarith
      have hb := hy0 y hy0'
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (mul_pos hypos (Real.exp_pos _))] at hb
      have hlogy : L / 3 ≤ Real.log y := by
        rw [← hlogt]
        exact Real.log_le_log htpos hyt
      have hexp : Real.exp (-c * Real.log y ^ (1 / 10 : ℝ)) ≤ E := by
        rw [hE, Real.exp_le_exp]
        have h1 : (L / 3) ^ (1 / 10 : ℝ) ≤ Real.log y ^ (1 / 10 : ℝ) :=
          Real.rpow_le_rpow (by linarith) hlogy (by norm_num)
        have h2 : (L / 3) ^ (1 / 10 : ℝ) = L ^ (1 / 10 : ℝ) / 3 ^ (1 / 10 : ℝ) :=
          Real.div_rpow (by linarith) (by norm_num) _
        have h3 : (3 : ℝ) ^ (1 / 10 : ℝ) ≤ 3 := by
          have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
            (by norm_num : (1 / 10 : ℝ) ≤ 1)
          simpa using this
        have h3pos : (0 : ℝ) < 3 ^ (1 / 10 : ℝ) := by positivity
        have hLr : 0 ≤ L ^ (1 / 10 : ℝ) := by positivity
        have h4 : L ^ (1 / 10 : ℝ) / 3 ≤ L ^ (1 / 10 : ℝ) / 3 ^ (1 / 10 : ℝ) :=
          div_le_div_of_nonneg_left hLr h3pos h3
        have hc'c : c' ≤ c / 3 := min_le_left _ _
        nlinarith
      calc |Mr y| ≤ C * (y * Real.exp (-c * Real.log y ^ (1 / 10 : ℝ))) := hb
        _ ≤ C * (y * E) := by gcongr
        _ = C * x * E * ((k : ℝ) ^ 2)⁻¹ := by rw [hy]; field_simp
        _ ≤ C * x * E * ((k : ℝ) ^ 2)⁻¹ + t := by linarith
    · rw [not_le] at hkt
      have hk2 : t ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ htpos.le hkt.le 2
      have hyt : x / (k : ℝ) ^ 2 ≤ t := by
        rw [div_le_iff₀ hkpos, ← ht3]
        nlinarith
      have := htriv (x / (k : ℝ) ^ 2) (by positivity)
      linarith
  -- summing the per-term bounds
  set K := (⌊x⌋₊).sqrt with hK
  have hKx : (K : ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by positivity) hxpos.le]
    have h1 : K * K ≤ ⌊x⌋₊ := Nat.sqrt_le ⌊x⌋₊
    have h2 : ((K * K : ℕ) : ℝ) ≤ x := le_trans (by exact_mod_cast h1) (Nat.floor_le hxpos.le)
    push_cast at h2
    nlinarith
  have hinv : ∑ k ∈ Finset.Icc 1 K, ((k : ℝ) ^ 2)⁻¹ ≤ 2 := by
    have hIcc : Finset.Icc 1 K = Finset.Ioo 0 (K + 1) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ioo]; omega
    rw [hIcc]
    have := sum_Ioo_inv_sq_le (α := ℝ) 0 (K + 1)
    simpa using this
  have hsqrt_t : Real.sqrt x * t ≤ x * E := by
    have hs : Real.sqrt x = Real.exp (L / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hxpos, hL]
      ring_nf
    have htt : t = Real.exp (L / 3) := by
      rw [ht, Real.rpow_def_of_pos hxpos, hL]
      ring_nf
    have hxx : x = Real.exp L := (Real.exp_log hxpos).symm
    rw [hs, htt, hE, ← Real.exp_add]
    conv_rhs => rw [hxx]
    rw [← Real.exp_add, Real.exp_le_exp]
    have h1 : L ^ (1 / 10 : ℝ) ≤ L := by
      have := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 10 : ℝ) ≤ 1)
      simpa using this
    have h2 : c' ≤ 1 / 6 := min_le_right _ _
    have h3 : 0 ≤ L ^ (1 / 10 : ℝ) := by positivity
    nlinarith
  have hrw : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.liouville n : ℤ) : ℝ)
      = ∑ k ∈ Finset.Icc 1 K, Mr (x / ((k * k : ℕ) : ℝ)) := by
    rw [← Int.cast_sum, hS, Int.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hMr]
    dsimp only
    rw [Nat.floor_div_natCast, Int.cast_sum]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (mul_pos hxpos hEpos), hrw]
  calc |∑ k ∈ Finset.Icc 1 K, Mr (x / ((k * k : ℕ) : ℝ))|
      ≤ ∑ k ∈ Finset.Icc 1 K, |Mr (x / ((k * k : ℕ) : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 K, (C * x * E * ((k : ℝ) ^ 2)⁻¹ + t) := Finset.sum_le_sum hterm
    _ = C * x * E * ∑ k ∈ Finset.Icc 1 K, ((k : ℝ) ^ 2)⁻¹ + K * t := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp
    _ ≤ C * x * E * 2 + Real.sqrt x * t := by
      have hCxE : 0 ≤ C * x * E := by positivity
      gcongr
    _ ≤ (2 * C + 1) * (x * E) := by nlinarith

/-- **Convergence of `∑ μ(n) / n ^ s` on the line `re s = 1`.** For `re s = 1` the partial
sums `∑_{n ≤ N} μ(n) / n ^ s` converge. The convergence is conditional: the series is not
absolutely convergent on this line. -/
theorem exists_tendsto_sum_moebius_div_cpow_of_re_eq_one {s : ℂ} (hs : s.re = 1) :
    ∃ L : ℂ, Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius n : ℤ) : ℂ) / (n : ℂ) ^ s)
      Filter.atTop (nhds L) := by
  classical
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hns : (-s).re = -1 := by simp [hs]
  set w : ℕ → ℂ := fun n => (n : ℂ) ^ (-s) with hw
  set M : ℕ → ℂ := fun N =>
    ∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius n : ℤ) : ℂ) with hMdef
  -- ## Summation by parts
  have hid : ∀ N : ℕ,
      ∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius n : ℤ) : ℂ) / (n : ℂ) ^ s
        = M N * w N - ∑ n ∈ Finset.range N, M n * (w (n + 1) - w n) := by
    intro N
    induction N with
    | zero => simp [hMdef]
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
      have hM1 : M (N + 1) = M N + ((ArithmeticFunction.moebius (N + 1) : ℤ) : ℂ) := by
        simp only [hMdef]
        rw [Finset.sum_Icc_succ_top (by omega)]
      have hw1 : ((ArithmeticFunction.moebius (N + 1) : ℤ) : ℂ) / ((N + 1 : ℕ) : ℂ) ^ s
          = ((ArithmeticFunction.moebius (N + 1) : ℤ) : ℂ) * w (N + 1) := by
        simp only [hw, Complex.cpow_neg, div_eq_mul_inv]
      rw [hM1, hw1]
      ring
  -- ## Mean value bound on the increments of `n ↦ n ^ (-s)`
  have hMVT : ∀ i : ℕ, 1 ≤ i → ‖w (i + 1) - w i‖ ≤ ‖s‖ * (i : ℝ) ^ (-2 : ℝ) := by
    intro i hi
    have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
    have hpos : ∀ x ∈ Set.Icc (i : ℝ) ((i : ℝ) + 1), (0 : ℝ) < x :=
      fun x hx => lt_of_lt_of_le hi0 hx.1
    have hder : ∀ x ∈ Set.Icc (i : ℝ) ((i : ℝ) + 1),
        HasDerivWithinAt (fun t : ℝ => (t : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1))
          (Set.Icc (i : ℝ) ((i : ℝ) + 1)) x :=
      fun x hx => (hasDerivAt_ofReal_cpow_const (ne_of_gt (hpos x hx))
        (neg_ne_zero.mpr hs0)).hasDerivWithinAt
    have hbnd : ∀ x ∈ Set.Icc (i : ℝ) ((i : ℝ) + 1),
        ‖-s * (x : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * (i : ℝ) ^ (-2 : ℝ) := by
      intro x hx
      rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (hpos x hx)]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
      have h1 : (-s - 1).re = -2 := by simp [hs]; norm_num
      rw [h1]
      exact Real.rpow_le_rpow_of_nonpos hi0 hx.1 (by norm_num)
    have hmvt := (convex_Icc (i : ℝ) ((i : ℝ) + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le
      hder hbnd (x := (i : ℝ)) (y := (i : ℝ) + 1) (by simp) (by simp)
    simpa [hw] using hmvt
  -- ## The Mertens bound gives `|M (n)| ≪ n / (1 + log n) ^ 2`
  obtain ⟨c, hc, hMO⟩ := sum_moebius_isBigO_mul_exp_neg_mul_log_rpow
  obtain ⟨C, hCb⟩ := hMO.bound
  obtain ⟨A, hA0, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧ ∀ u : ℝ, 0 ≤ u →
      (1 + u) ^ 2 ≤ A * Real.exp (c * u ^ (1 / 10 : ℝ)) := by
    have pow_bd : ∀ (n : ℕ) (u : ℝ), 0 ≤ u →
        (u ^ (1 / 10 : ℝ)) ^ n ≤
          ((Nat.factorial n : ℝ) / c ^ n) * Real.exp (c * u ^ (1 / 10 : ℝ)) := by
      intro n u hu
      have hv0 : (0 : ℝ) ≤ u ^ (1 / 10 : ℝ) := Real.rpow_nonneg hu _
      have hav : (0 : ℝ) ≤ c * u ^ (1 / 10 : ℝ) := mul_nonneg hc.le hv0
      have hfn : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast n.factorial_pos
      have hpn : (0 : ℝ) < c ^ n := pow_pos hc n
      have h := Real.pow_div_factorial_le_exp _ hav n
      rw [mul_pow, div_le_iff₀ hfn] at h
      rw [div_mul_eq_mul_div, le_div_iff₀ hpn]
      linarith
    have h10 : ∀ u : ℝ, 0 ≤ u → (u ^ (1 / 10 : ℝ)) ^ (10 : ℕ) = u := by
      intro u hu
      rw [← Real.rpow_natCast (u ^ (1 / 10 : ℝ)) 10, ← Real.rpow_mul hu]
      norm_num
    refine ⟨1 + 2 * ((Nat.factorial 10 : ℝ) / c ^ 10) + (Nat.factorial 20 : ℝ) / c ^ 20,
      by positivity, fun u hu => ?_⟩
    have h20 : (u ^ (1 / 10 : ℝ)) ^ (20 : ℕ) = u ^ 2 := by
      rw [show (20 : ℕ) = 10 * 2 from rfl, pow_mul, h10 u hu]
    have ha := pow_bd 10 u hu
    have hb := pow_bd 20 u hu
    rw [h10 u hu] at ha
    rw [h20] at hb
    have h1 : (1 : ℝ) ≤ Real.exp (c * u ^ (1 / 10 : ℝ)) :=
      Real.one_le_exp (mul_nonneg hc.le (Real.rpow_nonneg hu _))
    nlinarith
  have hMbd : ∀ᶠ n : ℕ in atTop,
      ‖M n‖ ≤ (|C| * A) * ((n : ℝ) / (1 + Real.log n) ^ 2) := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hCb, eventually_ge_atTop 1]
      with n hn hn1
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < n := by linarith
    have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1'
    have hMn : M n = ((∑ i ∈ Finset.Icc 1 ⌊(n : ℝ)⌋₊,
        ((ArithmeticFunction.moebius i : ℤ) : ℝ) : ℝ) : ℂ) := by
      simp only [hMdef, Nat.floor_natCast]
      push_cast
      rfl
    rw [hMn, Complex.norm_real]
    refine hn.trans ?_
    rw [Real.norm_eq_abs ((n : ℝ) * _), abs_of_pos (by positivity)]
    have hkey := hA (Real.log n) hlog
    have hL : 0 < (1 + Real.log n) ^ 2 := by positivity
    have hexp : Real.exp (-c * Real.log n ^ (1 / 10 : ℝ)) ≤ A / (1 + Real.log n) ^ 2 := by
      rw [le_div_iff₀ hL]
      have hEF : Real.exp (-c * Real.log n ^ (1 / 10 : ℝ)) *
          Real.exp (c * Real.log n ^ (1 / 10 : ℝ)) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-c * Real.log n ^ (1 / 10 : ℝ))]
    have hX0 : 0 ≤ (n : ℝ) * Real.exp (-c * Real.log n ^ (1 / 10 : ℝ)) := by positivity
    calc C * ((n : ℝ) * Real.exp (-c * Real.log n ^ (1 / 10 : ℝ)))
        ≤ |C| * ((n : ℝ) * (A / (1 + Real.log n) ^ 2)) :=
          (mul_le_mul_of_nonneg_right (le_abs_self C) hX0).trans
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hnpos.le) (abs_nonneg C))
      _ = (|C| * A) * ((n : ℝ) / (1 + Real.log n) ^ 2) := by ring
  -- ## Boundary term tends to zero
  have h1 : Tendsto (fun N : ℕ => M N * w N) atTop (nhds 0) := by
    have hlim : Tendsto (fun N : ℕ => |C| * A * ((1 + Real.log N) ^ 2)⁻¹) atTop (nhds 0) := by
      have : Tendsto (fun N : ℕ => 1 + Real.log N) atTop atTop :=
        tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      simpa using ((tendsto_pow_atTop two_ne_zero).comp this).inv_tendsto_atTop.const_mul (|C| * A)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hMbd, eventually_ge_atTop 1] with N hN hN1
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [norm_mul, hw]
    dsimp only
    rw [Complex.norm_natCast_cpow_of_pos hN1, hns, Real.rpow_neg_one]
    calc ‖M N‖ * (N : ℝ)⁻¹ ≤ ((|C| * A) * ((N : ℝ) / (1 + Real.log N) ^ 2)) * (N : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hN (by positivity)
      _ = |C| * A * ((1 + Real.log N) ^ 2)⁻¹ := by field_simp
  -- ## Summability of `∑ 1 / (n (1 + log n) ^ 2)` by telescoping
  have hstep : ∀ m : ℝ, 1 ≤ m →
      ((m + 1) * (1 + Real.log (m + 1)) ^ 2)⁻¹ ≤
        (1 + Real.log m)⁻¹ - (1 + Real.log (m + 1))⁻¹ := by
    intro m hm
    have hm0 : 0 < m := by linarith
    have hlm : 0 ≤ Real.log m := Real.log_nonneg hm
    have hlt : Real.log m + 1 / (m + 1) ≤ Real.log (m + 1) := by
      have h := Real.log_le_sub_one_of_pos (x := m / (m + 1)) (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h
      have h' : m / (m + 1) - 1 = -(1 / (m + 1)) := by field_simp; ring
      linarith
    have ha : 0 < 1 + Real.log m := by linarith
    have hb : 0 < 1 + Real.log (m + 1) := by
      have : 0 < 1 / (m + 1) := by positivity
      linarith
    have hba : 1 ≤ ((1 + Real.log (m + 1)) - (1 + Real.log m)) * (m + 1) := by
      have h := mul_le_mul_of_nonneg_right hlt (by positivity : (0 : ℝ) ≤ m + 1)
      have : 1 / (m + 1) * (m + 1) = 1 := by field_simp
      nlinarith
    have hab : (1 + Real.log m) * (1 + Real.log (m + 1)) ≤ (1 + Real.log (m + 1)) ^ 2 := by
      have : 1 / (m + 1) > 0 := by positivity
      nlinarith
    rw [inv_sub_inv ha.ne' hb.ne', inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hba (sq_nonneg (1 + Real.log (m + 1)))]
  set b : ℕ → ℝ := fun n => ((n : ℝ) * (1 + Real.log n) ^ 2)⁻¹ with hbdef
  have hb0 : ∀ n, 0 ≤ b n := fun n => by simp only [hbdef]; positivity
  have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range (N + 2), b i ≤ 2 - (1 + Real.log ((N : ℝ) + 1))⁻¹ := by
    intro N
    induction N with
    | zero => norm_num [Finset.sum_range_succ, hbdef]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have h := hstep ((N : ℝ) + 1) (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
      have e : (N : ℝ) + 1 + 1 = N + 2 := by ring
      rw [e] at h
      have hbN : b (N + 2) = (((N : ℝ) + 2) * (1 + Real.log ((N : ℝ) + 2)) ^ 2)⁻¹ := by
        simp only [hbdef]; push_cast; rfl
      rw [hbN]
      push_cast
      rw [e]
      linarith
  have hbsum : Summable b := by
    refine summable_of_sum_range_le hb0 (c := 2) fun N => ?_
    calc ∑ i ∈ Finset.range N, b i ≤ ∑ i ∈ Finset.range (N + 2), b i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
            (fun i _ _ => hb0 i)
      _ ≤ 2 - (1 + Real.log ((N : ℝ) + 1))⁻¹ := hpart N
      _ ≤ 2 := by
          have : 0 ≤ Real.log ((N : ℝ) + 1) :=
            Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
          have : 0 ≤ (1 + Real.log ((N : ℝ) + 1))⁻¹ := by positivity
          linarith
  -- ## The Abel-summed series converges absolutely
  have hsum : Summable (fun n => M n * (w (n + 1) - w n)) := by
    refine Summable.of_norm_bounded_eventually (hbsum.mul_left (|C| * A * ‖s‖)) ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hMbd, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [norm_mul]
    calc ‖M n‖ * ‖w (n + 1) - w n‖
        ≤ ((|C| * A) * ((n : ℝ) / (1 + Real.log n) ^ 2)) * (‖s‖ * (n : ℝ) ^ (-2 : ℝ)) :=
          mul_le_mul hn (hMVT n hn1) (norm_nonneg _) (by positivity)
      _ = |C| * A * ‖s‖ * b n := by
          rw [Real.rpow_neg hnpos.le, Real.rpow_two]
          simp only [hbdef]
          field_simp
  refine ⟨0 - ∑' n, M n * (w (n + 1) - w n), ?_⟩
  exact (h1.sub hsum.hasSum.tendsto_sum_nat).congr fun N => (hid N).symm

end ArithmeticFunction
