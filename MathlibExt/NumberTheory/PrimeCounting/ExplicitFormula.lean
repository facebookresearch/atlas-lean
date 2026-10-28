/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.RiemannZetaResidues
public import MathlibExt.NumberTheory.LSeries.RiemannZetaLogDerivZeros
public import Mathlib.NumberTheory.Chebyshev
import MathlibExt.Analysis.PerronKernel
import MathlibExt.NumberTheory.PrimeCounting.ChebyshevPsiZeroFree
import MathlibExt.NumberTheory.LSeries.VerticalLine
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The explicit formula for `ψ(x)`

For `x` half more than a positive integer,
`ψ(x) = x - ∑_ρ x^ρ/ρ - ζ'(0)/ζ(0) - ½ log (1 - x⁻²)`, the sum over the nontrivial zeros of `ζ`
counted with multiplicity being the limit of its truncations `|γ| < R`. We deduce von Koch's
theorem: the Riemann hypothesis holds if and only if `ψ(x) = x + O(√x log² x)`.

The proof follows the classical route: the truncated Perron formula expresses `ψ(x)` through a
vertical integral of `-ζ'/ζ(s) x^s/s`; shifting the contour to the left over a rectangle picks up
the residues at `1`, `0`, the nontrivial and the trivial zeros; the horizontal sides are bounded
at good heights, and the left side tends to `0`.

## Main statements

* `exists_sum_inv_abs_log_div_le`: `∑_{x/2 < n < 2x} |log (x/n)|⁻¹ ≤ C (x / ‖x‖) log x`, where
  `‖x‖` is the distance from `x` to the nearest integer.
* `exists_tsum_vonMangoldt_mul_div_abs_log_le`: the Perron error sum at `c = 1 + 1/log x`.
* `norm_chebyshevPsi_sub_truncated_integral_le`: the truncated Perron formula for `ψ(x)`.
* `exists_truncated_explicit_formula_chebyshevPsi`: the truncated explicit formula.
* `tendsto_sum_cpow_div_zeros_explicit_formula`: **the explicit formula** for `ψ(x)`.
* `chebyshevPsi_sub_self_isBigO_of_riemannHypothesis`: under the Riemann hypothesis,
  `ψ(x) - x = O(√x log² x)`.
* `riemannHypothesis_iff_chebyshevPsi_sub_self_isBigO`: **von Koch's criterion**.
-/

@[expose] public section

universe u

open Complex Filter Topology Asymptotics ArithmeticFunction RiemannXi ComplexConjugate

/-! ### An elementary sum -/

/-- For real `x ≥ 2` not an integer, `∑_{x/2 < n < 2x} |log (x/n)|⁻¹ ≤ C (x / ‖x‖) log x`, where
`‖x‖ = |x - round x|` is the distance from `x` to the nearest integer and `C` is absolute. -/
theorem exists_sum_inv_abs_log_div_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → (∀ m : ℤ, (m : ℝ) ≠ x) →
      ∑ n ∈ (Finset.range ⌈2 * x⌉₊).filter (fun n : ℕ => x / 2 < n ∧ (n : ℝ) < 2 * x),
          |Real.log (x / n)|⁻¹ ≤
        C * (x / |x - round x|) * Real.log x := by
  refine ⟨40, fun x hx hint => ?_⟩
  set d := |x - round x| with hd_def
  have hd_pos : 0 < d := abs_pos.mpr (sub_ne_zero.mpr (fun h => hint _ h.symm))
  have hd_le : d ≤ 1 / 2 := abs_sub_round x
  have hxr := abs_le.mp hd_le
  have hround_nonneg : (0 : ℤ) ≤ round x := by
    have : (0 : ℝ) ≤ (round x : ℝ) := by linarith [hxr.2]
    exact_mod_cast this
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = round x :=
    ⟨(round x).toNat, Int.toNat_of_nonneg hround_nonneg⟩
  have hrR : (r : ℝ) = (round x : ℝ) := by rw [← hr]; rfl
  have hxr' : |x - r| = d := by rw [hrR]
  have hr_le : (r : ℝ) ≤ x + 1 / 2 := by rw [hrR]; linarith [hxr.1]
  set N := ⌈2 * x⌉₊ with hN
  have hN_le : (N : ℝ) ≤ 3 * x := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * x by linarith)
    linarith
  have hN_pos : (0 : ℝ) < N := by
    have := Nat.le_ceil (2 * x)
    linarith
  let g : ℕ → ℝ := fun n =>
    (if r ≤ n then ((n : ℝ) - r + 1)⁻¹ else 0) + (if n ≤ r then ((r : ℝ) - n + 1)⁻¹ else 0)
  have hA0 : ∀ n, 0 ≤ (if r ≤ n then ((n : ℝ) - r + 1)⁻¹ else 0) := by
    intro n
    split_ifs with h
    · have : (r : ℝ) ≤ n := by exact_mod_cast h
      exact inv_nonneg.mpr (by linarith)
    · exact le_rfl
  have hB0 : ∀ n, 0 ≤ (if n ≤ r then ((r : ℝ) - n + 1)⁻¹ else 0) := by
    intro n
    split_ifs with h
    · have : (n : ℝ) ≤ r := by exact_mod_cast h
      exact inv_nonneg.mpr (by linarith)
    · exact le_rfl
  have hg_nonneg : ∀ n, 0 ≤ g n := fun n => add_nonneg (hA0 n) (hB0 n)
  have hterm : ∀ n ∈ (Finset.range N).filter (fun n : ℕ => x / 2 < n ∧ (n : ℝ) < 2 * x),
      |Real.log (x / n)|⁻¹ ≤ 4 * x / d * g n := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := (Finset.mem_filter.mp hn).2
    have hn0 : (0 : ℝ) < n := by linarith
    set k := |(n : ℝ) - r| with hk
    have hk0 : 0 ≤ k := abs_nonneg _
    have h1 : d ≤ |x - n| := by simpa using round_le x (n : ℤ)
    have h2 : k - d ≤ |x - n| := by
      have := abs_sub_le (n : ℝ) x r
      rw [abs_sub_comm (n : ℝ) x, hxr'] at this
      linarith
    have hdk : d * k ≤ 1 / 2 * k := mul_le_mul_of_nonneg_right hd_le hk0
    have hdist : d * (k + 1) / 2 ≤ |x - n| := by nlinarith
    have hlog : |x - n| / (2 * x) ≤ |Real.log (x / n)| := by
      rcases le_or_gt (n : ℝ) x with h | h
      · have hl := Real.one_sub_inv_le_log_of_pos (show 0 < x / n by positivity)
        rw [inv_div] at hl
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - n)]
        have : (x - n) / (2 * x) ≤ 1 - n / x := by
          rw [show 1 - (n : ℝ) / x = (x - n) / x by field_simp]
          exact div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
        exact this.trans (hl.trans (le_abs_self _))
      · have hl := Real.one_sub_inv_le_log_of_pos (show 0 < n / x by positivity)
        rw [inv_div] at hl
        have heq : Real.log (x / n) = - Real.log (n / x) := by
          rw [← Real.log_inv, inv_div]
        rw [heq, abs_neg, abs_of_neg (by linarith : x - (n : ℝ) < 0)]
        have : -(x - n) / (2 * x) ≤ 1 - x / n := by
          rw [div_le_iff₀ (by linarith), sub_mul, div_mul_eq_mul_div, le_sub_iff_add_le,
            ← le_sub_iff_add_le', div_le_iff₀ hn0]
          nlinarith
        exact this.trans (hl.trans (le_abs_self _))
    have hpos : 0 < d * (k + 1) / 2 := by positivity
    have hgk : (k + 1)⁻¹ ≤ g n := by
      rcases le_total r n with h | h
      · have hc : (r : ℝ) ≤ n := by exact_mod_cast h
        have : k = n - r := by rw [hk, abs_of_nonneg (by linarith)]
        simp only [g, ite_eq_left h, this]
        linarith [hB0 n]
      · have hc : (n : ℝ) ≤ r := by exact_mod_cast h
        have : k = r - n := by rw [hk, abs_of_nonpos (by linarith)]; ring
        simp only [g, ite_eq_left h, this]
        linarith [hA0 n]
    have hx0 : 0 < x := by linarith
    calc |Real.log (x / n)|⁻¹ ≤ (|x - n| / (2 * x))⁻¹ :=
          inv_anti₀ (div_pos (by linarith) (by linarith)) hlog
      _ = 2 * x / |x - n| := by rw [inv_div]
      _ ≤ 2 * x / (d * (k + 1) / 2) := div_le_div_of_nonneg_left (by positivity) hpos hdist
      _ = 4 * x / d * (k + 1)⁻¹ := by field_simp; ring
      _ ≤ 4 * x / d * g n := mul_le_mul_of_nonneg_left hgk (by positivity)
  have hharm : ∀ M : ℕ, ∑ j ∈ Finset.range M, ((j : ℝ) + 1)⁻¹ ≤ 1 + Real.log M := by
    intro M
    have h := harmonic_le_one_add_log M
    simp only [harmonic] at h
    push_cast at h
    simpa using h
  have hA : ∑ n ∈ Finset.range N, (if r ≤ n then ((n : ℝ) - r + 1)⁻¹ else 0)
      ≤ 1 + Real.log N := by
    have hsub : ∑ n ∈ Finset.range N, (if r ≤ n then ((n : ℝ) - r + 1)⁻¹ else 0)
        ≤ ∑ n ∈ Finset.range (r + N), (if r ≤ n then ((n : ℝ) - r + 1)⁻¹ else 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun n _ _ => hA0 n
    refine hsub.trans (le_of_eq_of_le ?_ (hharm N))
    rw [Finset.sum_range_add,
      Finset.sum_eq_zero (fun n hn => ite_eq_right (by simp at hn; omega)), zero_add]
    apply Finset.sum_congr rfl
    intro k _
    rw [ite_eq_left (by omega)]
    push_cast
    ring_nf
  have hB : ∑ n ∈ Finset.range N, (if n ≤ r then ((r : ℝ) - n + 1)⁻¹ else 0)
      ≤ 1 + Real.log (r + 1) := by
    have hsub : ∑ n ∈ Finset.range N, (if n ≤ r then ((r : ℝ) - n + 1)⁻¹ else 0)
        ≤ ∑ n ∈ Finset.range ((r + 1) + N), (if n ≤ r then ((r : ℝ) - n + 1)⁻¹ else 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun n _ _ => hB0 n
    have h := hharm (r + 1)
    push_cast at h
    refine hsub.trans (le_of_eq_of_le ?_ h)
    rw [Finset.sum_range_add,
      Finset.sum_eq_zero (s := Finset.range N) (fun n _ => ite_eq_right (by omega)), add_zero,
      ← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ r := by simp at hj; omega
    rw [ite_eq_left (by omega), show r + 1 - 1 - j = r - j by omega, Nat.cast_sub hj']
    ring_nf
  have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hl2 := Real.log_two_gt_d9
  have hl3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h3x : Real.log (3 * x) = Real.log 3 + Real.log x :=
    Real.log_mul (by norm_num) (by linarith)
  have hlN : Real.log N ≤ Real.log (3 * x) := Real.log_le_log hN_pos hN_le
  have hlr : Real.log ((r : ℝ) + 1) ≤ Real.log (3 * x) :=
    Real.log_le_log (by positivity) (by linarith)
  have hsum : ∑ n ∈ Finset.range N, g n ≤ 10 * Real.log x := by
    simp only [g]
    rw [Finset.sum_add_distrib]
    norm_num at hl2
    linarith
  have hx0 : 0 < x := by linarith
  calc ∑ n ∈ (Finset.range N).filter (fun n : ℕ => x / 2 < n ∧ (n : ℝ) < 2 * x),
          |Real.log (x / n)|⁻¹
      ≤ ∑ n ∈ (Finset.range N).filter (fun n : ℕ => x / 2 < n ∧ (n : ℝ) < 2 * x),
          4 * x / d * g n := Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.range N, 4 * x / d * g n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun n _ _ => mul_nonneg (by positivity) (hg_nonneg n))
    _ = 4 * x / d * ∑ n ∈ Finset.range N, g n := by rw [Finset.mul_sum]
    _ ≤ 4 * x / d * (10 * Real.log x) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 40 * (x / d) * Real.log x := by ring

/-! ### The Perron error sum -/

private lemma rpow_neg_one_add_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) (hN : 1 ≤ N) :
    ((N : ℝ) + 1) ^ (-(1 + ε)) ≤ ((N : ℝ) ^ (-ε) - ((N : ℝ) + 1) ^ (-ε)) / ε := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (0 : ℝ) < N + 1 := by linarith
  have hq : (0:ℝ) < N / (N + 1) := by positivity
  have hsplit : (N : ℝ) ^ (-ε) = ((N : ℝ) + 1) ^ (-ε) * ((N : ℝ) / (N + 1)) ^ (-ε) := by
    rw [← Real.mul_rpow hN1.le hq.le]; congr 1; field_simp
  have hlog : Real.log ((N : ℝ) / (N + 1)) ≤ -(1 / (N + 1)) := by
    have := Real.log_le_sub_one_of_pos hq
    have h2 : (N : ℝ) / (N + 1) - 1 = -(1 / (N + 1)) := by field_simp; ring
    linarith
  have hbern : 1 + ε / (N + 1) ≤ ((N : ℝ) / (N + 1)) ^ (-ε) := by
    rw [Real.rpow_def_of_pos hq]
    have := Real.add_one_le_exp (ε / (N + 1))
    have h3 : ε / (N + 1) ≤ Real.log ((N : ℝ) / (N + 1)) * -ε := by
      rw [show ε / (N + 1) = -(1 / (N + 1)) * -ε by ring]
      exact mul_le_mul_of_nonpos_right hlog (by linarith)
    linarith [Real.exp_le_exp.mpr h3]
  have hpow : ((N : ℝ) + 1) ^ (-(1 + ε)) = ((N : ℝ) + 1) ^ (-ε) / (N + 1) := by
    rw [show -(1 + ε) = -ε - 1 by ring, Real.rpow_sub hN1, Real.rpow_one]
  have hA : 0 ≤ ((N : ℝ) + 1) ^ (-ε) := by positivity
  rw [hpow, le_div_iff₀ hε, hsplit]
  have : ((N : ℝ) + 1) ^ (-ε) * (1 + ε / (N + 1)) ≤
      ((N : ℝ) + 1) ^ (-ε) * ((N : ℝ) / (N + 1)) ^ (-ε) := mul_le_mul_of_nonneg_left hbern hA
  have h4 : ((N : ℝ) + 1) ^ (-ε) * (1 + ε / (N + 1)) =
      ((N : ℝ) + 1) ^ (-ε) + ((N : ℝ) + 1) ^ (-ε) / (N + 1) * ε := by field_simp
  linarith

private lemma sum_range_rpow_neg_one_add_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∑ n ∈ Finset.range N, (n : ℝ) ^ (-(1 + ε)) ≤ 1 + 1 / ε := by
  have key : ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ (-(1 + ε)) ≤ 1 + 1 / ε - (N : ℝ) ^ (-ε) / ε := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      rw [Finset.sum_range_succ, Finset.sum_range_one, Nat.cast_zero, Nat.cast_one,
        Real.zero_rpow (by linarith), Real.one_rpow, Real.one_rpow]
      linarith
    | succ k hk ih =>
      rw [Finset.sum_range_succ]
      have := rpow_neg_one_add_le hε k hk
      push_cast
      have h2 : ((k : ℝ) ^ (-ε) - ((k : ℝ) + 1) ^ (-ε)) / ε =
          (k : ℝ) ^ (-ε) / ε - ((k : ℝ) + 1) ^ (-ε) / ε := sub_div _ _ _
      linarith
  have hnn : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ (-(1 + ε)) := fun n => by positivity
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Finset.sum_range_zero]; positivity
  · calc ∑ n ∈ Finset.range N, (n : ℝ) ^ (-(1 + ε))
        ≤ ∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ (-(1 + ε)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => by simp at hx ⊢; omega)
            (fun n _ _ => hnn n)
      _ ≤ 1 + 1 / ε - (N : ℝ) ^ (-ε) / ε := key N hN
      _ ≤ 1 + 1 / ε := by
          have : 0 ≤ (N : ℝ) ^ (-ε) / ε := by positivity
          linarith

private lemma summable_vonMangoldt_mul_rpow_and_tsum_le {x : ℝ} (hx : 3 / 2 ≤ x) :
    Summable (fun n : ℕ => Λ n * (x / n) ^ (1 + 1 / Real.log x)) ∧
      ∑' n : ℕ, Λ n * (x / n) ^ (1 + 1 / Real.log x) ≤ 30 * x * Real.log x ^ 2 := by
  set L := Real.log x with hL
  have hx0 : 0 < x := by linarith
  have hL3 : 1 / 3 ≤ L := by
    have := Real.one_sub_inv_le_log_of_pos hx0
    have : x⁻¹ ≤ 2 / 3 := by rw [inv_le_comm₀ hx0 (by norm_num)]; linarith
    linarith
  have hL0 : 0 < L := by linarith
  set δ := 1 / L with hδ
  have hδ0 : 0 < δ := by positivity
  have hxc : x ^ (1 + δ) = x * Real.exp 1 := by
    rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0, ← hL, hδ,
      mul_one_div_cancel hL0.ne']
  have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + δ / 2))) :=
    summable_of_sum_range_le (fun n => by positivity)
      (sum_range_rpow_neg_one_add_le (half_pos hδ0))
  have htsum : ∑' n : ℕ, (n : ℝ) ^ (-(1 + δ / 2)) ≤ 1 + 1 / (δ / 2) :=
    Real.tsum_le_of_sum_range_le (fun n => by positivity)
      (sum_range_rpow_neg_one_add_le (half_pos hδ0))
  set g : ℕ → ℝ := fun n => 6 * x * L * (n : ℝ) ^ (-(1 + δ / 2)) with hg
  have hle : ∀ n : ℕ, Λ n * (x / n) ^ (1 + δ) ≤ g n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ArithmeticFunction.map_zero, zero_mul]
      simp only [hg]
      positivity
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hΛ : Λ n ≤ (n : ℝ) ^ (δ / 2) / (δ / 2) :=
      vonMangoldt_le_log.trans (Real.log_le_rpow_div hn0.le (half_pos hδ0))
    rw [Real.div_rpow hx0.le hn0.le, hxc]
    have hp : (n : ℝ) ^ (δ / 2) / (n : ℝ) ^ (1 + δ) = (n : ℝ) ^ (-(1 + δ / 2)) := by
      rw [← Real.rpow_sub hn0]; congr 1; ring
    have hnc : 0 < (n : ℝ) ^ (1 + δ) := by positivity
    calc Λ n * (x * Real.exp 1 / (n : ℝ) ^ (1 + δ))
        ≤ (n : ℝ) ^ (δ / 2) / (δ / 2) * (x * 3 / (n : ℝ) ^ (1 + δ)) := by
          apply mul_le_mul hΛ _ (by positivity) (by positivity)
          gcongr
      _ = 6 * x * (1 / δ) * ((n : ℝ) ^ (δ / 2) / (n : ℝ) ^ (1 + δ)) := by
          field_simp; ring
      _ = g n := by rw [hp, hg, hδ, one_div_one_div]
  have hgs : Summable g := hsum.mul_left (6 * x * L)
  have hnn : ∀ n : ℕ, 0 ≤ Λ n * (x / n) ^ (1 + δ) :=
    fun n => mul_nonneg vonMangoldt_nonneg (by positivity)
  have hs : Summable (fun n : ℕ => Λ n * (x / n) ^ (1 + δ)) :=
    Summable.of_nonneg_of_le hnn hle hgs
  refine ⟨hs, ?_⟩
  calc ∑' n : ℕ, Λ n * (x / n) ^ (1 + δ)
      ≤ ∑' n, g n := hs.tsum_le_tsum hle hgs
    _ = 6 * x * L * ∑' n : ℕ, (n : ℝ) ^ (-(1 + δ / 2)) := by rw [hg, tsum_mul_left]
    _ ≤ 6 * x * L * (1 + 1 / (δ / 2)) := by gcongr
    _ = 6 * x * L * (1 + 2 * L) := by rw [hδ]; field_simp
    _ ≤ 30 * x * L ^ 2 := by
        have := mul_le_mul_of_nonneg_left hL3 (le_of_lt (mul_pos hx0 hL0))
        nlinarith

/-- **The Perron error sum at `c = 1 + 1/log x`.** There is an absolute constant `C` such that,
whenever `x - 1/2` is a positive integer, `c = 1 + 1/log x` and `R > 0`, the sum
`∑ Λ(n) (x/n)^c / (R |log (x/n)|)` converges and is at most `C x log² x / R`. -/
theorem exists_tsum_vonMangoldt_mul_div_abs_log_le :
    ∃ C : ℝ, ∀ x R : ℝ, (∃ m : ℕ, 0 < m ∧ x = m + 1 / 2) → 0 < R →
      Summable (fun n : ℕ => Λ n * (x / n) ^ (1 + 1 / Real.log x) /
          (R * |Real.log (x / n)|)) ∧
      ∑' n : ℕ, Λ n * (x / n) ^ (1 + 1 / Real.log x) / (R * |Real.log (x / n)|) ≤
        C * (x * Real.log x ^ 2 / R) := by
  obtain ⟨C₂, hC₂⟩ := exists_sum_inv_abs_log_div_le
  set C₃ := max C₂ 0 with hC₃
  have hC₃0 : 0 ≤ C₃ := le_max_right _ _
  refine ⟨32 * C₃ + 120, ?_⟩
  rintro x R ⟨m, hm, rfl⟩ hR
  set x : ℝ := (m : ℝ) + 1 / 2 with hxdef
  have hx : 3 / 2 ≤ x := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hL
  set c := 1 + 1 / L with hc
  obtain ⟨hs, ht⟩ := summable_vonMangoldt_mul_rpow_and_tsum_le hx
  rw [← hL, ← hc] at hs ht
  set h : ℕ → ℝ := fun n => Λ n * (x / n) ^ c with hh
  have hh0 : ∀ n, 0 ≤ h n := fun n => mul_nonneg vonMangoldt_nonneg (by positivity)
  have hf0 : ∀ n : ℕ, 0 ≤ h n / (R * |Real.log (x / n)|) := fun n =>
    div_nonneg (hh0 n) (by positivity)
  -- bound through a lower bound on `|log (x/n)|`
  have hdivle : ∀ n : ℕ, ∀ a : ℝ, 0 < a → a ≤ |Real.log (x / n)| →
      h n / (R * |Real.log (x / n)|) ≤ h n / (R * a) := fun n a ha hle =>
    div_le_div_of_nonneg_left (hh0 n) (by positivity) (mul_le_mul_of_nonneg_left hle hR.le)
  have hRHS0 : 0 ≤ x * L ^ 2 / R := by positivity
  have hL0 : 0 < L := Real.log_pos (by linarith)
  change Summable (fun n : ℕ => h n / (R * |Real.log (x / n)|)) ∧
    ∑' n : ℕ, h n / (R * |Real.log (x / n)|) ≤ _
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · -- `x = 3/2`
    have hm1 : m = 1 := by omega
    have hx32 : x = 3 / 2 := by rw [hxdef, hm1]; norm_num
    have hlow : ∀ n : ℕ, 1 ≤ n → 1 / 4 ≤ |Real.log (x / n)| := by
      intro n hn
      rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · have : n = 1 := by omega
        subst this
        have h1 := Real.one_sub_inv_le_log_of_pos hx0
        rw [hx32] at h1 ⊢
        norm_num at h1 ⊢
        rw [abs_of_nonneg (by linarith)]; linarith
      · have hn0 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        have hq : 0 < x / n := by positivity
        have h1 := Real.log_le_sub_one_of_pos hq
        have h2 : x / n ≤ 3 / 4 := by
          rw [div_le_iff₀ (by linarith), hx32]; linarith
        rw [abs_of_neg (by linarith)]; linarith
    have hle : ∀ n : ℕ, h n / (R * |Real.log (x / n)|) ≤ 4 / R * h n := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hh]
      · calc h n / (R * |Real.log (x / n)|) ≤ h n / (R * (1 / 4)) :=
            hdivle n _ (by norm_num) (hlow n hn)
          _ = 4 / R * h n := by field_simp
    have hfs := Summable.of_nonneg_of_le hf0 hle (hs.mul_left _)
    refine ⟨hfs, ?_⟩
    calc ∑' n : ℕ, h n / (R * |Real.log (x / n)|)
        ≤ ∑' n : ℕ, 4 / R * h n := hfs.tsum_le_tsum hle (hs.mul_left _)
      _ = 4 / R * ∑' n : ℕ, h n := tsum_mul_left
      _ ≤ 4 / R * (30 * x * L ^ 2) := by gcongr
      _ = 120 * (x * L ^ 2 / R) := by ring
      _ ≤ (32 * C₃ + 120) * (x * L ^ 2 / R) := by gcongr; linarith
  · -- `x ≥ 2`: split at `x/2` and `2x`
    have hx2 : 2 ≤ x := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      linarith
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hx2
    set S := (Finset.range ⌈2 * x⌉₊).filter (fun n : ℕ => x / 2 < n ∧ (n : ℝ) < 2 * x) with hS
    have hint : ∀ k : ℤ, (k : ℝ) ≠ x := by
      intro k hk
      have h2 : ((2 * k : ℤ) : ℝ) = ((2 * m + 1 : ℕ) : ℤ) := by
        push_cast; rw [hk, hxdef]; ring
      have h3 := Int.cast_injective (α := ℝ) h2
      omega
    have hround : |x - round x| = 1 / 2 := by
      have : round x = ((m + 1 : ℕ) : ℤ) := by
        rw [round_eq, Int.floor_eq_iff]; push_cast; rw [hxdef]; constructor <;> linarith
      rw [this, hxdef]; push_cast
      rw [show (m : ℝ) + 1 / 2 - (m + 1) = -(1 / 2) by ring, abs_neg, abs_of_pos (by norm_num)]
    have hmid := hC₂ x hx2 hint
    rw [hround, ← hL] at hmid
    have hmid' : ∑ n ∈ S, |Real.log (x / n)|⁻¹ ≤ C₃ * (2 * x) * L := by
      calc _ ≤ C₂ * (x / (1 / 2)) * L := hmid
        _ ≤ C₃ * (x / (1 / 2)) * L := by gcongr; exact le_max_left _ _
        _ = C₃ * (2 * x) * L := by ring
    set g : ℕ → ℝ := fun n => if n ∈ S then 16 * L / R * |Real.log (x / n)|⁻¹ else 0 with hg
    have hle : ∀ n : ℕ, h n / (R * |Real.log (x / n)|) ≤ g n + 2 / R * h n := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hh, hg, hS]
      have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hq : 0 < x / n := by positivity
      by_cases hnS : n ∈ S
      · have hmem := (Finset.mem_filter.mp hnS).2
        have hlpos : 0 < |Real.log (x / n)| := by
          refine abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hq ?_)
          intro h1
          rw [div_eq_one_iff_eq (by positivity)] at h1
          exact hint n (by exact_mod_cast h1.symm)
        have hΛ : Λ n ≤ 2 * L := by
          refine vonMangoldt_le_log.trans ?_
          have : Real.log n ≤ Real.log (2 * x) := Real.log_le_log (by positivity) hmem.2.le
          rw [Real.log_mul (by norm_num) hx0.ne'] at this
          linarith
        have hc3 : c ≤ 3 := by
          rw [hc]
          have : 1 / L ≤ 2 := by
            rw [div_le_iff₀ hL0]; linarith
          linarith
        have hpow : (x / n) ^ c ≤ 8 := by
          have h1 : x / n ≤ 2 := by
            rw [div_le_iff₀ (by positivity)]; linarith [hmem.1]
          calc (x / n) ^ c ≤ 2 ^ c := Real.rpow_le_rpow hq.le h1 (by positivity)
            _ ≤ 2 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc3
            _ = 8 := by norm_num
        have hhn : h n ≤ 16 * L := by
          calc h n = Λ n * (x / n) ^ c := rfl
            _ ≤ 2 * L * 8 := mul_le_mul hΛ hpow (by positivity) (by positivity)
            _ = 16 * L := by ring
        have hgn : g n = 16 * L / R * |Real.log (x / n)|⁻¹ := by rw [hg]; simp [hnS]
        calc h n / (R * |Real.log (x / n)|) ≤ 16 * L / (R * |Real.log (x / n)|) :=
              div_le_div_of_nonneg_right hhn (by positivity)
          _ = g n := by rw [hgn]; field_simp
          _ ≤ g n + 2 / R * h n := le_add_of_nonneg_right (by have := hh0 n; positivity)
      · have hout : x / 2 ≥ n ∨ (n : ℝ) ≥ 2 * x := by
          by_contra hcon
          push Not at hcon
          exact hnS (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_ceil.mpr hcon.2), hcon⟩)
        have hlow : 1 / 2 ≤ |Real.log (x / n)| := by
          rcases hout with h1 | h1
          · have : 2 ≤ x / n := by rw [le_div_iff₀ (by positivity)]; linarith
            have := Real.log_le_log (by norm_num) this
            rw [abs_of_nonneg (by linarith)]; linarith
          · have : x / n ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
            have h2 := Real.log_le_log hq this
            rw [one_div, Real.log_inv] at h2
            rw [abs_of_neg (by linarith)]; linarith
        have hgn : g n = 0 := by rw [hg]; simp [hnS]
        calc h n / (R * |Real.log (x / n)|) ≤ h n / (R * (1 / 2)) :=
              hdivle n _ (by norm_num) hlow
          _ = g n + 2 / R * h n := by rw [hgn]; field_simp; ring
    have hgsum : ∑' n : ℕ, g n = ∑ n ∈ S, 16 * L / R * |Real.log (x / n)|⁻¹ := by
      rw [tsum_eq_sum (s := S) (fun n hn => by rw [hg]; simp [hn])]
      exact Finset.sum_congr rfl (fun n hn => by rw [hg]; simp [hn])
    have hgs : Summable g :=
      summable_of_ne_finset_zero (s := S) (fun n hn => by rw [hg]; simp [hn])
    have hfs := Summable.of_nonneg_of_le hf0 hle (hgs.add (hs.mul_left _))
    refine ⟨hfs, ?_⟩
    calc ∑' n : ℕ, h n / (R * |Real.log (x / n)|)
        ≤ ∑' n : ℕ, (g n + 2 / R * h n) := hfs.tsum_le_tsum hle (hgs.add (hs.mul_left _))
      _ = ∑' n : ℕ, g n + 2 / R * ∑' n : ℕ, h n := by
          rw [hgs.tsum_add (hs.mul_left _), tsum_mul_left]
      _ ≤ 16 * L / R * (C₃ * (2 * x) * L) + 2 / R * (30 * x * L ^ 2) := by
          rw [hgsum, ← Finset.mul_sum]
          gcongr
      _ = (32 * C₃ + 60) * (x * L ^ 2 / R) := by field_simp; ring
      _ ≤ (32 * C₃ + 120) * (x * L ^ 2 / R) := by gcongr; linarith

/-! ### The truncated Perron formula for `ψ(x)` -/

/-- **The truncated Perron formula for `ψ(x)`.** For real `x > 1` not a prime power, `c > 1`
and `R > 0`,
`|ψ(x) - (1/2π) ∫_{-R}^{R} -ζ'/ζ(c + it) x^{c+it}/(c + it) dt|
  ≤ (1/π) ∑ Λ(n) (x/n)^c / (R |log (x/n)|)`. -/
theorem norm_chebyshevPsi_sub_truncated_integral_le {x c R : ℝ} (hx : 1 < x)
    (hpp : ∀ n : ℕ, (n : ℝ) = x → ¬ IsPrimePow n) (hc : 1 < c) (hR : 0 < R) :
    ‖(Chebyshev.psi x : ℂ) - (1 / (2 * Real.pi)) *
        ∫ t in (-R)..R, -(deriv riemannZeta (c + t * I) / riemannZeta (c + t * I)) *
          ((x : ℂ) ^ (c + t * I) / (c + t * I))‖ ≤
      1 / Real.pi * ∑' n : ℕ, Λ n * (x / n) ^ c / (R * |Real.log (x / n)|) := by
  classical
  have hx0 : 0 < x := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  set a : ℕ → ℂ := fun n => (Λ n : ℂ) with ha
  have hsum : LSeriesSummable a (c : ℂ) := LSeriesSummable_vonMangoldt (by simpa using hc)
  have hzne : ∀ t : ℝ, (c : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro t h
    exact hc0.ne' (by simpa using congrArg Complex.re h)
  have hre : ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * I).re = c := by intro t; simp
  have hΛx : ∀ n : ℕ, (n : ℝ) = x → Λ n = 0 := fun n hn =>
    vonMangoldt_eq_zero_iff.mpr (hpp n hn)
  -- the weights
  set w : ℕ → ℝ := fun n => x ^ c * ‖LSeries.term a (c : ℂ) n‖ with hwdef
  have hwS : Summable w := (summable_norm_iff.mpr hsum).mul_left _
  have hwval : ∀ n : ℕ, n ≠ 0 → w n = Λ n * (x / n) ^ c := by
    intro n hn
    have hn0 : 0 < n := Nat.pos_of_ne_zero hn
    simp only [hwdef, LSeries.term_of_ne_zero hn, norm_div,
      Complex.norm_natCast_cpow_of_pos hn0, Complex.ofReal_re, ha, Complex.norm_real,
      Real.norm_of_nonneg vonMangoldt_nonneg]
    rw [Real.div_rpow hx0.le (Nat.cast_nonneg n)]
    ring
  set B : ℕ → ℝ := fun n => Λ n * (x / n) ^ c / (R * |Real.log (x / n)|) with hBdef
  have hB0 : ∀ n, 0 ≤ B n := fun n =>
    div_nonneg (mul_nonneg vonMangoldt_nonneg (by positivity)) (by positivity)
  have hBs : Summable B := by
    refine Summable.of_norm_bounded_eventually_nat (hwS.div_const (R * Real.log 2)) ?_
    filter_upwards [eventually_ge_atTop ⌈2 * x⌉₊, eventually_ge_atTop 1] with n hn hn1
    have hn2 : 2 * x ≤ n := Nat.ceil_le.mp hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hlog : Real.log 2 ≤ |Real.log (x / n)| := by
      have h1 : x / n ≤ 1 / 2 := by rw [div_le_iff₀ hnpos]; linarith
      have h2 := Real.log_le_log (by positivity) h1
      rw [one_div, Real.log_inv] at h2
      rw [abs_of_neg (by linarith [Real.log_pos (one_lt_two : (1 : ℝ) < 2)])]; linarith
    rw [Real.norm_of_nonneg (hB0 n), hwval n (by omega)]
    exact div_le_div_of_nonneg_left (mul_nonneg vonMangoldt_nonneg (by positivity))
      (mul_pos hR (Real.log_pos one_lt_two)) (mul_le_mul_of_nonneg_left hlog hR.le)
  -- the truncated kernels
  set K : ℕ → ℂ := fun n => PerronKernel.perronKernel (x / n) c R with hKdef
  set D : ℕ → ℂ := fun n => a n * (if 1 < x / n then 1 else 0) with hDdef
  have hkey : ∀ n : ℕ, ‖D n - a n * K n‖ ≤ B n / Real.pi := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hDdef, ha, hBdef]
    rcases eq_or_ne (n : ℝ) x with hnx | hnx
    · simp [hDdef, ha, hBdef, hΛx n hnx]
    have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hxn : 0 < x / n := div_pos hx0 hnR
    have hxn1 : x / n ≠ 1 := fun h => hnx ((div_eq_one_iff_eq hnR.ne').mp h).symm
    have hb := PerronKernel.perron_bound hxn hxn1 hc0 hR
    rw [← Real.rpow_def_of_pos hxn] at hb
    rw [show D n - a n * K n = -(a n * (K n - (if 1 < x / n then (1 : ℂ) else 0))) by
      simp only [hDdef]; ring, norm_neg, norm_mul, ha, Complex.norm_real,
      Real.norm_of_nonneg vonMangoldt_nonneg]
    calc Λ n * ‖K n - (if 1 < x / n then (1 : ℂ) else 0)‖
        ≤ Λ n * ((x / n) ^ c / |Real.log (x / n)| / R / Real.pi) :=
          mul_le_mul_of_nonneg_left hb vonMangoldt_nonneg
      _ = B n / Real.pi := by
          simp only [hBdef]
          ring
  -- the interchange of the sum and the truncated integral
  have hHS : HasSum (fun n : ℕ => a n * K n)
      ((1 / (2 * Real.pi)) * ∫ t in (-R)..R,
        LSeries a ((c : ℂ) + (t : ℂ) * I) * ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
          ((c : ℂ) + (t : ℂ) * I))) := by
    have hKc : Continuous fun t : ℝ =>
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I) :=
      (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx0.ne'))).div
        (by fun_prop) hzne
    have hmain := hsum.hasSum_intervalIntegral_term_vertical_mul hKc (B := x ^ c / c)
      (fun t => by
        rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre]
        exact div_le_div_of_nonneg_left (by positivity) hc0
          ((hre t).symm.le.trans (Complex.re_le_norm _))) R
    refine (hmain.mul_left (1 / (2 * Real.pi) : ℂ)).congr_fun fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ha]
    · simp only [hKdef, PerronKernel.perronKernel]
      rw [show (fun t : ℝ => LSeries.term a ((c : ℂ) + (t : ℂ) * I) n *
          ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))) =
          fun t : ℝ => a n * ((((x / n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
            ((c : ℂ) + (t : ℂ) * I)) from funext fun t => by
              rw [← LSeries.term_mul_cpow_div a hn hx0, mul_div_assoc],
        intervalIntegral.integral_const_mul]
      push_cast
      ring
  -- the discrete sum
  have hDzero : ∀ n : ℕ, n ∉ Finset.Icc 1 ⌊x⌋₊ → D n = 0 := by
    intro n hnmem
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hDdef, ha]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnx : ¬ ((n : ℝ) ≤ x) := fun hlt => hnmem (Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr hn, Nat.le_floor hlt⟩)
      have hlt1 : ¬ 1 < x / n := by
        rw [lt_div_iff₀ hnR, one_mul]; exact fun h => hnx h.le
      simp [hDdef, hlt1]
  have hDsum : ∑' n, D n = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n := by
    rw [tsum_eq_sum hDzero]
    refine Finset.sum_congr rfl fun n hnmem => ?_
    simp only [Finset.mem_Icc] at hnmem
    have hn : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hnmem.1
    have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0.le).mp hnmem.2
    rcases eq_or_ne (n : ℝ) x with hnx | hnx
    · simp [hDdef, ha, hΛx n hnx]
    have hgt1 : 1 < x / n := by
      rw [lt_div_iff₀ hnR, one_mul]; exact lt_of_le_of_ne hnle hnx
    simp [hDdef, hgt1]
  have hDsummable : Summable D := summable_of_ne_finset_zero hDzero
  have hpsi : (Chebyshev.psi x : ℂ) = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n := by
    rw [Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
    push_cast
    rfl
  have hint : (∫ t in (-R)..R, -(deriv riemannZeta (c + t * I) / riemannZeta (c + t * I)) *
        ((x : ℂ) ^ (c + t * I) / (c + t * I))) =
      ∫ t in (-R)..R, LSeries a ((c : ℂ) + (t : ℂ) * I) *
        ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [ha]
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by rw [hre]; exact hc), neg_div]
  have hns : Summable fun n => ‖D n - a n * K n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hkey (hBs.div_const _)
  rw [hint, hpsi, ← hDsum, ← hHS.tsum_eq, ← hDsummable.tsum_sub hHS.summable]
  calc ‖∑' n, (D n - a n * K n)‖ ≤ ∑' n, ‖D n - a n * K n‖ := norm_tsum_le_tsum_norm hns
    _ ≤ ∑' n, B n / Real.pi := hns.tsum_le_tsum hkey (hBs.div_const _)
    _ = 1 / Real.pi * ∑' n, B n := by rw [tsum_div_const]; ring

/-- **The truncated Perron formula at `c = 1 + 1/log x`.** There is an absolute constant `C` such
that, when `x - 1/2` is a positive integer and `R > 0`, with `c = 1 + 1/log x`,
`|ψ(x) - (1/2π) ∫_{-R}^{R} -ζ'/ζ(c + it) x^{c+it}/(c + it) dt| ≤ C x log² x / R`. -/
theorem exists_norm_chebyshevPsi_sub_truncated_integral_le_log_sq :
    ∃ C : ℝ, ∀ x R : ℝ, (∃ n : ℕ, 0 < n ∧ x = n + 1 / 2) → 0 < R →
      ‖(Chebyshev.psi x : ℂ) - (1 / (2 * Real.pi)) *
          ∫ t in (-R)..R,
            -(deriv riemannZeta ((1 + 1 / Real.log x : ℝ) + t * I) /
                riemannZeta ((1 + 1 / Real.log x : ℝ) + t * I)) *
              ((x : ℂ) ^ ((1 + 1 / Real.log x : ℝ) + t * I) /
                ((1 + 1 / Real.log x : ℝ) + t * I))‖ ≤
        C * (x * Real.log x ^ 2 / R) := by
  obtain ⟨C₂, hC₂⟩ := exists_tsum_vonMangoldt_mul_div_abs_log_le
  refine ⟨C₂ / Real.pi, ?_⟩
  rintro x R hxn hR
  obtain ⟨m, hm, hxm⟩ := hxn
  have hx : 1 < x := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [hxm]; linarith
  have hpp : ∀ n : ℕ, (n : ℝ) = x → ¬ IsPrimePow n := by
    intro n hn
    exfalso
    have h3 : ((((n : ℤ) - m) : ℤ) : ℝ) = 1 / 2 := by push_cast; linarith
    rcases le_or_gt ((n : ℤ) - m) 0 with h | h
    · have : ((((n : ℤ) - m) : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h
      linarith
    · have : (1 : ℝ) ≤ ((((n : ℤ) - m) : ℤ) : ℝ) := by exact_mod_cast h
      linarith
  have hc : 1 < 1 + 1 / Real.log x := by
    have : 0 < 1 / Real.log x := one_div_pos.mpr (Real.log_pos hx)
    linarith
  have h1 := norm_chebyshevPsi_sub_truncated_integral_le hx hpp hc hR
  have h2 := (hC₂ x R ⟨m, hm, hxm⟩ hR).2
  refine h1.trans ?_
  calc 1 / Real.pi * _ ≤ 1 / Real.pi * (C₂ * (x * Real.log x ^ 2 / R)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = C₂ / Real.pi * (x * Real.log x ^ 2 / R) := by ring

/-! ### The truncated explicit formula -/

section Truncated

private lemma log_add_le {a b : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) :
    Real.log (a + b) ≤ Real.log a + b := by
  have h1 : a + b ≤ a * Real.exp b := by
    have := Real.add_one_le_exp b
    nlinarith
  calc Real.log (a + b) ≤ Real.log (a * Real.exp b) := Real.log_le_log (by linarith) h1
    _ = Real.log a + b := by rw [Real.log_mul (by linarith) (Real.exp_pos b).ne', Real.log_exp]

/-- A horizontal side of the contour: if `‖ζ'/ζ(σ + iτ)‖ ≤ a - bσ` on `[-U, c]` with `|τ| = R`,
then the integral of `-ζ'/ζ(s) x^s/s` along it is at most `x^c (a / log x + b / log² x) / R`. -/
private lemma norm_integral_horizontal_le {x : ℝ} (hx : 1 < x) {R τ : ℝ} (hR : 0 < R)
    (hτ : |τ| = R) {a b c U : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hU : 0 ≤ U) (hab : 0 ≤ a + b * U)
    (hle : ∀ σ : ℝ, -U ≤ σ → σ ≤ c →
      ‖deriv riemannZeta (σ + τ * I) / riemannZeta (σ + τ * I)‖ ≤ a - b * σ) :
    ‖∫ σ in (-U)..c, -(deriv riemannZeta (σ + τ * I) / riemannZeta (σ + τ * I)) *
        ((x : ℂ) ^ ((σ : ℂ) + τ * I) / ((σ : ℂ) + τ * I))‖ ≤
      x ^ c * (a / Real.log x + b / Real.log x ^ 2) / R := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  set g : ℝ → ℝ := fun σ => (a - b * σ) * x ^ σ / R with hg
  set Φ : ℝ → ℝ := fun σ => x ^ σ * ((a - b * σ) / Real.log x + b / Real.log x ^ 2) / R
    with hΦ
  have hderiv : ∀ σ : ℝ, HasDerivAt Φ (g σ) σ := by
    intro σ
    have h1 : HasDerivAt (fun σ : ℝ => x ^ σ) (x ^ σ * Real.log x) σ :=
      (Real.hasStrictDerivAt_const_rpow hx0 σ).hasDerivAt
    have h2 : HasDerivAt (fun σ : ℝ => (a - b * σ) / Real.log x + b / Real.log x ^ 2)
        (-b / Real.log x) σ := by
      have := (((hasDerivAt_id σ).const_mul b).const_sub a).div_const (Real.log x)
      simpa using this.add_const (b / Real.log x ^ 2)
    refine ((h1.mul h2).div_const R).congr_deriv ?_
    change _ = (a - b * σ) * x ^ σ / R
    field_simp
    ring
  have hgc : Continuous g := by
    have : Continuous (fun σ : ℝ => x ^ σ) :=
      continuous_const.rpow continuous_id (fun _ => Or.inl hx0.ne')
    simp only [hg]
    fun_prop
  have hint : ∫ σ in (-U)..c, g σ = Φ c - Φ (-U) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hderiv σ)
      (hgc.intervalIntegrable _ _)
  have hΦa : 0 ≤ Φ (-U) := by
    simp only [hΦ]
    have : 0 ≤ a - b * -U := by linarith
    positivity
  have hΦc : Φ c ≤ x ^ c * (a / Real.log x + b / Real.log x ^ 2) / R := by
    simp only [hΦ]
    have hxc : 0 < x ^ c := Real.rpow_pos_of_pos hx0 c
    gcongr
    linarith [mul_nonneg hb hc]
  have hle' : ∀ σ ∈ Set.Ioc (-U) c,
      ‖-(deriv riemannZeta (σ + τ * I) / riemannZeta (σ + τ * I)) *
        ((x : ℂ) ^ ((σ : ℂ) + τ * I) / ((σ : ℂ) + τ * I))‖ ≤ g σ := by
    rintro σ ⟨hσ1, hσ2⟩
    have hsT : R ≤ ‖(σ : ℂ) + τ * I‖ := by
      rw [← hτ]; simpa using Complex.abs_im_le_norm ((σ : ℂ) + τ * I)
    have hxs : ‖(x : ℂ) ^ ((σ : ℂ) + τ * I)‖ = x ^ σ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp
    have hxσ : 0 < x ^ σ := Real.rpow_pos_of_pos hx0 σ
    have h0 := hle σ hσ1.le hσ2
    rw [norm_mul, norm_neg, norm_div ((x : ℂ) ^ _), hxs]
    calc _ ≤ (a - b * σ) * (x ^ σ / R) :=
          mul_le_mul h0 (div_le_div_of_nonneg_left hxσ.le hR hsT) (by positivity)
            (le_trans (norm_nonneg _) h0)
      _ = g σ := by simp only [hg]; ring
  have hmain := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
    (by linarith) (Eventually.of_forall (fun σ hσ => hle' σ hσ)) (hgc.intervalIntegrable _ _)
  rw [hint] at hmain
  linarith

/-- The left side of the contour tends to `0` as `U = 2k + 1 → ∞`. -/
private lemma tendsto_integral_left_side (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ s : ℂ, s.re ≤ -1 → (∀ m : ℕ, 0 < m → 1 ≤ ‖s + 2 * (m : ℂ)‖) →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ K * Real.log (2 * ‖s‖))
    {x : ℝ} (hx : 1 < x) {R : ℝ} (hR : 1 ≤ R) :
    Tendsto (fun k : ℕ => ∫ t in (-R)..R,
      -(deriv riemannZeta (((-((2 * k + 1 : ℕ) : ℝ) : ℝ) : ℂ) + t * I) /
        riemannZeta (((-((2 * k + 1 : ℕ) : ℝ) : ℝ) : ℂ) + t * I)) *
        ((x : ℂ) ^ (((-((2 * k + 1 : ℕ) : ℝ) : ℝ) : ℂ) + t * I) /
          (((-((2 * k + 1 : ℕ) : ℝ) : ℝ) : ℂ) + t * I)))
      atTop (𝓝 0) := by
  have hx0 : 0 < x := by linarith
  set r : ℝ := x⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hx
  set L : ℝ := Real.log (2 * R) + 2 with hL
  have hL0 : 0 ≤ L := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * R by linarith); linarith
  set B : ℕ → ℝ := fun k => K * ((4 * k + L) * r ^ k) * (2 * R) with hB
  have hBt : Tendsto B atTop (𝓝 0) := by
    have h1 := tendsto_self_mul_const_pow_of_lt_one hr0 hr1
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have h3 : Tendsto (fun k : ℕ => (4 * k + L) * r ^ k) atTop (𝓝 0) := by
      have := (h1.const_mul 4).add (h2.const_mul L)
      simp only [mul_zero, add_zero] at this
      exact this.congr fun k => by ring
    simpa [hB] using (h3.const_mul K).mul_const (2 * R)
  refine squeeze_zero_norm' ?_ hBt
  filter_upwards with k
  set U : ℕ := 2 * k + 1 with hU
  have hU1 : (1 : ℝ) ≤ U := by
    rw [hU]; push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hbound : ∀ t ∈ Set.uIoc (-R) R,
      ‖-(deriv riemannZeta (((-(U : ℝ) : ℝ) : ℂ) + t * I) /
          riemannZeta (((-(U : ℝ) : ℝ) : ℂ) + t * I)) *
        ((x : ℂ) ^ (((-(U : ℝ) : ℝ) : ℂ) + t * I) / (((-(U : ℝ) : ℝ) : ℂ) + t * I))‖ ≤
      K * ((4 * k + L) * r ^ k) := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    set s : ℂ := ((-(U : ℝ) : ℝ) : ℂ) + t * I with hs
    have hsre : s.re = -(U : ℝ) := by simp [hs]
    have hsim : s.im = t := by simp [hs]
    have h1s : 1 ≤ ‖s‖ := by
      calc (1 : ℝ) ≤ |s.re| := by rw [hsre, abs_neg, abs_of_pos (by linarith)]; exact hU1
        _ ≤ ‖s‖ := Complex.abs_re_le_norm s
    have hsle : ‖s‖ ≤ U + R := by
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ U + R := by
          rw [hsre, hsim, abs_neg, abs_of_pos (by linarith)]
          linarith [abs_le.mpr ⟨ht.1.le, ht.2⟩]
    have hxs : ‖(x : ℂ) ^ s‖ ≤ r ^ k := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, hsre, Real.rpow_neg hx0.le,
        Real.rpow_natCast, ← inv_pow]
      exact pow_le_pow_of_le_one hr0 hr1.le (by omega)
    have hdist : ∀ m : ℕ, 0 < m → 1 ≤ ‖s + 2 * (m : ℂ)‖ := by
      intro m _
      have hre : (s + 2 * (m : ℂ)).re = (((2 * (m : ℤ) - 2 * k - 1 : ℤ)) : ℝ) := by
        simp [hs, hU]; ring
      have hne : (2 * (m : ℤ) - 2 * k - 1 : ℤ) ≠ 0 := by omega
      have h1 : (1 : ℝ) ≤ |(((2 * (m : ℤ) - 2 * k - 1 : ℤ)) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
      calc (1 : ℝ) ≤ _ := h1
        _ = |(s + 2 * (m : ℂ)).re| := by rw [hre]
        _ ≤ _ := Complex.abs_re_le_norm _
    have h := hK s (by rw [hsre]; linarith) hdist
    have hlog : Real.log (2 * ‖s‖) ≤ 4 * k + L := by
      calc Real.log (2 * ‖s‖) ≤ Real.log (2 * R + 2 * U) :=
            Real.log_le_log (by linarith) (by linarith)
        _ ≤ Real.log (2 * R) + 2 * U := log_add_le (by linarith) (by linarith)
        _ = 4 * k + L := by rw [hL, hU]; push_cast; ring
    have hLd : ‖deriv riemannZeta s / riemannZeta s‖ ≤ K * (4 * k + L) :=
      h.trans (mul_le_mul_of_nonneg_left hlog hK0)
    rw [norm_mul, norm_neg, norm_div ((x : ℂ) ^ s)]
    have hrk : 0 ≤ r ^ k := pow_nonneg hr0 k
    calc _ ≤ K * (4 * k + L) * (r ^ k / 1) :=
          mul_le_mul hLd (div_le_div₀ hrk hxs one_pos h1s) (by positivity) (by positivity)
      _ = K * ((4 * k + L) * r ^ k) := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [show |R - -R| = 2 * R by rw [abs_of_nonneg (by linarith)]; ring] at this
  simpa [hB] using this

private lemma final_bound (x R Cg K K₂ : ℝ) (hx0 : 0 < x) (hR0 : 0 < R)
    (hlR : 1 ≤ Real.log R) (hlx : 0 < Real.log x) (h1L : 1 / Real.log x ≤ 3) (hK0 : 0 ≤ K)
    (hK₂0 : 0 ≤ K₂) :
    Real.exp 1 * x * ((|Cg| * Real.log R ^ 2 + K₂ + K * Real.log (2 * R) + 8 * K) /
        Real.log x + 2 * K / Real.log x ^ 2) / R / Real.pi ≤
      (|Cg| + K₂ + 16 * K) * (x * Real.log R ^ 2 / (R * Real.log x)) := by
  set a : ℝ := |Cg| * Real.log R ^ 2 + K₂ + K * Real.log (2 * R) + 8 * K with ha
  set D : ℝ := |Cg| + K₂ + 16 * K with hD
  have hD0 : 0 ≤ D := by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hl2 : Real.log (2 * R) ≤ 2 * Real.log R ^ 2 := by
    rw [Real.log_mul (by norm_num) hR0.ne']
    have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    nlinarith
  have hsq : 1 ≤ Real.log R ^ 2 := by nlinarith
  have hA6 : a + 6 * K ≤ D * Real.log R ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hl2 hK0
    have h2 := mul_le_mul_of_nonneg_left hsq hK0
    have h3 := mul_le_mul_of_nonneg_left hsq hK₂0
    simp only [ha, hD]
    linarith
  have hfrac : a / Real.log x + 2 * K / Real.log x ^ 2 ≤ D * Real.log R ^ 2 / Real.log x := by
    have e1 : 2 * K / Real.log x ^ 2 = (2 * K / Real.log x) * (1 / Real.log x) := by
      field_simp
    have e2 : 2 * K / Real.log x * (1 / Real.log x) ≤ 2 * K / Real.log x * 3 :=
      mul_le_mul_of_nonneg_left h1L (by positivity)
    have e3 : a / Real.log x + 2 * K / Real.log x * 3 = (a + 6 * K) / Real.log x := by
      field_simp; ring
    rw [e1]
    calc _ ≤ a / Real.log x + 2 * K / Real.log x * 3 := by linarith
      _ = (a + 6 * K) / Real.log x := e3
      _ ≤ _ := div_le_div_of_nonneg_right hA6 hlx.le
  set Q : ℝ := x * (D * Real.log R ^ 2 / Real.log x) / R with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hHbQ : Real.exp 1 * x * (a / Real.log x + 2 * K / Real.log x ^ 2) / R ≤
      Real.exp 1 * Q := by
    calc Real.exp 1 * x * (a / Real.log x + 2 * K / Real.log x ^ 2) / R
        ≤ Real.exp 1 * x * (D * Real.log R ^ 2 / Real.log x) / R := by gcongr
      _ = Real.exp 1 * Q := by simp only [hQ]; ring
  have hepi : Real.exp 1 ≤ Real.pi := by linarith [Real.exp_one_lt_d9, Real.pi_gt_three]
  calc _ ≤ Real.exp 1 * Q / Real.pi := div_le_div_of_nonneg_right hHbQ hpi.le
    _ ≤ Real.pi * Q / Real.pi := by gcongr
    _ = Q := by field_simp
    _ = D * (x * Real.log R ^ 2 / (R * Real.log x)) := by simp only [hQ]; field_simp

private lemma combine_bound (N E Hp C₁ D X Y : ℝ) (hmain : N ≤ E + Hp) (hE : E ≤ C₁ * X)
    (hH : Hp ≤ D * Y) (hD0 : 0 ≤ D) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    N ≤ (max C₁ 0 + D) * (X + Y) := by
  have hm : 0 ≤ max C₁ 0 := le_max_right _ _
  have hC1 : C₁ * X ≤ max C₁ 0 * X := mul_le_mul_of_nonneg_right (le_max_left _ _) hX
  nlinarith [mul_nonneg hm hY, mul_nonneg hD0 hX]

end Truncated

/-- **The truncated explicit formula for `ψ(x)`.** There are constants `C` and `T₀` such that
every `T ≥ T₀` can be moved by at most `1` to a height `R` for which, for every `x` half more
than a positive integer,
`|ψ(x) - x + ∑_{|γ| < R} x^ρ/ρ + ζ'(0)/ζ(0) + ½ log (1 - x⁻²)|
  ≤ C (x log² x / R + x log² R / (R log x))`,
the sum over the nontrivial zeros `ρ = β + iγ` counted with multiplicity (any family `z` listing
the zeros of `ξ` with multiplicity). The height `R` depends only on `T`. -/
theorem exists_truncated_explicit_formula_chebyshevPsi :
    ∃ C T₀ : ℝ, ∀ T ≥ T₀, ∃ R : ℝ, |R - T| ≤ 1 ∧
      ∀ {ι : Type u} (z : ι → ℂ),
        (∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) →
        ∀ x : ℝ, (∃ n : ℕ, 0 < n ∧ x = n + 1 / 2) →
          ‖(Chebyshev.psi x : ℂ) - x +
              ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0) +
              deriv riemannZeta 0 / riemannZeta 0 +
              (1 / 2 : ℂ) * (Real.log (1 - x ^ (-2 : ℤ)) : ℂ)‖
            ≤ C * (x * Real.log x ^ 2 / R + x * Real.log R ^ 2 / (R * Real.log x)) := by
  obtain ⟨Cg, Tg, hgood⟩ := exists_good_height_norm_logDeriv_riemannZeta_le
  obtain ⟨C₁, hC₁⟩ := exists_norm_chebyshevPsi_sub_truncated_integral_le_log_sq
  obtain ⟨K₀, hK₀⟩ := exists_norm_logDeriv_riemannZeta_le_log_of_re_le_neg_one one_pos
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_norm_logDeriv_riemannZeta_le (δ := 1) one_pos
  set K : ℝ := max K₀ 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  have hKb : ∀ s : ℂ, s.re ≤ -1 → (∀ m : ℕ, 0 < m → 1 ≤ ‖s + 2 * (m : ℂ)‖) →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ K * Real.log (2 * ‖s‖) := by
    intro s h2 h3
    have hs1 : 1 ≤ ‖s‖ :=
      le_trans (by rw [abs_of_nonpos (by linarith)]; linarith) (Complex.abs_re_le_norm s)
    have hlog : 0 ≤ Real.log (2 * ‖s‖) := Real.log_nonneg (by linarith)
    exact (hK₀ s h2 h3).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)
  set D : ℝ := |Cg| + K₂ + 16 * K with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨max C₁ 0 + D, max Tg 4, fun T hT => ?_⟩
  obtain ⟨R, hRT, hRz, hRM⟩ := hgood T (le_trans (le_max_left _ _) hT)
  refine ⟨R, hRT, ?_⟩
  intro ι z hz x hxn
  have hT4 : 4 ≤ T := le_trans (le_max_right _ _) hT
  have hR3 : 3 ≤ R := by rw [abs_le] at hRT; linarith
  have hR0 : 0 < R := by linarith
  have hlR : 1 ≤ Real.log R := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  obtain ⟨n0, hn0, hxn0⟩ := hxn
  have hx32 : 3 / 2 ≤ x := by
    have : (1 : ℝ) ≤ n0 := by exact_mod_cast hn0
    rw [hxn0]; linarith
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hL3 : 1 / 3 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have h3 : Real.exp (1 / 3) ^ 3 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have he : Real.exp 1 < 3.375 := by linarith [Real.exp_one_lt_d9]
    have h32 : Real.exp (1 / 3) ≤ 3 / 2 :=
      le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by norm_num)
        (by rw [h3]; norm_num; linarith)
    linarith
  have hlx : 0 < Real.log x := by linarith
  set c : ℝ := 1 + 1 / Real.log x with hc
  have hc1 : 1 < c := by have := one_div_pos.mpr hlx; linarith
  have h1L : 1 / Real.log x ≤ 3 := by rw [div_le_iff₀ hlx]; linarith
  have hc4 : c ≤ 4 := by linarith
  have hxc : x ^ c = Real.exp 1 * x := by
    rw [hc, Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0,
      mul_one_div_cancel hlx.ne']
    ring
  have hRz' : ∀ ρ ∈ riemannZetaNontrivialZeros, |ρ.im| ≠ R := by
    intro ρ hρ heq
    rcases (abs_eq hR0.le).mp heq with h | h
    · exact hRz ρ hρ h
    · exact hRz _ (conj_mem_riemannZetaNontrivialZeros hρ) (by rw [Complex.conj_im, h, neg_neg])
  have hl2R : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  set a : ℝ := |Cg| * Real.log R ^ 2 + K₂ + K * Real.log (2 * R) + 8 * K with ha
  have ha0 : 0 ≤ a := by positivity
  have hline : ∀ τ : ℝ, |τ| = R →
      (∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
        ‖deriv riemannZeta (σ + τ * I) / riemannZeta (σ + τ * I)‖ ≤ Cg * Real.log R ^ 2) →
      ∀ U : ℝ, ∀ σ : ℝ, -U ≤ σ → σ ≤ c →
        ‖deriv riemannZeta (σ + τ * I) / riemannZeta (σ + τ * I)‖ ≤ a - 2 * K * σ := by
    intro τ hτ hmid U σ _ hσ2
    have hCg : Cg * Real.log R ^ 2 ≤ |Cg| * Real.log R ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have hKσ : 0 ≤ K * Real.log (2 * R) := mul_nonneg hK0 hl2R
    have hCg0 : 0 ≤ |Cg| * Real.log R ^ 2 := by positivity
    by_cases h1 : σ ≤ -1
    · set s : ℂ := (σ : ℂ) + τ * I with hs
      have hsre : s.re = σ := by simp [hs]
      have hsim : s.im = τ := by simp [hs]
      have hsle : ‖s‖ ≤ R + -σ := by
        calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
          _ = R + -σ := by rw [hsre, hsim, hτ, abs_of_nonpos (by linarith)]; ring
      have hRs : R ≤ ‖s‖ := by rw [← hτ, ← hsim]; exact Complex.abs_im_le_norm s
      have hdist : ∀ m : ℕ, 0 < m → 1 ≤ ‖s + 2 * (m : ℂ)‖ := by
        intro m _
        calc (1 : ℝ) ≤ R := by linarith
          _ = |(s + 2 * (m : ℂ)).im| := by simp [hsim, hτ]
          _ ≤ _ := Complex.abs_im_le_norm _
      have h := hKb s (by rw [hsre]; exact h1) hdist
      have hlog : Real.log (2 * ‖s‖) ≤ Real.log (2 * R) + 2 * -σ := by
        calc Real.log (2 * ‖s‖) ≤ Real.log (2 * R + 2 * -σ) :=
              Real.log_le_log (by linarith) (by linarith)
          _ ≤ _ := log_add_le (by linarith) (by linarith)
      have := mul_le_mul_of_nonneg_left hlog hK0
      linarith
    · push Not at h1
      by_cases h2 : σ ≤ 2
      · have := hmid σ h1.le h2
        nlinarith [mul_nonneg hK0 (show 0 ≤ 2 - σ by linarith)]
      · push Not at h2
        have := hK₂ (σ + τ * I) (by simp; linarith)
        nlinarith [mul_nonneg hK0 (show 0 ≤ 4 - σ by linarith)]
  have hlineT := hline R (abs_of_pos hR0) (fun σ h1 h2 => hRM σ h1 h2)
  have hlineB := hline (-R) (by rw [abs_neg, abs_of_pos hR0]) (fun σ h1 h2 => by
    have e : (σ : ℂ) + ((-R : ℝ) : ℂ) * I = conj ((σ : ℂ) + (R : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [e, norm_logDeriv_riemannZeta_conj]; exact hRM σ h1 h2)
  set F : ℂ → ℂ := fun s => -(deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s) with hF
  set S := ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0) with hS
  set A := deriv riemannZeta 0 / riemannZeta 0 with hA
  set Lg : ℂ := (1 / 2 : ℂ) * (Real.log (1 - x ^ (-2 : ℤ)) : ℂ) with hLg
  set P : ℂ := (1 / (2 * Real.pi)) * ∫ t in (-R)..R, F (c + t * I) with hP
  have hPer : ‖(Chebyshev.psi x : ℂ) - P‖ ≤ C₁ * (x * Real.log x ^ 2 / R) :=
    hC₁ x R ⟨n0, hn0, hxn0⟩ hR0
  set Hb : ℝ := x ^ c * (a / Real.log x + 2 * K / Real.log x ^ 2) / R with hHb
  set Sk : ℕ → ℂ := fun k => ∑ m ∈ Finset.Icc 1 ((2 * k + 1) / 2),
    (x : ℂ) ^ (-(2 * (m : ℂ))) / (2 * (m : ℂ)) with hSk
  set Lk : ℕ → ℂ := fun k =>
    ∫ t in (-R)..R, F (((-((2 * k + 1 : ℕ) : ℝ) : ℝ) : ℂ) + t * I) with hLk
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi0 : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hnorm2pi : ‖(1 / (2 * Real.pi * I) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg hpi.le]
  have hk : ∀ k : ℕ, ‖(Chebyshev.psi x : ℂ) - x + S + A + Lg‖ ≤
      ‖(Chebyshev.psi x : ℂ) - P‖ + ‖Sk k + Lg‖ + Hb / Real.pi +
        ‖(1 / (2 * Real.pi * I)) * (I * Lk k)‖ := by
    intro k
    set U : ℕ := 2 * k + 1 with hU
    have hUodd : Odd U := ⟨k, rfl⟩
    have hU0 : (0 : ℝ) ≤ U := Nat.cast_nonneg _
    have hrect := boundaryIntegral_neg_logDeriv_riemannZeta_mul_cpow_div z hz hx0 hc1 hUodd hR0
      hRz'
    simp only [RectilinearRectangle.boundaryIntegral, RectilinearRectangle.ofBounds_first_re,
      RectilinearRectangle.ofBounds_second_re, RectilinearRectangle.ofBounds_first_im,
      RectilinearRectangle.ofBounds_second_im, smul_eq_mul] at hrect
    set Hbot := ∫ σ in (-(U : ℝ))..c, F (σ + ((-R : ℝ) : ℂ) * I) with hHbot
    set Htop := ∫ σ in (-(U : ℝ))..c, F (σ + (R : ℂ) * I) with hHtop
    set Rt := ∫ t in (-R)..R, F (c + t * I) with hRt
    have hrect' : (x : ℂ) - S - A + Sk k =
        (1 / (2 * Real.pi * I)) * (Hbot - Htop + I * Rt - I * Lk k) := by
      rw [hrect, ← mul_assoc, one_div_mul_cancel hpi0, one_mul]
    have hPR : (1 / (2 * Real.pi * I)) * (I * Rt) = P := by
      rw [hP]; field_simp
    have htop : ‖Htop‖ ≤ Hb :=
      norm_integral_horizontal_le hx1 hR0 (abs_of_pos hR0) (by positivity) (by linarith) hU0
        (by positivity) (hlineT U)
    have hbot : ‖Hbot‖ ≤ Hb :=
      norm_integral_horizontal_le hx1 hR0 (by rw [abs_neg, abs_of_pos hR0]) (by positivity)
        (by linarith) hU0 (by positivity) (hlineB U)
    have hid : (Chebyshev.psi x : ℂ) - x + S + A + Lg = ((Chebyshev.psi x : ℂ) - P) +
        (Sk k + Lg) - (1 / (2 * Real.pi * I)) * (Hbot - Htop) +
        (1 / (2 * Real.pi * I)) * (I * Lk k) := by
      linear_combination -hrect' - hPR
    rw [hid]
    have hE : ‖(1 / (2 * Real.pi * I)) * (Hbot - Htop)‖ ≤ Hb / Real.pi := by
      rw [norm_mul, hnorm2pi]
      calc 1 / (2 * Real.pi) * ‖Hbot - Htop‖ ≤ 1 / (2 * Real.pi) * (Hb + Hb) :=
            mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hbot htop))
              (by positivity)
        _ = Hb / Real.pi := by field_simp; ring
    have t1 := norm_add_le (((Chebyshev.psi x : ℂ) - P) + (Sk k + Lg) -
      (1 / (2 * Real.pi * I)) * (Hbot - Htop)) ((1 / (2 * Real.pi * I)) * (I * Lk k))
    have t2 := norm_sub_le (((Chebyshev.psi x : ℂ) - P) + (Sk k + Lg))
      ((1 / (2 * Real.pi * I)) * (Hbot - Htop))
    have t3 := norm_add_le ((Chebyshev.psi x : ℂ) - P) (Sk k + Lg)
    linarith
  have hlim1 : Tendsto (fun k => ‖Sk k + Lg‖) atTop (𝓝 0) := by
    have h := ((tendsto_sum_cpow_neg_two_mul_div_two_mul hx1).add_const Lg).norm
    rw [neg_add_cancel, norm_zero] at h
    refine h.congr fun k => ?_
    simp only [hSk, show (2 * k + 1) / 2 = k by omega]
  have hlim2 : Tendsto (fun k => ‖(1 / (2 * Real.pi * I)) * (I * Lk k)‖) atTop (𝓝 0) := by
    have h := (((tendsto_integral_left_side K hK0 hKb hx1 (by linarith : (1 : ℝ) ≤ R)).const_mul
      I).const_mul (1 / (2 * Real.pi * I))).norm
    rw [mul_zero, mul_zero, norm_zero] at h
    exact h
  have hlim := ((hlim1.const_add (‖(Chebyshev.psi x : ℂ) - P‖)).add_const
    (Hb / Real.pi)).add hlim2
  simp only [add_zero] at hlim
  have hmain : ‖(Chebyshev.psi x : ℂ) - x + S + A + Lg‖ ≤
      ‖(Chebyshev.psi x : ℂ) - P‖ + Hb / Real.pi :=
    ge_of_tendsto hlim (Eventually.of_forall hk)
  have hfinal : Hb / Real.pi ≤ D * (x * Real.log R ^ 2 / (R * Real.log x)) := by
    have h := final_bound x R Cg K K₂ hx0 hR0 hlR hlx h1L hK0 hK₂0
    rw [← hxc] at h
    exact h
  exact combine_bound _ _ _ _ _ _ _ hmain hPer hfinal hD0 (by positivity) (by positivity)

/-! ### The explicit formula -/

/-- Moving the truncation height by at most `1` changes the zero sum by `O(x log R / R)`. -/
private lemma norm_sum_zeros_sub_sum_zeros_le {ι : Type u} (z : ι → ℂ)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) (Cc : ℝ) (hCc0 : 0 ≤ Cc)
    (hcnt : ∀ T D : ℝ, 2 ≤ T → 0 ≤ D → ∀ F : Finset ι, (∀ n ∈ F, |(|(z n).im| - T)| ≤ D) →
      (F.card : ℝ) ≤ (1 + D ^ 2) * Cc * Real.log T)
    {x : ℝ} (hx : 1 < x) {R T : ℝ} (hR : 3 ≤ R) (hTR : |T - R| ≤ 1) :
    ‖(∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0)) -
        ∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0)‖ ≤
      2 * Cc * Real.log (R + 1) * (x / (R - 1)) := by
  classical
  have hx0 : 0 < x := by linarith
  have hTR' := abs_le.mp hTR
  set U := max R T with hU
  set NF := (finite_setOf_abs_im_lt_of_card_eq_analyticOrderAt hz U).toFinset with hNF
  have hsupp : ∀ V : ℝ, V ≤ U → ∑' n, (if |(z n).im| < V then (x : ℂ) ^ z n / z n else 0) =
      ∑ n ∈ NF, (if |(z n).im| < V then (x : ℂ) ^ z n / z n else 0) := by
    intro V hV
    refine tsum_eq_sum fun n hn => ite_eq_right ?_
    intro h
    apply hn
    simp only [hNF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    linarith
  rw [hsupp R (le_max_left _ _), hsupp T (le_max_right _ _), ← Finset.sum_sub_distrib]
  set d : ι → ℂ := fun n => (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0) -
    (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0) with hd
  set c0 : ℝ := (R + T) / 2 with hc0
  have hdz : ∀ n, d n ≠ 0 → min R T ≤ |(z n).im| ∧ |(z n).im| < max R T := by
    intro n hn
    by_contra hc
    apply hn
    simp only [hd]
    rcases not_and_or.mp hc with h | h
    · push Not at h
      rw [ite_eq_left (lt_of_lt_of_le h (min_le_left _ _)),
        ite_eq_left (lt_of_lt_of_le h (min_le_right _ _)), sub_self]
    · push Not at h
      rw [ite_eq_right (not_lt.mpr ((le_max_left _ _).trans h)),
        ite_eq_right (not_lt.mpr ((le_max_right _ _).trans h)), sub_self]
  have hdnorm : ∀ n, ‖d n‖ ≤ x / (R - 1) := by
    intro n
    by_cases hn : d n = 0
    · rw [hn, norm_zero]; exact div_nonneg hx0.le (by linarith)
    obtain ⟨h1, h2⟩ := hdz n hn
    have hmin : R - 1 ≤ min R T := le_min (by linarith) (by linarith)
    have hzn : R - 1 ≤ ‖z n‖ := (hmin.trans h1).trans (Complex.abs_im_le_norm _)
    have hmem := mem_riemannZetaNontrivialZeros_of_card_eq_analyticOrderAt hz n
    have hpow : ‖(x : ℂ) ^ z n‖ ≤ x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      calc x ^ (z n).re ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le hmem.2.2
        _ = x := Real.rpow_one x
    have hval : ‖(x : ℂ) ^ z n / z n‖ ≤ x / (R - 1) := by
      rw [norm_div]
      exact div_le_div₀ hx0.le hpow (by linarith) hzn
    simp only [hd] at hn ⊢
    split_ifs at hn ⊢ with ha hb hb
    · simp at hn
    · rwa [sub_zero]
    · rwa [zero_sub, norm_neg]
    · simp at hn
  set W : Finset ι := NF.filter (fun n => d n ≠ 0) with hW
  have hsum_eq : ∑ n ∈ NF, d n = ∑ n ∈ W, d n := by
    rw [hW, Finset.sum_filter_ne_zero]
  have hWcard : (W.card : ℝ) ≤ 2 * Cc * Real.log (R + 1) := by
    have hnear : ∀ n ∈ W, |(|(z n).im| - c0)| ≤ 1 := by
      intro n hn
      obtain ⟨h1, h2⟩ := hdz n (Finset.mem_filter.mp hn).2
      rw [abs_le]
      constructor
      · have : min R T ≥ c0 - 1 / 2 := by
          rcases le_total R T with h | h
          · rw [min_eq_left h, hc0]; linarith
          · rw [min_eq_right h, hc0]; linarith
        linarith
      · have : max R T ≤ c0 + 1 / 2 := by
          rcases le_total R T with h | h
          · rw [max_eq_right h, hc0]; linarith
          · rw [max_eq_left h, hc0]; linarith
        linarith
    have h := hcnt c0 1 (by rw [hc0]; linarith) zero_le_one W hnear
    have hlog : Real.log c0 ≤ Real.log (R + 1) :=
      Real.log_le_log (by rw [hc0]; linarith) (by rw [hc0]; linarith)
    have := mul_le_mul_of_nonneg_left hlog hCc0
    nlinarith
  rw [hsum_eq]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ => hdnorm n).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hWcard (div_nonneg hx0.le (by linarith))

/-- **The explicit formula for `ψ(x)`.** For `x` half more than a positive integer,
`ψ(x) = x - ∑_ρ x^ρ/ρ - ζ'(0)/ζ(0) - ½ log (1 - x⁻²)`. The sum over the nontrivial zeros
`ρ = β + iγ` of `ζ`, counted with multiplicity (any family `z` listing the zeros of `ξ` with
multiplicity), converges conditionally: it is the limit as `R → ∞` of the sums over `|γ| < R`,
each of which has finite support. -/
theorem tendsto_sum_cpow_div_zeros_explicit_formula {ι : Type u} (z : ι → ℂ)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w)
    {x : ℝ} (hx : ∃ n : ℕ, 0 < n ∧ x = n + 1 / 2) :
    Tendsto (fun R : ℝ => ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0)) atTop
      (𝓝 ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 -
        (1 / 2 : ℂ) * (Real.log (1 - x ^ (-2 : ℤ)) : ℂ) - (Chebyshev.psi x : ℂ))) := by
  obtain ⟨C₀, T₀, hTEF⟩ := exists_truncated_explicit_formula_chebyshevPsi.{u}
  obtain ⟨Cc, hCc0, hcount⟩ := exists_card_le_log_of_abs_abs_im_sub_le.{u}
  have hcnt := hcount z hz
  obtain ⟨n0, hn0, hxn0⟩ := hx
  have hx32 : 3 / 2 ≤ x := by
    have : (1 : ℝ) ≤ n0 := by exact_mod_cast hn0
    rw [hxn0]; linarith
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  set S : ℝ → ℂ := fun R => ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0) with hS
  set V : ℂ := (x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 -
    (1 / 2 : ℂ) * (Real.log (1 - x ^ (-2 : ℤ)) : ℂ) - (Chebyshev.psi x : ℂ) with hV
  set g : ℕ → ℝ → ℝ := fun k R => Real.log (R + 1) ^ k / (R - 1) with hg
  have hgt : ∀ k, Tendsto (g k) atTop (𝓝 0) := by
    intro k
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) k one_ne_zero
    have hc : Tendsto (fun R : ℝ => R + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_id
    refine (h.comp hc).congr fun R => ?_
    simp only [Function.comp_apply, hg]
    congr 1
    ring
  set f : ℝ → ℝ := fun R => |C₀| * (x * Real.log x ^ 2 * g 0 R + x / Real.log x * g 2 R) +
    2 * Cc * x * g 1 R with hf
  have hft : Tendsto f atTop (𝓝 0) := by
    have := (((hgt 0).const_mul (x * Real.log x ^ 2)).add ((hgt 2).const_mul
      (x / Real.log x))).const_mul |C₀| |>.add ((hgt 1).const_mul (2 * Cc * x))
    simpa [hf] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hft
  filter_upwards [eventually_ge_atTop (max T₀ 4)] with R hR
  have hR4 : 4 ≤ R := le_trans (le_max_right _ _) hR
  obtain ⟨R', hR'R, hR'⟩ := hTEF R (le_trans (le_max_left _ _) hR)
  have hR'R2 := abs_le.mp hR'R
  have hR'3 : 3 ≤ R' := by linarith
  have hE := hR' z hz x ⟨n0, hn0, hxn0⟩
  have hw := norm_sum_zeros_sub_sum_zeros_le z hz Cc hCc0 hcnt hx1 (by linarith : 3 ≤ R) hR'R
  have hid : S R' - V = (Chebyshev.psi x : ℂ) - x +
      ∑' n, (if |(z n).im| < R' then (x : ℂ) ^ z n / z n else 0) +
      deriv riemannZeta 0 / riemannZeta 0 +
      (1 / 2 : ℂ) * (Real.log (1 - x ^ (-2 : ℤ)) : ℂ) := by
    simp only [hS, hV]; ring
  have htri := norm_sub_le_norm_sub_add_norm_sub (S R) (S R') V
  rw [hid] at htri
  set X : ℝ := x * Real.log x ^ 2 / R' + x * Real.log R' ^ 2 / (R' * Real.log x) with hX
  have hlR' : 0 ≤ Real.log R' := Real.log_nonneg (by linarith)
  have hX0 : 0 ≤ X := by positivity
  have hEX : C₀ * X ≤ |C₀| * X := mul_le_mul_of_nonneg_right (le_abs_self _) hX0
  have hR1 : 0 < R - 1 := by linarith
  have hp1 : x * Real.log x ^ 2 / R' ≤ x * Real.log x ^ 2 * g 0 R := by
    have : x * Real.log x ^ 2 * g 0 R = x * Real.log x ^ 2 / (R - 1) := by
      simp only [hg, pow_zero]; ring
    rw [this]
    exact div_le_div_of_nonneg_left (by positivity) hR1 (by linarith)
  have hp2 : x * Real.log R' ^ 2 / (R' * Real.log x) ≤ x / Real.log x * g 2 R := by
    have : x / Real.log x * g 2 R = x * Real.log (R + 1) ^ 2 / ((R - 1) * Real.log x) := by
      simp only [hg]; field_simp
    rw [this]
    have hl : Real.log R' ≤ Real.log (R + 1) := Real.log_le_log (by linarith) (by linarith)
    apply div_le_div₀ (by positivity) _ (by positivity)
    · exact mul_le_mul_of_nonneg_right (by linarith) hlx.le
    · gcongr
  have hXb : |C₀| * X ≤ |C₀| * (x * Real.log x ^ 2 * g 0 R + x / Real.log x * g 2 R) :=
    mul_le_mul_of_nonneg_left (by rw [hX]; linarith) (abs_nonneg _)
  have hwg : 2 * Cc * Real.log (R + 1) * (x / (R - 1)) = 2 * Cc * x * g 1 R := by
    simp only [hg, pow_one]; ring
  have hfR : f R = |C₀| * (x * Real.log x ^ 2 * g 0 R + x / Real.log x * g 2 R) +
      2 * Cc * x * g 1 R := rfl
  rw [hfR]
  simp only [hS] at htri hw
  linarith

/-! ### The Riemann hypothesis and the error term in the prime number theorem -/

private lemma abs_sub_le_of_abs_sub_le_half {p x y M K0 : ℝ} (hx10 : 10 ≤ x)
    (hyx1 : x - 1 / 2 ≤ y) (hyx2 : y ≤ x + 1 / 2) (hM0 : 0 ≤ M) (hK00 : 0 ≤ K0)
    (hψy : |p - y| ≤ M * (Real.sqrt y * Real.log y ^ 2) + K0 + 1 / 2) :
    |p - x| ≤ (8 * M + K0 + 2) * |Real.sqrt x * Real.log x ^ 2| := by
  have hy0 : 0 < y := by linarith
  have hx0 : 0 < x := by linarith
  have hsqy : Real.sqrt y ≤ 2 * Real.sqrt x := by
    calc Real.sqrt y ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt (by linarith)
      _ = 2 * Real.sqrt x := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
  have hlogx1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  have hlogy1 : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hy0]
    linarith [Real.exp_one_lt_d9]
  have hlogyx : Real.log y ≤ 2 * Real.log x := by
    rw [← Real.log_rpow hx0]
    apply Real.log_le_log hy0
    rw [Real.rpow_two, sq]; nlinarith
  have hsqx1 : 1 ≤ Real.sqrt x := by rw [Real.one_le_sqrt]; linarith
  have h1 : Real.log y ^ 2 ≤ 4 * Real.log x ^ 2 := by nlinarith
  have hprod : Real.sqrt y * Real.log y ^ 2 ≤ 8 * (Real.sqrt x * Real.log x ^ 2) := by
    have := mul_le_mul hsqy h1 (sq_nonneg _) (by positivity)
    linarith
  have hone : 1 ≤ Real.sqrt x * Real.log x ^ 2 := by
    have : 1 ≤ Real.log x ^ 2 := by nlinarith
    nlinarith
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt x * Real.log x ^ 2)]
  have hxy : |p - x| ≤ |p - y| + 1 / 2 := by
    have : |y - x| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    calc |p - x| = |(p - y) + (y - x)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by linarith)
  have := mul_le_mul_of_nonneg_left hprod hM0
  have hK := le_mul_of_one_le_right hK00 hone
  linarith

/-- **The Riemann hypothesis gives the error term in the prime number theorem**:
under RH, `ψ(x) = x + O(√x log² x)` as `x → ∞`. -/
theorem chebyshevPsi_sub_self_isBigO_of_riemannHypothesis (hRH : RiemannHypothesis) :
    (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
      (fun x : ℝ => Real.sqrt x * Real.log x ^ 2) := by
  obtain ⟨C, T₀, hTEF⟩ := exists_truncated_explicit_formula_chebyshevPsi.{0}
  obtain ⟨Cz, hCz⟩ := exists_tsum_one_div_norm_le_log_sq.{0}
  obtain ⟨ι, z, hz⟩ := exists_card_eq_analyticOrderAt
  have hzre : ∀ n, (z n).re = 1 / 2 := by
    intro n
    have hmem := mem_riemannZetaNontrivialZeros_of_card_eq_analyticOrderAt hz n
    refine hRH (z n) hmem.1 ?_ (ne_one_of_mem_riemannZetaNontrivialZeros hmem)
    rintro ⟨m, hm⟩
    have h1 := hmem.2.1
    rw [hm] at h1
    simp at h1
    linarith
  set K0 : ℝ := ‖deriv riemannZeta 0 / riemannZeta 0‖ with hK0
  set M : ℝ := 4 * |Cz| + 10 * |C| with hM
  have hM0 : 0 ≤ M := by positivity
  refine IsBigO.of_bound (8 * M + K0 + 2) ?_
  filter_upwards [eventually_ge_atTop (max T₀ 0 + 10)] with x hx
  have hx10 : 10 ≤ x := le_trans (by linarith [le_max_right T₀ 0]) hx
  set n : ℕ := ⌊x⌋₊ with hn
  have hn1 : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hn2 : x < n + 1 := Nat.lt_floor_add_one x
  set y : ℝ := n + 1 / 2 with hy
  have hy9 : 9 ≤ y := by linarith
  have hyT : T₀ ≤ y := by linarith [le_max_left T₀ 0]
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  obtain ⟨R, hRT, hR⟩ := hTEF y hyT
  have hRb := abs_le.mp hRT
  have key := hR z hz y ⟨n, hnpos, rfl⟩
  -- `ψ x = ψ y`
  have hψ : Chebyshev.psi x = Chebyshev.psi y := by
    have : ⌊y⌋₊ = n := by
      rw [Nat.floor_eq_iff (by linarith)]
      constructor <;> linarith
    unfold Chebyshev.psi
    rw [this]
  have hy0 : 0 < y := by linarith
  have hR2 : 2 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hlogy1 : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hy0]
    linarith [Real.exp_one_lt_d9]
  have hlogR : Real.log R ≤ 2 * Real.log y := by
    rw [← Real.log_rpow hy0]
    apply Real.log_le_log hR0
    rw [Real.rpow_two, sq]; nlinarith
  have hlogR0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hlogRsq : Real.log R ^ 2 ≤ 4 * Real.log y ^ 2 := by nlinarith
  -- the zero sum
  have hsum : ‖∑' k, (if |(z k).im| < R then (y : ℂ) ^ z k / z k else 0)‖ ≤
      Real.sqrt y * (Cz * Real.log R ^ 2) := by
    have hnorm : ∀ k, ‖(if |(z k).im| < R then (y : ℂ) ^ z k / z k else 0)‖ =
        Real.sqrt y * (if |(z k).im| < R then 1 / ‖z k‖ else 0) := by
      intro k
      split_ifs
      · rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, hzre, Real.sqrt_eq_rpow]
        ring
      · simp
    have hle := hCz z hz R hR2
    by_cases hs : Summable fun k => ‖(if |(z k).im| < R then (y : ℂ) ^ z k / z k else 0)‖
    · refine (norm_tsum_le_tsum_norm hs).trans ?_
      simp_rw [hnorm]
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
    · have hs' : ¬ Summable fun k => (if |(z k).im| < R then (y : ℂ) ^ z k / z k else 0) :=
        fun h => hs h.norm
      rw [tsum_eq_zero_of_not_summable hs', norm_zero]
      have : 0 ≤ Cz * Real.log R ^ 2 :=
        le_trans (tsum_nonneg fun k => by split_ifs <;> positivity) hle
      positivity
  -- the error term
  have hyR : y ≤ 2 * R := by linarith
  have hlogy0 : 0 < Real.log y := by linarith
  have herr : C * (y * Real.log y ^ 2 / R + y * Real.log R ^ 2 / (R * Real.log y)) ≤
      10 * |C| * Real.log y ^ 2 := by
    have h1 : y * Real.log y ^ 2 / R ≤ 2 * Real.log y ^ 2 := by
      rw [div_le_iff₀ hR0]; nlinarith [sq_nonneg (Real.log y)]
    have h2 : y * Real.log R ^ 2 / (R * Real.log y) ≤ 8 * Real.log y ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : y * Real.log R ^ 2 ≤ 2 * R * (4 * Real.log y ^ 2) := by
        have := mul_le_mul hyR hlogRsq (sq_nonneg _) (by linarith)
        linarith
      have h3 : 2 * R * (4 * Real.log y ^ 2) ≤ 8 * Real.log y ^ 2 * (R * Real.log y) := by
        have : 0 ≤ R * Real.log y ^ 2 := by positivity
        nlinarith
      linarith
    have h0 : 0 ≤ y * Real.log y ^ 2 / R + y * Real.log R ^ 2 / (R * Real.log y) := by
      positivity
    calc _ ≤ |C| * (y * Real.log y ^ 2 / R + y * Real.log R ^ 2 / (R * Real.log y)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |C| * (10 * Real.log y ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); linarith
      _ = _ := by ring
  have hL := norm_half_log_one_sub_zpow_neg_two_le (y := y) (by linarith)
  -- combine at `y`
  have hψy : |Chebyshev.psi y - y| ≤ M * (Real.sqrt y * Real.log y ^ 2) + K0 + 1 / 2 := by
    set S := ∑' k, (if |(z k).im| < R then (y : ℂ) ^ z k / z k else 0)
    set Lt := (1 / 2 : ℂ) * (Real.log (1 - y ^ (-2 : ℤ)) : ℂ)
    set A := (Chebyshev.psi y : ℂ) - y + S + deriv riemannZeta 0 / riemannZeta 0 + Lt
    have hrw : ((Chebyshev.psi y - y : ℝ) : ℂ) =
        A - S - deriv riemannZeta 0 / riemannZeta 0 - Lt := by
      simp only [A]; push_cast; ring
    have hn : |Chebyshev.psi y - y| ≤ ‖A‖ + ‖S‖ + K0 + ‖Lt‖ := by
      have he : |Chebyshev.psi y - y| = ‖((Chebyshev.psi y - y : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      rw [he, hrw]
      have := norm_sub_le (A - S - deriv riemannZeta 0 / riemannZeta 0) Lt
      have := norm_sub_le (A - S) (deriv riemannZeta 0 / riemannZeta 0)
      have := norm_sub_le A S
      linarith
    have hsq1 : 1 ≤ Real.sqrt y := by rw [Real.one_le_sqrt]; linarith
    have hS : ‖S‖ ≤ 4 * |Cz| * (Real.sqrt y * Real.log y ^ 2) := by
      refine hsum.trans ?_
      have : Cz * Real.log R ^ 2 ≤ |Cz| * (4 * Real.log y ^ 2) :=
        (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hlogRsq (abs_nonneg _))
      have := mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg y)
      linarith
    have hC : 10 * |C| * Real.log y ^ 2 ≤ 10 * |C| * (Real.sqrt y * Real.log y ^ 2) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (sq_nonneg _) hsq1) (by positivity)
    have hk : ‖A‖ ≤ 10 * |C| * Real.log y ^ 2 := key.trans herr
    clear_value A S Lt
    rw [hM, add_mul]
    linarith
  -- transfer to `x`
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hψ]
  clear_value y n
  exact abs_sub_le_of_abs_sub_le_half (by linarith) (by linarith) (by linarith) hM0
    (norm_nonneg _) hψy

/-- **Von Koch's criterion.** The Riemann hypothesis holds if and only if
`ψ(x) = x + O(√x log² x)` as `x → ∞`. -/
theorem riemannHypothesis_iff_chebyshevPsi_sub_self_isBigO :
    RiemannHypothesis ↔ (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
      (fun x : ℝ => Real.sqrt x * Real.log x ^ 2) := by
  refine ⟨chebyshevPsi_sub_self_isBigO_of_riemannHypothesis, fun h s hs htriv hs1 => ?_⟩
  have hfree := riemannZeta_ne_zero_of_psi_sub_self_isBigO h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- reflect a zero with `Re s < 1/2` to `1 - s`
    have hre0 : 0 ≤ s.re := by
      by_contra h0
      obtain ⟨n, hn, rfl⟩ := exists_eq_neg_two_mul_of_riemannZeta_eq_zero_of_re_neg
        (not_le.mp h0) hs
      exact htriv ⟨n - 1, by
        rw [Nat.cast_sub (by omega)]; push_cast; ring⟩
    have hmem : s ∈ riemannZetaNontrivialZeros := ⟨hs, hre0, by linarith⟩
    have h1 := (one_sub_mem_riemannZetaNontrivialZeros hmem).1
    exact hfree (1 - s) (by simp; linarith) h1
  · exact hfree s hgt hs
