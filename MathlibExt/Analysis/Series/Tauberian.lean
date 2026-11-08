/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Tauberian theorems for power series

This file proves two classical converses to **Abel's limit theorem**
(`Real.tendsto_tsum_powerSeries_nhdsWithin_lt` in Mathlib): while Abel's
theorem says that if the partial sums of `a : ℕ → ℝ` converge to `A` then the
Abel means `∑' n, a n * r ^ n` converge to `A` as `r → 1⁻`, the theorems here
go in the other direction, under a side condition on `a`.

* `tauber_tendsto_partial_sums`: **Tauber's theorem** (1897). If
  `∑' n, a n * r ^ n → A` as `r → 1⁻` and the Tauberian condition
  `n * aₙ → 0` holds, then the partial sums `∑_{n < N} aₙ` converge to `A`.
  The proof is the classical `r = 1 - 1 / N` estimate: the partial sum
  differs from the Abel mean by a head sum, bounded using `1 - rⁿ ≤ n (1 - r)`
  and the Tauberian condition, and a tail sum, bounded by a geometric series.
* `hardy_littlewood_tendsto_partial_sums`: the **Hardy–Littlewood Tauberian
  theorem** (1914). If `aₙ ≥ 0`, the series `∑ aₙ rⁿ` converges for every
  `r ∈ (0, 1)`, and its Abel limit as `r → 1⁻` is `A`, then the partial sums
  converge to `A`. The proof bounds the partial sums by `e` times the Abel
  mean at `r = 1 - 1 / (N + 1)` (using `log (1 - x) ≥ -x / (1 - x)`), so they
  are bounded; monotonicity then gives convergence, and Abel's theorem
  identifies the limit with `A`.

The conclusions are stated as convergence of partial sums, not as
`Summable a`, because in Mathlib `Summable` means unconditional convergence,
which fails for conditionally convergent series (e.g. the alternating harmonic
series).

The Abel hypothesis is a `Tendsto` statement about the `∑'` function. In
Tauber's theorem, summability of `aₙ rⁿ` for `r ∈ [0, 1)` follows from the
Tauberian condition (which bounds `|aₙ|`); in the Hardy–Littlewood theorem it
is an explicit hypothesis. This matters because `∑'` is `0` (junk) when the
series diverges, so the `Tendsto` hypothesis alone would also hold for
e.g. `aₙ = 2ⁿ` with `A = 0`.

References: A. Tauber, "Ein Satz aus der Theorie der unendlichen Reihen",
*Monatshefte für Mathematik und Physik* 8 (1897), 273–277;
G. H. Hardy and J. E. Littlewood, "Tauberian theorems concerning power series
and Dirichlet's series whose coefficients are positive",
*Proceedings of the London Mathematical Society* (2) 13 (1914), 174–191;
K. Knopp, *Theory and Application of Infinite Series*, § 101.
-/

@[expose] public section

namespace MathlibExt.Analysis.Series.Tauberian

open Filter Topology Set Finset

/-- A sequence converging to `0` is bounded in absolute value. -/
private theorem exists_bound_of_tendsto_zero {b : ℕ → ℝ}
    (hb : Tendsto b atTop (𝓝 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n, |b n| ≤ M := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hb) 1 one_pos
  refine ⟨1 + ∑ n ∈ Finset.range N, |b n|, by
    exact add_nonneg zero_le_one (Finset.sum_nonneg (fun _ _ => abs_nonneg _)), fun n => ?_⟩
  by_cases hn : n < N
  · calc |b n| ≤ ∑ k ∈ Finset.range N, |b k| :=
          Finset.single_le_sum (f := fun k => |b k|) (fun i _ => abs_nonneg _) (Finset.mem_range.mpr hn)
      _ ≤ 1 + ∑ k ∈ Finset.range N, |b k| := le_add_of_nonneg_left zero_le_one
  · have h := hN n (Nat.le_of_not_lt hn)
    rw [Real.dist_eq, sub_zero] at h
    exact h.le.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => abs_nonneg _)))

/-- For `r ∈ [0, 1]`, `1 - r ^ n ≤ n * (1 - r)`. -/
private theorem one_sub_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    1 - r ^ n ≤ n * (1 - r) := by
  have h := geom_sum_mul r n
  have hsum : ∑ k ∈ Finset.range n, r ^ k ≤ n := by
    calc ∑ k ∈ Finset.range n, r ^ k
        ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => pow_le_one₀ hr0 hr1
      _ = n := by simp
  have heq : 1 - r ^ n = (∑ k ∈ Finset.range n, r ^ k) * (1 - r) := by
    linear_combination h
  rw [heq]
  exact mul_le_mul_of_nonneg_right hsum (by linarith)

/-- **Tauber's theorem** (1897). If the power series `∑ aₙ rⁿ` converges (in the
Abel sense) to `A` as `r → 1⁻` and `n * aₙ → 0`, then the partial sums of `a`
converge to `A`. -/
theorem tauber_tendsto_partial_sums {a : ℕ → ℝ} {A : ℝ}
    (hAbel : Tendsto (fun r => ∑' n, a n * r ^ n) (𝓝[<] 1) (𝓝 A))
    (hTaub : Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 A) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_tendsto_zero hTaub
  have hsum : ∀ r ∈ Set.Ico (0 : ℝ) 1, Summable (fun n => a n * r ^ n) := by
    intro r ⟨hr0, hr1⟩
    refine Summable.of_norm_bounded (g := fun n => (M + |a 0|) * r ^ n) ?_ ?_
    · exact (summable_geometric_of_lt_one hr0 hr1).mul_left _
    · intro n
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hr0]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 n)
      rcases eq_or_ne n 0 with rfl | hn
      · simp [le_add_of_nonneg_left hM0]
      · have hn1 : (1 : ℝ) ≤ n := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        have h1 : |a n| = |(n : ℝ) * a n| / (n : ℝ) := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
          field_simp
        rw [h1]
        calc |(n : ℝ) * a n| / n ≤ M / n := by gcongr; exact hM n
          _ ≤ M / 1 := by gcongr
          _ = M := by simp
          _ ≤ M + |a 0| := le_add_of_nonneg_right (abs_nonneg _)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / 4 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hTaub) δ hδ
  obtain ⟨η, hη0, hη⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hAbel) δ hδ
  have hhead : ∀ᶠ (M : ℕ) in atTop,
      |∑ n ∈ Finset.range N1, a n * (1 - (1 - 1 / (M : ℝ)) ^ n)| < δ := by
    have h1 : Tendsto (fun M : ℕ => (1 : ℝ) - 1 / (M : ℝ)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun M : ℕ => (1 : ℝ) / (M : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      simpa using tendsto_const_nhds.sub h0
    have h2 : ∀ n : ℕ,
        Tendsto (fun M : ℕ => a n * (1 - (1 - 1 / (M : ℝ)) ^ n)) atTop
          (𝓝 (a n * (1 - 1 ^ n))) :=
      fun n => Tendsto.const_mul _ (Tendsto.const_sub _ (h1.pow n))
    have h3 := tendsto_finsetSum (Finset.range N1) (fun n _ => h2 n)
    have h4 : (∑ n ∈ Finset.range N1, a n * (1 - 1 ^ n)) = 0 := by simp
    rw [h4] at h3
    have hev := h3.eventually (Metric.ball_mem_nhds (0 : ℝ) hδ)
    exact hev.mono fun M hM => by rwa [Real.dist_eq, sub_zero] at hM
  rw [eventually_atTop] at hhead
  obtain ⟨N2, hN2⟩ := hhead
  obtain ⟨N3, hN3⟩ := (Metric.tendsto_atTop.mp (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))) η hη0
  set N0 := max (max (max N1 N2) N3) 1 with hN0def
  refine ⟨N0, fun M hM' => ?_⟩
  have hM1 : 1 ≤ M := by omega
  have hMN1 : N1 ≤ M := by omega
  have hMN2 : N2 ≤ M := by omega
  have hMN3 : N3 ≤ M := by omega
  set r : ℝ := 1 - 1 / (M : ℝ) with hrdef
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hr0 : 0 ≤ r := by
    rw [hrdef]
    have hle : (1 : ℝ) / (M : ℝ) ≤ 1 := by
      rw [div_le_one hMpos]
      exact_mod_cast hM1
    linarith
  have hr1 : r < 1 := by
    rw [hrdef]
    have hpos : (0 : ℝ) < 1 / (M : ℝ) := by positivity
    linarith
  have hrIco : r ∈ Set.Ico (0 : ℝ) 1 := ⟨hr0, hr1⟩
  have h1r : 1 - r = 1 / (M : ℝ) := by rw [hrdef]; ring
  have hAbelM : |(∑' n, a n * r ^ n) - A| < δ := by
    have h := hη (show r ∈ Set.Iio (1 : ℝ) from hr1) (by
      rw [Real.dist_eq]
      have heq : r - 1 = -(1 / (M : ℝ)) := by rw [hrdef]; ring
      rw [heq, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (M : ℝ))]
      have h3 := hN3 M hMN3
      rw [Real.dist_eq, sub_zero] at h3
      rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (M : ℝ))] at h3)
    rwa [Real.dist_eq] at h
  have hsplit := (hsum r hrIco).sum_add_tsum_nat_add M
  have hheadM : |∑ n ∈ Finset.range M, a n * (1 - r ^ n)| ≤ 2 * δ := by
    have hsplit2 := Finset.sum_range_add_sum_Ico (fun n => a n * (1 - r ^ n)) hMN1
    have h1 : |∑ n ∈ Finset.range N1, a n * (1 - r ^ n)| < δ := by
      have h := hN2 M hMN2
      rwa [← hrdef] at h
    have h2 : |∑ n ∈ Finset.Ico N1 M, a n * (1 - r ^ n)| ≤ δ := by
      have hterm : ∀ n ∈ Finset.Ico N1 M, |a n * (1 - r ^ n)| ≤ δ / (M : ℝ) := by
        intro n hn
        rw [Finset.mem_Ico] at hn
        rcases eq_or_ne n 0 with rfl | hn0
        · simp [le_of_lt (by positivity : (0 : ℝ) < δ / (M : ℝ))]
        · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
          have habs : |(n : ℝ) * a n| < δ := by
            have h := hN1 n hn.1
            rwa [Real.dist_eq, sub_zero] at h
          have hle1 : |a n| ≤ δ / (n : ℝ) := by
            have h1 : |a n| = |(n : ℝ) * a n| / (n : ℝ) := by
              rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
              field_simp
            rw [h1]
            gcongr
          have hle2 : 1 - r ^ n ≤ (n : ℝ) * (1 - r) := one_sub_pow_le hr0 hr1.le n
          have hnonneg : 0 ≤ 1 - r ^ n := by
            have hle : r ^ n ≤ 1 := pow_le_one₀ hr0 hr1.le
            linarith
          calc |a n * (1 - r ^ n)| = |a n| * (1 - r ^ n) := by
                rw [abs_mul, abs_of_nonneg hnonneg]
            _ ≤ (δ / (n : ℝ)) * ((n : ℝ) * (1 - r)) :=
                mul_le_mul hle1 hle2 (by linarith) (by positivity)
            _ = δ * (1 - r) := by field_simp
            _ = δ / (M : ℝ) := by rw [h1r]; field_simp
      calc |∑ n ∈ Finset.Ico N1 M, a n * (1 - r ^ n)|
          ≤ ∑ n ∈ Finset.Ico N1 M, |a n * (1 - r ^ n)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Finset.Ico N1 M, δ / (M : ℝ) := Finset.sum_le_sum hterm
        _ = (Finset.Ico N1 M).card • (δ / (M : ℝ)) := Finset.sum_const _
        _ = ((M - N1 : ℕ) : ℝ) * (δ / (M : ℝ)) := by
            rw [Nat.card_Ico, nsmul_eq_mul]
        _ ≤ M * (δ / (M : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast Nat.sub_le M N1
        _ = δ := by field_simp
    calc |∑ n ∈ Finset.range M, a n * (1 - r ^ n)|
        = |∑ n ∈ Finset.range N1, a n * (1 - r ^ n) +
            ∑ n ∈ Finset.Ico N1 M, a n * (1 - r ^ n)| := by rw [← hsplit2]
      _ ≤ |∑ n ∈ Finset.range N1, a n * (1 - r ^ n)| +
            |∑ n ∈ Finset.Ico N1 M, a n * (1 - r ^ n)| := abs_add_le _ _
      _ ≤ δ + δ := add_le_add h1.le h2
      _ = 2 * δ := by ring
  have htail : |∑' k, a (k + M) * r ^ (k + M)| ≤ δ := by
    have hsumm : Summable (fun k => a (k + M) * r ^ (k + M)) :=
      (summable_nat_add_iff M).mpr (hsum r hrIco)
    have hterm : ∀ k, |a (k + M) * r ^ (k + M)| ≤ (δ / (M : ℝ)) * r ^ (k + M) := by
      intro k
      rw [abs_mul, abs_pow, abs_of_nonneg hr0]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 _)
      have hkn : M ≤ k + M := Nat.le_add_left M k
      have hkn1 : (1 : ℝ) ≤ ((k + M : ℕ) : ℝ) := by
        have h1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
        have hle : (M : ℝ) ≤ ((k + M : ℕ) : ℝ) := by
          push_cast
          have h2 : (M : ℝ) ≤ (k : ℝ) + (M : ℝ) := le_add_of_nonneg_left (by positivity)
          linarith
        linarith
      have habs : |((k + M : ℕ) : ℝ) * a (k + M)| < δ := by
        have h := hN1 (k + M) (le_trans hMN1 hkn)
        rwa [Real.dist_eq, sub_zero] at h
      have hle : |a (k + M)| ≤ δ / ((k + M : ℕ) : ℝ) := by
        have h1 : |a (k + M)| = |((k + M : ℕ) : ℝ) * a (k + M)| / ((k + M : ℕ) : ℝ) := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k + M : ℕ) : ℝ))]
          field_simp
        rw [h1]
        gcongr
      calc |a (k + M)| ≤ δ / ((k + M : ℕ) : ℝ) := hle
        _ ≤ δ / (M : ℝ) := by gcongr
    have hgeom : ∑' k, (δ / (M : ℝ)) * r ^ (k + M) = δ * r ^ M := by
      rw [tsum_mul_left]
      have hshift : ∑' k, r ^ (k + M) = r ^ M * ∑' k, r ^ k := by
        have h1 : (fun k => r ^ (k + M)) = (fun k => r ^ M * r ^ k) := by
          funext k
          rw [pow_add, mul_comm]
        rw [h1, tsum_mul_left]
      rw [hshift, tsum_geometric_of_lt_one hr0 hr1, h1r]
      field_simp
    have hsumabs : Summable (fun k => |a (k + M) * r ^ (k + M)|) := hsumm.abs
    have hsumdom : Summable (fun k => (δ / (M : ℝ)) * r ^ (k + M)) :=
      ((summable_nat_add_iff M).mpr (summable_geometric_of_lt_one hr0 hr1)).mul_left _
    have h1 : ∑' k, a (k + M) * r ^ (k + M) ≤ ∑' k, |a (k + M) * r ^ (k + M)| :=
      hsumm.tsum_le_tsum (fun k => le_abs_self _) hsumabs
    have h2 : -∑' k, |a (k + M) * r ^ (k + M)| ≤ ∑' k, a (k + M) * r ^ (k + M) := by
      have h := (hsumabs.neg).tsum_le_tsum (fun k => neg_abs_le (a (k + M) * r ^ (k + M))) hsumm
      rwa [tsum_neg] at h
    have h3 : ∑' k, |a (k + M) * r ^ (k + M)| ≤ ∑' k, (δ / (M : ℝ)) * r ^ (k + M) :=
      hsumabs.tsum_le_tsum hterm hsumdom
    have h4 : |∑' k, a (k + M) * r ^ (k + M)| ≤ δ * r ^ M := by
      rw [hgeom] at h3
      exact abs_le.mpr ⟨(neg_le_neg h3).trans h2, h1.trans h3⟩
    calc |∑' k, a (k + M) * r ^ (k + M)| ≤ δ * r ^ M := h4
      _ ≤ δ * 1 := by
          apply mul_le_mul_of_nonneg_left _ hδ.le
          exact pow_le_one₀ hr0 hr1.le
      _ = δ := by simp
  have hdecomp : (∑ n ∈ Finset.range M, a n) - A =
      (∑ n ∈ Finset.range M, a n * (1 - r ^ n)) - (∑' k, a (k + M) * r ^ (k + M)) +
        ((∑' n, a n * r ^ n) - A) := by
    have hcomp : (∑ n ∈ Finset.range M, a n * (1 - r ^ n)) =
        (∑ n ∈ Finset.range M, a n) - ∑ n ∈ Finset.range M, a n * r ^ n := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      rw [mul_sub, mul_one]
    rw [hcomp]
    linear_combination hsplit
  calc dist (∑ n ∈ Finset.range M, a n) A
      = |(∑ n ∈ Finset.range M, a n) - A| := Real.dist_eq _ _
    _ = |(∑ n ∈ Finset.range M, a n * (1 - r ^ n)) - (∑' k, a (k + M) * r ^ (k + M)) +
          ((∑' n, a n * r ^ n) - A)| := by rw [hdecomp]
    _ ≤ |∑ n ∈ Finset.range M, a n * (1 - r ^ n)| + |∑' k, a (k + M) * r ^ (k + M)| +
          |(∑' n, a n * r ^ n) - A| := by
      have hsub : |(∑ n ∈ Finset.range M, a n * (1 - r ^ n)) -
            (∑' k, a (k + M) * r ^ (k + M))| ≤
          |∑ n ∈ Finset.range M, a n * (1 - r ^ n)| +
            |∑' k, a (k + M) * r ^ (k + M)| := by
        rw [sub_eq_add_neg]
        calc |(∑ n ∈ Finset.range M, a n * (1 - r ^ n)) +
              (-(∑' k, a (k + M) * r ^ (k + M)))|
            ≤ |∑ n ∈ Finset.range M, a n * (1 - r ^ n)| +
              |-(∑' k, a (k + M) * r ^ (k + M))| := abs_add_le _ _
          _ = |∑ n ∈ Finset.range M, a n * (1 - r ^ n)| +
              |∑' k, a (k + M) * r ^ (k + M)| := by rw [abs_neg]
      exact (abs_add_le _ _).trans (add_le_add hsub le_rfl)
    _ < 2 * δ + δ + δ := by
        apply add_lt_add_of_le_of_lt (add_le_add hheadM htail) hAbelM
    _ = ε := by rw [hδdef]; ring


/-- **Hardy–Littlewood Tauberian theorem** (1914). If `aₙ ≥ 0` and the power series
`∑ aₙ rⁿ` converges for every `r ∈ (0, 1)` with Abel limit `A` as `r → 1⁻`, then
the partial sums of `a` converge to `A`. -/
theorem hardy_littlewood_tendsto_partial_sums {a : ℕ → ℝ} {A : ℝ}
    (hnonneg : ∀ n, 0 ≤ a n)
    (hsum : ∀ r ∈ Set.Ioo (0 : ℝ) 1, Summable (fun n => a n * r ^ n))
    (hAbel : Tendsto (fun r => ∑' n, a n * r ^ n) (𝓝[<] 1) (𝓝 A)) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 A) := by
  have hmono : Monotone (fun N => ∑ n ∈ Finset.range N, a n) := by
    intro m n hmn
    have hsub : Finset.range m ⊆ Finset.range n := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnonneg i)
  have hbdd : BddAbove (Set.range (fun N => ∑ n ∈ Finset.range N, a n)) := by
    -- Key estimate: for `N ≥ 1` and `r = 1 - 1 / (N + 1)`, `s N ≤ e * A(r)`.
    have hbound : ∀ N : ℕ, 1 ≤ N →
        (∑ n ∈ Finset.range N, a n) ≤
          Real.exp 1 * (∑' n, a n * (1 - 1 / ((N : ℝ) + 1)) ^ n) := by
      intro N hN1
      set r : ℝ := 1 - 1 / ((N : ℝ) + 1) with hrdef
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by linarith
      have hr0 : 0 < r := by
        rw [hrdef]
        have hlt : (1 : ℝ) / ((N : ℝ) + 1) < 1 := by
          rw [div_lt_one hN1pos]
          linarith [Nat.cast_nonneg (α := ℝ) N]
        linarith
      have hr1 : r < 1 := by
        rw [hrdef]
        have hpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
        linarith
      have hterm : ∀ n ∈ Finset.range N, a n ≤ (a n * r ^ n) * (r ^ N)⁻¹ := by
        intro n hn
        rw [Finset.mem_range] at hn
        have hpow : r ^ N ≤ r ^ n := pow_le_pow_of_le_one hr0.le hr1.le hn.le
        have h1 : a n * r ^ N ≤ a n * r ^ n := mul_le_mul_of_nonneg_left hpow (hnonneg n)
        have h2 : (0 : ℝ) < r ^ N := pow_pos hr0 N
        calc a n = (a n * r ^ N) * (r ^ N)⁻¹ := by
              rw [mul_inv_cancel_right₀ (ne_of_gt h2)]
          _ ≤ (a n * r ^ n) * (r ^ N)⁻¹ :=
              mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr h2.le)
      have hsumr := hsum r ⟨hr0, hr1⟩
      have hinv : (r ^ N)⁻¹ ≤ Real.exp 1 := by
        have hlog : Real.log r ≥ -(1 / (N : ℝ)) := by
          have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < r from hr0)
          have hr_eq : r = (N : ℝ) / ((N : ℝ) + 1) := by
            rw [hrdef, eq_div_iff hN1pos.ne', sub_mul, one_mul,
              div_mul_cancel₀ _ hN1pos.ne']
            ring
          have hrinv : r⁻¹ = ((N : ℝ) + 1) / (N : ℝ) := by
            rw [hr_eq, inv_div]
          rw [hrinv] at h
          have heq : (1 : ℝ) - ((N : ℝ) + 1) / (N : ℝ) = -(1 / (N : ℝ)) := by
            field_simp
            ring
          rw [heq] at h
          exact h
        calc (r ^ N)⁻¹ = (r⁻¹) ^ N := by rw [inv_pow]
          _ = Real.exp ((N : ℝ) * Real.log r⁻¹) := by
              rw [Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hr0)]
          _ ≤ Real.exp 1 := by
              apply Real.exp_le_exp.mpr
              rw [Real.log_inv]
              have h2 : -((N : ℝ) * Real.log r) ≤ (N : ℝ) * (1 / (N : ℝ)) := by
                have h4 : -Real.log r ≤ 1 / (N : ℝ) := by simpa using neg_le_neg hlog
                calc -((N : ℝ) * Real.log r) = (N : ℝ) * (-Real.log r) := by ring
                  _ ≤ (N : ℝ) * (1 / (N : ℝ)) :=
                      mul_le_mul_of_nonneg_left h4 (by positivity)
              have h3 : (N : ℝ) * (1 / (N : ℝ)) = 1 := mul_one_div_cancel hNpos.ne'
              calc (N : ℝ) * (-Real.log r) = -((N : ℝ) * Real.log r) := by ring
                _ ≤ (N : ℝ) * (1 / (N : ℝ)) := h2
                _ = 1 := h3
      have htsum_nonneg : 0 ≤ ∑' n, a n * r ^ n :=
        tsum_nonneg fun n => mul_nonneg (hnonneg n) (pow_nonneg hr0.le n)
      calc (∑ n ∈ Finset.range N, a n)
          ≤ ∑ n ∈ Finset.range N, (a n * r ^ n) * (r ^ N)⁻¹ := Finset.sum_le_sum hterm
        _ = (∑ n ∈ Finset.range N, a n * r ^ n) * (r ^ N)⁻¹ := by
            rw [Finset.sum_mul]
        _ ≤ (∑' n, a n * r ^ n) * (r ^ N)⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (pow_pos hr0 N).le)
            exact hsumr.sum_le_tsum (Finset.range N)
              (fun i _ => mul_nonneg (hnonneg i) (pow_nonneg hr0.le i))
        _ ≤ (∑' n, a n * r ^ n) * Real.exp 1 :=
            mul_le_mul_of_nonneg_left hinv htsum_nonneg
        _ = Real.exp 1 * (∑' n, a n * r ^ n) := mul_comm _ _
    -- The Abel values at `r = 1 - 1 / (N + 1)` are eventually bounded by `|A| + 1`.
    obtain ⟨η, hη0, hη⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hAbel) 1 one_pos
    obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))) η hη0
    set N2 := max N1 1 with hN2def
    have hAbdd : ∀ N : ℕ, N2 ≤ N →
        (∑' n, a n * (1 - 1 / ((N : ℝ) + 1)) ^ n) ≤ |A| + 1 := by
      intro N hN
      have hN1' : N1 ≤ N := le_trans (le_max_left _ _) hN
      have hdist : dist (1 - 1 / ((N : ℝ) + 1)) 1 < η := by
        have h5 := hN1 N hN1'
        rw [Real.dist_eq, sub_zero] at h5
        rw [Real.dist_eq]
        have heq : (1 - 1 / ((N : ℝ) + 1)) - 1 = -(1 / ((N : ℝ) + 1)) := by ring
        rw [heq, abs_neg]
        exact h5
      have h := hη (show (1 - 1 / ((N : ℝ) + 1)) ∈ Set.Iio (1 : ℝ) from by
        rw [Set.mem_Iio]
        have hpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
        linarith) hdist
      rw [Real.dist_eq] at h
      have hle : (∑' n, a n * (1 - 1 / ((N : ℝ) + 1)) ^ n) - A ≤ 1 :=
        (le_abs_self _).trans h.le
      calc (∑' n, a n * (1 - 1 / ((N : ℝ) + 1)) ^ n)
          = ((∑' n, a n * (1 - 1 / ((N : ℝ) + 1)) ^ n) - A) + A := by ring
        _ ≤ 1 + A := add_le_add hle le_rfl
        _ ≤ 1 + |A| := by linarith [le_abs_self A]
        _ = |A| + 1 := by ring
    refine ⟨max (∑ n ∈ Finset.range N2, a n) (Real.exp 1 * (|A| + 1)), fun x hx => ?_⟩
    obtain ⟨N, rfl⟩ := hx
    by_cases hN : N2 ≤ N
    · calc (∑ n ∈ Finset.range N, a n)
          ≤ Real.exp 1 * (∑' n, a n * (1 - 1 / ((N : ℝ) + 1)) ^ n) :=
            hbound N (le_trans (le_max_right _ _) hN)
        _ ≤ Real.exp 1 * (|A| + 1) :=
            mul_le_mul_of_nonneg_left (hAbdd N hN) (Real.exp_nonneg 1)
        _ ≤ max (∑ n ∈ Finset.range N2, a n) (Real.exp 1 * (|A| + 1)) := le_max_right _ _
    · calc (∑ n ∈ Finset.range N, a n) ≤ ∑ n ∈ Finset.range N2, a n :=
          hmono (le_of_not_ge hN)
        _ ≤ max (∑ n ∈ Finset.range N2, a n) (Real.exp 1 * (|A| + 1)) := le_max_left _ _
  have hlim := tendsto_atTop_ciSup hmono hbdd
  have hAbel2 := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hlim
  have hEq : (⨆ N, ∑ n ∈ Finset.range N, a n) = A := tendsto_nhds_unique hAbel2 hAbel
  rw [← hEq]
  exact hlim

end MathlibExt.Analysis.Series.Tauberian
