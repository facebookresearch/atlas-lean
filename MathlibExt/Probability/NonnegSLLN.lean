/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance

import MathlibExt.Probability.PairwiseIndepSLLN

/-!
# A strong law for nonnegative, non-identically distributed variables

Pairwise independent, nonnegative, square-integrable random variables `Y₀, Y₁, …` with bounded
means `mᵢ = E Yᵢ ≤ B`, variances `Var Yᵢ ≤ C mᵢ` and divergent total mean `Mₙ = ∑_{i<n} mᵢ`
satisfy `(∑_{i<n} Yᵢ) / Mₙ → 1` almost surely. The variables need not be identically
distributed, so Mathlib's `ProbabilityTheory.strong_law_ae` does not apply. Poisson counts
`Yᵢ ∼ Po(mᵢ)` satisfy the variance hypothesis with `C = 1`; the indicator law
`ProbabilityTheory.pairwise_indep_slln` is the special case `B = C = 1`.

## Source

The subsequence-and-bracketing argument for nonnegative pairwise independent variables of
N. Etemadi, *On the laws of large numbers for nonnegative random variables*, J. Multivariate
Anal. 13 (1983), 187–193; here with the hypotheses `Var Yᵢ ≤ C E Yᵢ` and `E Yᵢ ≤ B` and
normalization by `E ∑_{i<n} Yᵢ`.

## Main results

* `ProbabilityTheory.ae_tendsto_sum_div_sum_integral`: the ratio strong law above.

## Implementation notes

The proof is the Chebyshev–Borel–Cantelli argument along a subsequence with `M_{σ(k)} ≈ k²`,
followed by bracketing, as in `ProbabilityTheory.pairwise_indep_slln`. It reuses that file's
`ProbabilityTheory.ae_tendsto_of_ae_eventually_abs_sub_lt`, Mathlib's Chebyshev inequality
`ProbabilityTheory.meas_ge_le_variance_div_sq`, `ProbabilityTheory.IndepFun.variance_sum` and the
Borel–Cantelli lemma `MeasureTheory.ae_eventually_notMem`.
-/

@[expose] public section

open MeasureTheory Filter Topology Function

namespace ProbabilityTheory

/-- Deterministic subsequence for the ratio strong law: if `M` starts at `0`, is monotone with
increments at most `B` and tends to `∞`, there is a strictly increasing `σ` with
`(k + 1)² ≤ M (σ k)` along which consecutive ratios `M (σ (k + 1)) / M (σ k)` tend to `1`. -/
private lemma exists_subseq_ratio {M : ℕ → ℝ} {B : ℝ} (hM0 : M 0 = 0) (hmono : Monotone M)
    (hstep : ∀ n, M (n + 1) ≤ M n + B) (htop : Tendsto M atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ (∀ k : ℕ, ((k : ℝ) + 1) ^ 2 ≤ M (σ k)) ∧
      Tendsto (fun k => M (σ (k + 1)) / M (σ k)) atTop (𝓝 1) := by
  set c := |B| + 1 with hc
  have hc1 : 1 ≤ c := by have := abs_nonneg B; linarith
  have hex : ∀ k : ℕ, ∃ n, ((k : ℝ) + c) ^ 2 ≤ M n := fun k =>
    (htop.eventually_ge_atTop _).exists
  classical
  let σ : ℕ → ℕ := fun k => Nat.find (hex k)
  have hkc : ∀ k : ℕ, 0 < (k : ℝ) + c := fun k => by
    have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hlow : ∀ k : ℕ, ((k : ℝ) + c) ^ 2 ≤ M (σ k) := fun k => Nat.find_spec (hex k)
  have hup : ∀ k : ℕ, M (σ k) ≤ ((k : ℝ) + c) ^ 2 + B := by
    intro k
    have hpos : σ k ≠ 0 := by
      intro h0
      have := hlow k
      rw [h0, hM0] at this
      linarith [pow_pos (hkc k) 2]
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    have hmin : ¬ ((k : ℝ) + c) ^ 2 ≤ M j := Nat.find_min (hex k)
      (show j < Nat.find (hex k) by have : Nat.find (hex k) = j + 1 := hj; omega)
    rw [hj]
    linarith [hstep j, not_le.1 hmin]
  have hMpos : ∀ k, 0 < M (σ k) := fun k => lt_of_lt_of_le (pow_pos (hkc k) 2) (hlow k)
  have hσ : StrictMono σ := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    by_contra h
    have h1 := hmono (not_lt.1 h)
    have h2 := hlow (k + 1)
    have h3 := hup k
    have hB : B < 2 * ((k : ℝ) + c) + 1 := by
      have := le_abs_self B; have := Nat.cast_nonneg (α := ℝ) k; linarith
    push_cast at h2
    have e : ((k : ℝ) + 1 + c) ^ 2 = ((k : ℝ) + c) ^ 2 + (2 * ((k : ℝ) + c) + 1) := by ring
    linarith
  refine ⟨σ, hσ, fun k => le_trans ?_ (hlow k), ?_⟩
  · have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  set u : ℕ → ℝ := fun k => 1 / ((k : ℝ) + c)
  have hu : Tendsto u atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun k => (1 + u k) ^ 2 + B * u k ^ 2) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add hu).pow 2 |>.add
      ((tendsto_const_nhds (x := B)).mul (hu.pow 2))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => ?_)
    (fun k => ?_)
  · exact (one_le_div (hMpos k)).2 (hmono (hσ.monotone (Nat.le_succ k)))
  · have h1 := hup (k + 1)
    have hk0 := hkc k
    push_cast at h1
    rw [div_le_iff₀ (hMpos k)]
    have h2 : ((1 + u k) ^ 2 + B * u k ^ 2) * ((k : ℝ) + c) ^ 2 =
        ((k : ℝ) + 1 + c) ^ 2 + B := by
      simp only [u]; field_simp; ring
    have h3 : (0 : ℝ) ≤ (1 + u k) ^ 2 + B * u k ^ 2 := by
      have hu0 : 0 ≤ u k := (one_div_pos.2 (hkc k)).le
      have : 0 ≤ (1 + u k) ^ 2 + B * u k ^ 2 - 1 := by
        have e : (1 + u k) ^ 2 + B * u k ^ 2 - 1 = u k * (2 + (1 + B) * u k) := by ring
        rw [e]
        refine mul_nonneg hu0 ?_
        have hBc : -B ≤ |B| := neg_le_abs B
        have huc : u k * ((k : ℝ) + c) = 1 := by simp only [u]; field_simp
        nlinarith [Nat.cast_nonneg (α := ℝ) k]
      linarith
    calc M (σ (k + 1)) ≤ ((k : ℝ) + 1 + c) ^ 2 + B := h1
      _ = ((1 + u k) ^ 2 + B * u k ^ 2) * ((k : ℝ) + c) ^ 2 := h2.symm
      _ ≤ ((1 + u k) ^ 2 + B * u k ^ 2) * M (σ k) := mul_le_mul_of_nonneg_left (hlow k) h3

/-- Deterministic bracketing: for nonnegative monotone `T` and monotone `M`, convergence of
`T / M` to `1` along a strictly increasing `σ` with consecutive ratios of `M ∘ σ` tending to `1`
gives convergence along the whole sequence. -/
private lemma tendsto_div_of_subseq {T M : ℕ → ℝ} {σ : ℕ → ℕ} (hT0 : ∀ n, 0 ≤ T n)
    (hTmono : Monotone T) (hMmono : Monotone M) (hσ : StrictMono σ) (hMpos : ∀ k, 0 < M (σ k))
    (hsub : Tendsto (fun k => T (σ k) / M (σ k)) atTop (𝓝 1))
    (hratio : Tendsto (fun k => M (σ (k + 1)) / M (σ k)) atTop (𝓝 1)) :
    Tendsto (fun n => T n / M n) atTop (𝓝 1) := by
  classical
  let κ : ℕ → ℕ := fun n => Nat.findGreatest (fun k => σ k ≤ n) n
  have hκ1 : ∀ n, σ 0 ≤ n → σ (κ n) ≤ n := fun n hn =>
    Nat.findGreatest_spec (P := fun k => σ k ≤ n) (Nat.zero_le n) hn
  have hκ2 : ∀ n, n < σ (κ n + 1) := fun n => by
    by_contra h
    have h' : σ (κ n + 1) ≤ n := not_lt.1 h
    have : κ n + 1 ≤ κ n := Nat.le_findGreatest (P := fun k => σ k ≤ n) ((hσ.id_le _).trans h') h'
    omega
  have hκ : Tendsto κ atTop atTop := tendsto_atTop.2 fun K => eventually_atTop.2
    ⟨σ K, fun n hn => Nat.le_findGreatest (P := fun k => σ k ≤ n) ((hσ.id_le K).trans hn) hn⟩
  have hL : Tendsto (fun k => T (σ k) / M (σ k) * (M (σ (k + 1)) / M (σ k))⁻¹) atTop (𝓝 1) := by
    simpa using hsub.mul (hratio.inv₀ one_ne_zero)
  have hU : Tendsto (fun k => T (σ (k + 1)) / M (σ (k + 1)) * (M (σ (k + 1)) / M (σ k))) atTop
      (𝓝 1) := by
    simpa using ((tendsto_add_atTop_iff_nat 1).2 hsub).mul hratio
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hL.comp hκ) (hU.comp hκ) ?_ ?_
  · filter_upwards [eventually_ge_atTop (σ 0)] with n hn
    have h1 := hκ1 n hn
    have hk := hMpos (κ n)
    have hk1 := hMpos (κ n + 1)
    have hMn : M (σ (κ n)) ≤ M n := hMmono h1
    have hMn' : M n ≤ M (σ (κ n + 1)) := hMmono (hκ2 n).le
    have e : T (σ (κ n)) / M (σ (κ n)) * (M (σ (κ n + 1)) / M (σ (κ n)))⁻¹ =
        T (σ (κ n)) / M (σ (κ n + 1)) := by field_simp
    simp only [Function.comp]
    rw [e]
    exact div_le_div₀ (hT0 n) (hTmono h1) (hk.trans_le hMn) hMn'
  · filter_upwards [eventually_ge_atTop (σ 0)] with n hn
    have h1 := hκ1 n hn
    have hk := hMpos (κ n)
    have hk1 := hMpos (κ n + 1)
    have hMn : M (σ (κ n)) ≤ M n := hMmono h1
    have e : T (σ (κ n + 1)) / M (σ (κ n + 1)) * (M (σ (κ n + 1)) / M (σ (κ n))) =
        T (σ (κ n + 1)) / M (σ (κ n)) := by field_simp
    simp only [Function.comp]
    rw [e]
    exact div_le_div₀ (hT0 _) (hTmono (hκ2 n).le) hk hMn

section SLLN

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Strong law for nonnegative, non-identically distributed variables.** Let `Y₀, Y₁, …` be
pairwise independent, a.e. nonnegative, square-integrable real random variables whose means
`mᵢ = E Yᵢ` are bounded by `B`, whose variances satisfy `Var Yᵢ ≤ C mᵢ`, and whose total mean
`Mₙ = ∑_{i<n} mᵢ` diverges. Then almost surely `(∑_{i<n} Yᵢ) / Mₙ → 1`.

For Poisson counts `Yᵢ ~ Po(mᵢ)` the variance hypothesis holds with `C = 1`. The proof is the
Chebyshev–Borel–Cantelli argument along a subsequence with `M_{σ(k)} ≈ k²`, followed by
bracketing, as in `ProbabilityTheory.pairwise_indep_slln` (the indicator case, `C = B = 1`). -/
theorem ae_tendsto_sum_div_sum_integral {Y : ℕ → Ω → ℝ} {B C : ℝ}
    (hL2 : ∀ i, MemLp (Y i) 2 μ) (hnonneg : ∀ i, 0 ≤ᵐ[μ] Y i)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y)) (hbdd : ∀ i, μ[Y i] ≤ B)
    (hvar : ∀ i, Var[Y i; μ] ≤ C * μ[Y i])
    (htop : Tendsto (fun n => ∑ i ∈ Finset.range n, μ[Y i]) atTop atTop) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (∑ i ∈ Finset.range n, Y i ω) / ∑ i ∈ Finset.range n, μ[Y i])
      atTop (𝓝 1) := by
  set M : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, μ[Y i] with hMdef
  have hm0 : ∀ i, 0 ≤ μ[Y i] := fun i => integral_nonneg_of_ae (hnonneg i)
  have hMmono : Monotone M := fun m n hmn =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn) fun i _ _ => hm0 i
  have hstep : ∀ n, M (n + 1) ≤ M n + B := fun n => by
    simp only [M, Finset.sum_range_succ]; linarith [hbdd n]
  obtain ⟨σ, hσ, hlow, hratio⟩ := exists_subseq_ratio (by simp [M]) hMmono hstep htop
  have hMpos : ∀ k, 0 < M (σ k) := fun k => lt_of_lt_of_le (by positivity) (hlow k)
  -- Chebyshev along the subsequence
  have hcheb : ∀ ε : ℝ, 0 < ε → ∀ k, μ {ω | ε ≤ |(∑ i ∈ Finset.range (σ k), Y i ω) / M (σ k) - 1|}
      ≤ ENNReal.ofReal (|C| / (ε ^ 2 * ((k : ℝ) + 1) ^ 2)) := by
    intro ε hε k
    set Tf : Ω → ℝ := ∑ i ∈ Finset.range (σ k), Y i with hTf
    have hTfω : ∀ ω, Tf ω = ∑ i ∈ Finset.range (σ k), Y i ω := fun ω => Finset.sum_apply _ _ _
    have hmem : MemLp Tf 2 μ := memLp_finsetSum' _ fun i _ => hL2 i
    have hint : μ[Tf] = M (σ k) := by
      simp only [hTfω]; exact integral_finsetSum _ fun i _ => (hL2 i).integrable one_le_two
    have hvarT : Var[Tf; μ] ≤ C * M (σ k) := by
      rw [IndepFun.variance_sum (fun i _ => hL2 i) (fun i _ j _ hij => hindep hij),
        show M (σ k) = ∑ i ∈ Finset.range (σ k), μ[Y i] from rfl, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hvar i
    have hMk := hMpos k
    have hsub : {ω | ε ≤ |(∑ i ∈ Finset.range (σ k), Y i ω) / M (σ k) - 1|} ⊆
        {ω | ε * M (σ k) ≤ |Tf ω - μ[Tf]|} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [hint, hTfω]
      rw [div_sub_one hMk.ne', abs_div, abs_of_pos hMk, le_div_iff₀ hMk] at hω
      exact hω
    refine (measure_mono hsub).trans ((meas_ge_le_variance_div_sq hmem (by positivity)).trans ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    have hk1 : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
    calc Var[Tf; μ] / (ε * M (σ k)) ^ 2 ≤ |C| * M (σ k) / (ε * M (σ k)) ^ 2 := by
          gcongr
          exact hvarT.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hMk.le)
      _ = |C| / (ε ^ 2 * M (σ k)) := by field_simp
      _ ≤ |C| / (ε ^ 2 * ((k : ℝ) + 1) ^ 2) := by
          gcongr
          exact hlow k
  have hsumm : ∀ ε : ℝ, 0 < ε →
      Summable fun k : ℕ => |C| / (ε ^ 2 * ((k : ℝ) + 1) ^ 2) := by
    intro ε hε
    have hshift : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
      have h2 := (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num : 1 < 2)
      have heq : (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) =
          (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) ∘ (· + 1) := by
        ext n; simp only [Function.comp, one_div]; push_cast; ring
      rw [heq]
      exact h2.comp_injective (fun a b hab => by omega)
    exact (hshift.mul_left (|C| / ε ^ 2)).congr fun k => by
      have hk : ((k : ℝ) + 1) ^ 2 ≠ 0 := by positivity
      field_simp
  have hae_sub : ∀ᵐ ω ∂μ, Tendsto (fun k => (∑ i ∈ Finset.range (σ k), Y i ω) / M (σ k)) atTop
      (𝓝 1) := by
    refine ae_tendsto_of_ae_eventually_abs_sub_lt fun m => ?_
    have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hfin : ∑' k, μ {ω | 1 / ((m : ℝ) + 1) ≤
        |(∑ i ∈ Finset.range (σ k), Y i ω) / M (σ k) - 1|} ≠ ⊤ :=
      ne_top_of_le_ne_top ((hsumm _ hε).tsum_ofReal_lt_top).ne
        (ENNReal.tsum_le_tsum fun k => hcheb _ hε k)
    filter_upwards [ae_eventually_notMem hfin] with ω hω
    exact hω.mono fun k hk => not_le.1 hk
  filter_upwards [hae_sub, ae_all_iff.2 hnonneg] with ω hω hnn
  refine tendsto_div_of_subseq (T := fun n => ∑ i ∈ Finset.range n, Y i ω)
    (fun n => Finset.sum_nonneg fun i _ => hnn i) (fun m n hmn =>
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn) fun i _ _ => hnn i)
    hMmono hσ hMpos hω hratio

end SLLN

end ProbabilityTheory
