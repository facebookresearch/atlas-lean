/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Data.Nat.Nth
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

import Mathlib.Probability.Independence.InfinitePi
import MathlibExt.Probability.NonnegSLLN

/-!
# Cesàro means of random subsequences

This file defines the fair coin measure and proves Schreier's theorem that fair coin sampling
almost surely preserves the Cesàro limit of a bounded real sequence.
-/

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook4Wanted

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal

/-- **Fair coin measure.** The fair coin measure is the measure on the Booleans
$\{\mathrm{true}, \mathrm{false}\}$ that gives mass $1/2$ to each of $\mathrm{true}$ and
$\mathrm{false}$, that is,
$\frac{1}{2}\delta_{\mathrm{true}} + \frac{1}{2}\delta_{\mathrm{false}}$. -/
noncomputable def fairCoinMeasure : MeasureTheory.Measure Bool :=
  (1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac true +
    (1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac false

namespace schreierCesaroSubsequences

local instance fairCoinProbability : IsProbabilityMeasure fairCoinMeasure where
  measure_univ := by
    simp [fairCoinMeasure, ← two_mul, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

private noncomputable abbrev coinSequenceMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => fairCoinMeasure

private lemma integral_coinSequence_eval (f : Bool → ℝ) (i : ℕ) :
    (∫ ω, f (ω i) ∂coinSequenceMeasure) = (f true + f false) / 2 := by
  have hm : Measurable f := measurable_of_finite f
  rw [← integral_map (measurable_pi_apply i).aemeasurable hm.aestronglyMeasurable,
    Measure.infinitePi_map_eval]
  unfold fairCoinMeasure
  rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure (by simp))
    ((integrable_dirac (by simp)).smul_measure (by simp))]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- For weights bounded above and at least one, the retained sum divided by the original
prefix length tends to half of the original Cesàro limit. -/
private lemma ae_tendsto_retained_sum_div {b : ℕ → ℝ} {C L : ℝ}
    (hlo : ∀ i, 1 ≤ b i) (hhi : ∀ i, b i ≤ C)
    (hb : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, b i) / (n : ℝ)) atTop (𝓝 L)) :
    ∀ᵐ ω ∂coinSequenceMeasure, Tendsto
      (fun n : ℕ => (∑ i ∈ (Finset.range n).filter (fun i => ω i = true), b i) / (n : ℝ))
      atTop (𝓝 (L / 2)) := by
  let g (i : ℕ) (v : Bool) : ℝ := if v = true then b i else 0
  let Y (i : ℕ) (ω : ℕ → Bool) : ℝ := g i (ω i)
  have hg (i : ℕ) : Measurable (g i) := measurable_of_finite _
  have hY (i : ℕ) : Measurable (Y i) := (hg i).comp (measurable_pi_apply i)
  have hC : 0 ≤ C := (zero_le_one.trans (hlo 0)).trans (hhi 0)
  have hbounds (i : ℕ) (ω : ℕ → Bool) : Y i ω ∈ Set.Icc 0 C := by
    by_cases hv : ω i = true
    · simpa [Y, g, hv] using ⟨zero_le_one.trans (hlo i), hhi i⟩
    · simpa [Y, g, hv] using hC
  have hL2 (i : ℕ) : MemLp (Y i) 2 coinSequenceMeasure :=
    memLp_of_bounded (ae_of_all _ (hbounds i)) (hY i).aestronglyMeasurable _
  have hmean (i : ℕ) : coinSequenceMeasure[Y i] = b i / 2 := by
    simpa [Y, g] using integral_coinSequence_eval (g i) i
  have hvar (i : ℕ) : Var[Y i; coinSequenceMeasure] ≤ C * coinSequenceMeasure[Y i] := by
    have hsq : (∫ ω, (Y i ^ 2) ω ∂coinSequenceMeasure) = b i ^ 2 / 2 := by
      change (∫ ω, g i (ω i) ^ 2 ∂coinSequenceMeasure) = _
      rw [integral_coinSequence_eval (fun v => g i v ^ 2) i]
      norm_num [g]
    rw [variance_eq_sub (hL2 i), hsq, hmean]
    have hle := mul_le_mul_of_nonneg_right (hhi i) (zero_le_one.trans (hlo i))
    nlinarith [sq_nonneg (b i / 2)]
  have hindep : iIndepFun Y coinSequenceMeasure := iIndepFun_infinitePi hg
  let M (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, coinSequenceMeasure[Y i]
  have hM (n : ℕ) : M n = (∑ i ∈ Finset.range n, b i) / 2 := by
    simp only [M, hmean, Finset.sum_div]
  have hMtop : Tendsto M atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_natCast_atTop_atTop.const_mul_atTop (show (0 : ℝ) < 1 / 2 by norm_num))
    have hsum : (n : ℝ) ≤ ∑ i ∈ Finset.range n, b i := by
      simpa using (Finset.sum_le_sum fun i (_ : i ∈ Finset.range n) => hlo i)
    rw [hM]
    linarith
  have hMavg : Tendsto (fun n : ℕ => M n / (n : ℝ)) atTop (𝓝 (L / 2)) := by
    convert hb.div_const 2 using 1
    ext n
    rw [hM, div_right_comm]
  filter_upwards [ae_tendsto_sum_div_sum_integral (B := C) hL2
    (fun i => ae_of_all _ fun ω => (hbounds i ω).1) (fun _ _ hij => hindep.indepFun hij)
    (fun i => by rw [hmean]; linarith [hhi i]) hvar hMtop] with ω hω
  have hlim := hω.mul hMavg
  rw [one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [hMtop.eventually_ne_atTop 0] with n hn
  rw [Finset.sum_filter]
  change (∑ i ∈ Finset.range n, Y i ω) / M n * (M n / (n : ℝ)) =
    (∑ i ∈ Finset.range n, Y i ω) / (n : ℝ)
  rw [div_mul_div_cancel₀ hn]

/-- The retained terms before the `N`th selected index are the first `N` subsequence terms. -/
private lemma sum_filter_range_nth {p : ℕ → Prop} [DecidablePred p]
    (hp : (Set.ofPred p).Infinite) (b : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ (Finset.range (Nat.nth p N)).filter p, b i) =
      ∑ k ∈ Finset.range N, b (Nat.nth p k) := by
  induction N with
  | zero =>
    have hempty : (Finset.range (Nat.nth p 0)).filter p = ∅ := by
      rw [← Finset.card_eq_zero, ← Nat.count_eq_card_filter_range, Nat.count_nth_zero]
    simp [hempty]
  | succ N ih =>
    rw [Nat.filter_range_nth_eq_insert_of_infinite hp, Finset.sum_insert (by simp), ih,
      Finset.sum_range_succ, add_comm]

/-- Reindexing at successive selected indices turns the ratio of retained weight to retained
count into the Cesàro mean of the subsequence. -/
private lemma tendsto_subsequence_average {p : ℕ → Prop} [DecidablePred p] {b : ℕ → ℝ} {L : ℝ}
    (hb : Tendsto
      (fun n : ℕ => (∑ i ∈ (Finset.range n).filter p, b i) / (n : ℝ)) atTop (𝓝 (L / 2)))
    (hc : Tendsto (fun n : ℕ => (Nat.count p n : ℝ) / (n : ℝ)) atTop (𝓝 (1 / 2))) :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, b (Nat.nth p k)) / (N : ℝ)) atTop (𝓝 L) := by
  have hcount : Tendsto (fun n : ℕ => (Nat.count p n : ℝ)) atTop atTop := by
    refine (hc.pos_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hn)
  have hp : (Set.ofPred p).Infinite := by
    intro hfin
    obtain ⟨n, hn⟩ := (hcount.eventually_gt_atTop (hfin.toFinset.card : ℝ)).exists
    exact (not_lt_of_ge (by exact_mod_cast Nat.count_le_card hfin n)) hn
  have htop := (Nat.nth_strictMono hp).tendsto_atTop
  have hlim := (hb.comp htop).div (hc.comp htop) (by norm_num)
  rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0), div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [htop.eventually_ne_atTop 0] with N hN
  simp only [Pi.div_apply, Function.comp_apply]
  rw [sum_filter_range_nth hp, Nat.count_nth_of_infinite hp,
    div_div_div_cancel_right₀ (Nat.cast_ne_zero.mpr hN)]

private lemma average_add_const (b : ℕ → ℝ) (c : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (∑ i ∈ Finset.range n, (b i + c)) / (n : ℝ) =
      (∑ i ∈ Finset.range n, b i) / (n : ℝ) + c := by
  simp [Finset.sum_add_distrib, nsmul_eq_mul, add_div, Nat.cast_ne_zero.mpr hn]

end schreierCesaroSubsequences

/--
**Schreier's theorem on Cesàro means of random subsequences.** Let $(a_n)_{n \ge 0}$ be a
bounded sequence of real numbers whose Cesàro means $\frac{1}{n} \sum_{i < n} a_i$ converge
to a real number $S$ as $n \to \infty$. Give the space of Boolean sequences
$\omega = (\omega_n)_{n \ge 0}$ the infinite product of fair coin measures. For such $\omega$
let $n_0 < n_1 < \cdots$ list, in increasing order, the indices $n$ with
$\omega_n = \mathrm{true}$, with $n_k = 0$ whenever there are at most $k$ such indices. Then
for almost every $\omega$ the Cesàro means $\frac{1}{N} \sum_{k < N} a_{n_k}$ of the
subsequence $(a_{n_k})$ converge to $S$ as $N \to \infty$.

Identifying a subset of $\mathbb{N}$ with its indicator sequence $\omega$, this says that
almost every subsequence of $(a_n)$ has Cesàro means converging to $S$.

Source: J. Schreier, Problem 4 of the
Scottish Book, stated as a theorem in the Scottish Book typescript.
-/
theorem schreierCesaroSubsequences :
    ∀ (a : ℕ → ℝ) (S : ℝ), (∃ B : ℝ, ∀ n, |a n| ≤ B) →
      Filter.Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, a i) / (n : ℝ))
        Filter.atTop (nhds S) →
      ∀ᵐ ω ∂(MeasureTheory.Measure.infinitePi fun _ : ℕ => fairCoinMeasure),
        Filter.Tendsto (fun N : ℕ =>
          (∑ k ∈ Finset.range N, a (Nat.nth (fun n => ω n = true) k)) / (N : ℝ))
          Filter.atTop (nhds S) := by
  intro a S ⟨B, hB⟩ hlim
  open schreierCesaroSubsequences in
  let c := B + 1
  let b (i : ℕ) := a i + c
  have hlo (i : ℕ) : 1 ≤ b i := by
    dsimp [b, c]
    linarith [neg_abs_le (a i), hB i]
  have hhi (i : ℕ) : b i ≤ B + c := by
    dsimp [b]
    linarith [le_abs_self (a i), hB i]
  have hb : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, b i) / (n : ℝ)) atTop
      (𝓝 (S + c)) := by
    refine (hlim.add_const c).congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    exact (average_add_const a c hn).symm
  have hone : Tendsto (fun n : ℕ => (∑ _i ∈ Finset.range n, (1 : ℝ)) / (n : ℝ))
      atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    simp [Nat.cast_ne_zero.mpr hn]
  filter_upwards [ae_tendsto_retained_sum_div hlo hhi hb,
    ae_tendsto_retained_sum_div (C := 1) (fun _ => le_rfl) (fun _ => le_rfl) hone] with ω hω hc
  have hcount : Tendsto (fun n : ℕ => (Nat.count (fun i => ω i = true) n : ℝ) / (n : ℝ))
      atTop (𝓝 (1 / 2)) := by
    simpa [Nat.count_eq_card_filter_range] using hc
  have hsub := (tendsto_subsequence_average hω hcount).sub_const c
  rw [add_sub_cancel_right] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with N hN
  rw [average_add_const (fun k => a (Nat.nth (fun i => ω i = true) k)) c hN,
    add_sub_cancel_right]

end MathlibExt.Analysis.ScottishBook4Wanted
