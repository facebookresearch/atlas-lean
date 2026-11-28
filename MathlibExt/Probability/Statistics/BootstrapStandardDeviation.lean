/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw

/-!
# Consistency of the bootstrap standard deviation

For i.i.d. real observations `X₀, X₁, …` with finite positive variance `σ²`, the standard
deviation `s*_m` of a bootstrap sample of size `m` drawn from `X₀, …, X_n` converges to `σ` in
conditional probability given the data, along almost every sample sequence, as `n` and `m` tend
to infinity jointly (`bootstrap_sd_tendsto`; P. J. Bickel and D. A. Freedman, "Some asymptotic
theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, Theorem 2.1(b)).

Resampling is written through the indices: a bootstrap sample of size `m` from `X₀, …, X_n` is
`X_{I(1)}, …, X_{I(m)}` for a uniformly random map `I : Fin m → Fin (n + 1)`, so a conditional
probability given the data is the proportion of the `(n + 1)^m` maps `I` with the property.

## Proof

Fix the data and write `s*_m² = (1/m) ∑_j X*_j² - (μ*_m)²`, where `μ*_m` is the bootstrap mean.
Under the uniform law on maps the draws `X*_j` are independent with the empirical law, so the
second moment of a centred bootstrap sum is computed exactly, and Chebyshev's inequality bounds
the conditional probability that `μ*_m` is at least `t` away from the sample mean by the
empirical second moment divided by `m t²`. For the bootstrap second moment, truncate `X*_j²` at a
level `K`: Chebyshev's inequality controls the bounded part in the same way, and Markov's
inequality controls the part above `K` through the empirical mean of `(X_i² - K)⁺`. The strong
law of large numbers, applied to `X`, `X²` and `(X² - K)⁺` for every `K ∈ ℕ`, gives the limits of
these empirical means for almost every sample sequence, and dominated convergence makes
`E (X₀² - K)⁺` small for large `K`.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace MathlibExt.Probability.Statistics.BootstrapWanted

/-- Summing a function of one coordinate over all maps `Fin m → Fin N`. -/
private lemma sum_comp_apply {N m : ℕ} (g : Fin N → ℝ) (j : Fin m) :
    ∑ I : Fin m → Fin N, g (I j) = (N : ℝ) ^ (m - 1) * ∑ i, g i := by
  classical
  have h := Fintype.prod_sum (fun (l : Fin m) (i : Fin N) => if l = j then g i else 1)
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true] at h
  rw [← h, Fintype.prod_eq_mul_prod_compl j]
  rw [Finset.prod_congr rfl (g := fun _ => (N : ℝ)) fun l hl => by
    rw [Finset.mem_compl, Finset.mem_singleton] at hl
    simp [hl]]
  simp [Finset.prod_const, Finset.card_compl, mul_comm]

/-- Two distinct coordinates of a uniform map are uncorrelated for a centred function. -/
private lemma sum_comp_apply_mul {N m : ℕ} (g : Fin N → ℝ) (hg : ∑ i, g i = 0) {j k : Fin m}
    (hjk : j ≠ k) : ∑ I : Fin m → Fin N, g (I j) * g (I k) = 0 := by
  classical
  have h := Fintype.prod_sum
    (fun (l : Fin m) (i : Fin N) => (if l = j then g i else 1) * (if l = k then g i else 1))
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true] at h
  rw [← h]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hjk, hg])

/-- The second moment of a centred sum over the coordinates of a uniform map. -/
private lemma sum_sq_sum_comp_apply {N m : ℕ} (g : Fin N → ℝ) (hg : ∑ i, g i = 0) :
    ∑ I : Fin m → Fin N, (∑ j, g (I j)) ^ 2 = m * (N : ℝ) ^ (m - 1) * ∑ i, g i ^ 2 := by
  calc ∑ I : Fin m → Fin N, (∑ j, g (I j)) ^ 2
      = ∑ I : Fin m → Fin N, ∑ j, ∑ k, g (I j) * g (I k) := by
        simp only [sq, Finset.sum_mul_sum]
    _ = ∑ j, ∑ k, ∑ I : Fin m → Fin N, g (I j) * g (I k) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j : Fin m, ∑ I : Fin m → Fin N, g (I j) ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_eq_single j (fun k _ hkj => sum_comp_apply_mul g hg (Ne.symm hkj))
          (by simp)]
        simp [sq]
    _ = m * (N : ℝ) ^ (m - 1) * ∑ i, g i ^ 2 := by
        simp only [sum_comp_apply (fun i => g i ^ 2)]
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

/-- Markov's inequality for counting measure. -/
private lemma card_filter_le_sum {α : Type*} (s : Finset α) (F : α → ℝ) (hF : ∀ a ∈ s, 0 ≤ F a)
    {t : ℝ} (ht : 0 < t) :
    ((s.filter fun a => t ≤ F a).card : ℝ) ≤ (∑ a ∈ s, F a) / t := by
  rw [le_div_iff₀ ht]
  calc ((s.filter fun a => t ≤ F a).card : ℝ) * t = ∑ a ∈ s.filter (fun a => t ≤ F a), t := by
        simp
    _ ≤ ∑ a ∈ s.filter (fun a => t ≤ F a), F a :=
        Finset.sum_le_sum fun a ha => (Finset.mem_filter.1 ha).2
    _ ≤ ∑ a ∈ s, F a :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun a ha _ => hF a ha

/-- `N ^ (m - 1) / N ^ m = 1 / N` for `N, m ≥ 1`. -/
private lemma pow_inv_mul_pow_pred {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    ((N : ℝ) ^ m)⁻¹ * (N : ℝ) ^ (m - 1) = (N : ℝ)⁻¹ := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
  simp only [zero_add, Nat.add_sub_cancel]
  rw [pow_succ]
  field_simp

/-- Markov's inequality for the bootstrap mean of a nonnegative function. -/
private lemma markov {N m : ℕ} (hN : 0 < N) (hm : 0 < m) (g : Fin N → ℝ) (hg : ∀ i, 0 ≤ g i)
    {t : ℝ} (ht : 0 < t) :
    ((N : ℝ) ^ m)⁻¹ * ((Finset.univ.filter fun I : Fin m → Fin N =>
        t ≤ (m : ℝ)⁻¹ * ∑ j, g (I j)).card : ℝ) ≤ ((N : ℝ)⁻¹ * ∑ i, g i) / t := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hsum : ∑ I : Fin m → Fin N, (m : ℝ)⁻¹ * ∑ j, g (I j) = (N : ℝ) ^ (m - 1) * ∑ i, g i := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [sum_comp_apply g, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have h := card_filter_le_sum Finset.univ (fun I : Fin m → Fin N => (m : ℝ)⁻¹ * ∑ j, g (I j))
    (fun I _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => hg _)) ht
  rw [hsum] at h
  calc ((N : ℝ) ^ m)⁻¹ * _ ≤ ((N : ℝ) ^ m)⁻¹ * (((N : ℝ) ^ (m - 1) * ∑ i, g i) / t) := by
        gcongr
    _ = ((N : ℝ)⁻¹ * ∑ i, g i) / t := by
        rw [← mul_div_assoc, ← mul_assoc, pow_inv_mul_pow_pred hN hm]

/-- Chebyshev's inequality for the bootstrap mean, with the empirical second moment in place of
the empirical variance. -/
private lemma chebyshev {N m : ℕ} (hN : 0 < N) (hm : 0 < m) (g : Fin N → ℝ) {t : ℝ}
    (ht : 0 < t) :
    ((N : ℝ) ^ m)⁻¹ * ((Finset.univ.filter fun I : Fin m → Fin N =>
        t ≤ |(m : ℝ)⁻¹ * ∑ j, g (I j) - (N : ℝ)⁻¹ * ∑ i, g i|).card : ℝ) ≤
      ((N : ℝ)⁻¹ * ∑ i, g i ^ 2) / (m * t ^ 2) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  set c := (N : ℝ)⁻¹ * ∑ i, g i with hc
  set h : Fin N → ℝ := fun i => g i - c with hh
  have hsum0 : ∑ i, h i = 0 := by
    simp only [hh, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hc]
    field_simp
    ring
  have hcen : ∀ I : Fin m → Fin N,
      (m : ℝ)⁻¹ * ∑ j, g (I j) - c = (m : ℝ)⁻¹ * ∑ j, h (I j) := by
    intro I
    simp only [hh, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have hsq : ∑ i, h i ^ 2 ≤ ∑ i, g i ^ 2 := by
    have : ∑ i, h i ^ 2 = ∑ i, g i ^ 2 - N * c ^ 2 := by
      simp only [hh, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
      rw [hc]
      field_simp
      ring
    rw [this]
    nlinarith [sq_nonneg c, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hsub : (Finset.univ.filter fun I : Fin m → Fin N =>
        t ≤ |(m : ℝ)⁻¹ * ∑ j, g (I j) - c|) ⊆
      (Finset.univ.filter fun I : Fin m → Fin N => t ^ 2 ≤ ((m : ℝ)⁻¹ * ∑ j, h (I j)) ^ 2) := by
    intro I hI
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI ⊢
    rw [hcen] at hI
    calc t ^ 2 ≤ |(m : ℝ)⁻¹ * ∑ j, h (I j)| ^ 2 := by gcongr
      _ = _ := sq_abs _
  have h2 := card_filter_le_sum Finset.univ
    (fun I : Fin m → Fin N => ((m : ℝ)⁻¹ * ∑ j, h (I j)) ^ 2) (fun I _ => sq_nonneg _)
    (pow_pos ht 2)
  have hval : ∑ I : Fin m → Fin N, ((m : ℝ)⁻¹ * ∑ j, h (I j)) ^ 2 =
      (m : ℝ)⁻¹ * (N : ℝ) ^ (m - 1) * ∑ i, h i ^ 2 := by
    simp only [mul_pow, ← Finset.mul_sum, sum_sq_sum_comp_apply h hsum0]
    field_simp
  rw [hval] at h2
  have hcard := (Nat.cast_le (α := ℝ)).2 (Finset.card_le_card hsub)
  calc ((N : ℝ) ^ m)⁻¹ * _ ≤ ((N : ℝ) ^ m)⁻¹ *
        (((m : ℝ)⁻¹ * (N : ℝ) ^ (m - 1) * ∑ i, h i ^ 2) / t ^ 2) := by
        gcongr
        exact hcard.trans h2
    _ = ((N : ℝ)⁻¹ * ∑ i, h i ^ 2) / (m * t ^ 2) := by
        rw [show ((N : ℝ) ^ m)⁻¹ * (((m : ℝ)⁻¹ * (N : ℝ) ^ (m - 1) * ∑ i, h i ^ 2) / t ^ 2) =
          (((N : ℝ) ^ m)⁻¹ * (N : ℝ) ^ (m - 1)) * ((m : ℝ)⁻¹ * (∑ i, h i ^ 2) / t ^ 2) by ring,
          pow_inv_mul_pow_pred hN hm]
        field_simp
    _ ≤ ((N : ℝ)⁻¹ * ∑ i, g i ^ 2) / (m * t ^ 2) := by
        gcongr

/-- The plug-in variance of a finite sample is its second moment minus the square of its mean. -/
private lemma var_eq {m : ℕ} (hm : (m : ℝ) ≠ 0) (y : Fin m → ℝ) :
    (m : ℝ)⁻¹ * ∑ j, (y j - (m : ℝ)⁻¹ * ∑ l, y l) ^ 2 =
      (m : ℝ)⁻¹ * ∑ j, y j ^ 2 - ((m : ℝ)⁻¹ * ∑ j, y j) ^ 2 := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  field_simp
  ring

/-- A nonnegative function tends to zero if it is eventually below every positive level. -/
private lemma tendsto_zero_of_eventually_le {α : Type*} {l : Filter α} {f : α → ℝ}
    (h0 : ∀ a, 0 ≤ f a) (h : ∀ γ > 0, ∀ᶠ a in l, f a ≤ γ) : Tendsto f l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro γ hγ
  filter_upwards [h (γ / 2) (half_pos hγ)] with a ha
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (h0 a)]
  linarith

/-- Truncation at `K` splits `a` into a part at most `K` and a nonnegative excess. -/
private lemma min_add_max_sub (a K : ℝ) : min a K + max (a - K) 0 = a := by
  rcases le_total a K with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_left (by linarith)]
    ring

/-- The bootstrap standard deviation is consistent for a fixed data sequence whose empirical first
and second moments converge, to `μ` and `σ² + μ²`, and whose empirical second moments are
uniformly integrable, in the form that the empirical means of `(x_i² - K)⁺` are eventually small
for large `K`. -/
private theorem tendsto_card_bad {x : ℕ → ℝ} {μ σ : ℝ} (hσ : 0 < σ)
    (hmean : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), x i)
      atTop (𝓝 μ))
    (hsq : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), x i ^ 2)
      atTop (𝓝 (σ ^ 2 + μ ^ 2)))
    (htail : ∀ κ > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), max (x i ^ 2 - K) 0 < κ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun nm : ℕ × ℕ =>
        (((nm.1 + 1 : ℕ) : ℝ) ^ nm.2)⁻¹ *
          ((Finset.univ.filter fun I : Fin nm.2 → Fin (nm.1 + 1) =>
            ε < |Real.sqrt ((nm.2 : ℝ)⁻¹ * ∑ j, (x (I j) -
              (nm.2 : ℝ)⁻¹ * ∑ l, x (I l)) ^ 2) - σ|).card : ℝ))
      (atTop ×ˢ atTop) (𝓝 0) := by
  set τ := σ ^ 2 + μ ^ 2 with hτ
  set δ := ε * σ with hδ
  have hδpos : 0 < δ := mul_pos hε hσ
  set η := min 1 (δ / (5 * (2 * |μ| + 1))) with hη
  have hηpos : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hημ : η * (2 * |μ| + 1) ≤ δ / 5 := by
    have := min_le_right 1 (δ / (5 * (2 * |μ| + 1)))
    calc η * (2 * |μ| + 1) ≤ δ / (5 * (2 * |μ| + 1)) * (2 * |μ| + 1) := by gcongr
      _ = δ / 5 := by field_simp
  refine tendsto_zero_of_eventually_le (fun nm => by positivity) fun γ hγ => ?_
  set κ := min (δ / 5) (γ * δ / 10) with hκ
  have hκpos : 0 < κ := lt_min (by positivity) (by positivity)
  obtain ⟨K, hK⟩ := htail κ hκpos
  set A := (K : ℝ) ^ 2 / (δ / 5) ^ 2 + (τ + 1) / (η / 2) ^ 2 with hA
  have hm_ev : ∀ᶠ m : ℕ in atTop, 0 < m ∧ A / m ≤ γ / 2 :=
    (eventually_gt_atTop 0).and
      ((tendsto_const_div_atTop_nhds_zero_nat A).eventually (ge_mem_nhds (half_pos hγ)))
  have hn_ev : ∀ᶠ n : ℕ in atTop,
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), max (x i ^ 2 - K) 0 < κ ∧
      |((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), x i ^ 2 - τ| < δ / 5 ∧
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), x i ^ 2 ≤ τ + 1 ∧
      |((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), x i - μ| < η / 2 := by
    refine (hK.and ((Metric.tendsto_nhds.1 hsq (δ / 5) (by positivity)).and
      ((hsq.eventually (ge_mem_nhds (lt_add_one τ))).and
        (Metric.tendsto_nhds.1 hmean (η / 2) (by positivity))))).mono ?_
    rintro n ⟨h1, h2, h3, h4⟩
    exact ⟨h1, by rwa [Real.dist_eq] at h2, h3, by rwa [Real.dist_eq] at h4⟩
  filter_upwards [hn_ev.prod_inl atTop, hm_ev.prod_inr atTop] with nm hn hm
  obtain ⟨n, m⟩ := nm
  obtain ⟨hv, hy, hy1, hx⟩ := hn
  obtain ⟨hm, hAm⟩ := hm
  dsimp only at hv hy hy1 hx hm hAm ⊢
  have hN : 0 < n + 1 := Nat.succ_pos n
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← Fin.sum_univ_eq_sum_range (fun i => max (x i ^ 2 - K) 0)] at hv
  rw [← Fin.sum_univ_eq_sum_range (fun i => x i ^ 2)] at hy hy1
  rw [← Fin.sum_univ_eq_sum_range (fun i => x i)] at hx
  -- Three events control the bad resamples: the bounded part of the bootstrap second moment
  -- deviates, its part above `K` is large, or the bootstrap mean deviates.
  set E₁ := Finset.univ.filter fun I : Fin m → Fin (n + 1) =>
    δ / 5 ≤ |(m : ℝ)⁻¹ * ∑ j, min (x (I j) ^ 2) (K : ℝ) -
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (n + 1), min (x i ^ 2) (K : ℝ)| with hE₁
  set E₂ := Finset.univ.filter fun I : Fin m → Fin (n + 1) =>
    δ / 5 ≤ (m : ℝ)⁻¹ * ∑ j, max (x (I j) ^ 2 - K) 0 with hE₂
  set E₃ := Finset.univ.filter fun I : Fin m → Fin (n + 1) =>
    η / 2 ≤ |(m : ℝ)⁻¹ * ∑ j, x (I j) - ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (n + 1), x i| with hE₃
  have hsub : (Finset.univ.filter fun I : Fin m → Fin (n + 1) =>
        ε < |Real.sqrt ((m : ℝ)⁻¹ * ∑ j, (x (I j) - (m : ℝ)⁻¹ * ∑ l, x (I l)) ^ 2) - σ|) ⊆
      E₁ ∪ E₂ ∪ E₃ := by
    intro I hI
    simp only [hE₁, hE₂, hE₃, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and] at hI ⊢
    by_contra hcon
    simp only [not_or, not_le] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    set a := (m : ℝ)⁻¹ * ∑ j, x (I j) with ha
    set b := (m : ℝ)⁻¹ * ∑ j, x (I j) ^ 2 with hb
    set U := (m : ℝ)⁻¹ * ∑ j, min (x (I j) ^ 2) (K : ℝ) with hU
    set W := (m : ℝ)⁻¹ * ∑ j, max (x (I j) ^ 2 - K) 0 with hW
    set ubar := ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (n + 1), min (x i ^ 2) (K : ℝ) with hubar
    set vbar := ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (n + 1), max (x i ^ 2 - K) 0 with hvbar
    set ybar := ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (n + 1), x i ^ 2 with hybar
    set xbar := ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (n + 1), x i with hxbar
    have hbUW : b = U + W := by
      simp only [hb, hU, hW, ← mul_add, ← Finset.sum_add_distrib, min_add_max_sub]
    have hyuv : ybar = ubar + vbar := by
      simp only [hybar, hubar, hvbar, ← mul_add, ← Finset.sum_add_distrib, min_add_max_sub]
    have hW0 : 0 ≤ W :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => le_max_right _ _)
    have hv0 : 0 ≤ vbar :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => le_max_right _ _)
    have hV : (m : ℝ)⁻¹ * ∑ j, (x (I j) - (m : ℝ)⁻¹ * ∑ l, x (I l)) ^ 2 = b - a ^ 2 :=
      var_eq hm' (fun j => x (I j))
    have hV0 : 0 ≤ b - a ^ 2 := by
      rw [← hV]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => sq_nonneg _)
    rw [hV] at hI
    have had : |a - μ| < η := by
      calc |a - μ| = |(a - xbar) + (xbar - μ)| := by ring_nf
        _ ≤ |a - xbar| + |xbar - μ| := abs_add_le _ _
        _ < η / 2 + η / 2 := add_lt_add h3 hx
        _ = η := by ring
    have ha2 : |a ^ 2 - μ ^ 2| ≤ δ / 5 := by
      rw [show a ^ 2 - μ ^ 2 = (a - μ) * ((a - μ) + 2 * μ) by ring, abs_mul]
      calc |a - μ| * |(a - μ) + 2 * μ| ≤ η * (2 * |μ| + 1) := by
            apply mul_le_mul had.le _ (abs_nonneg _) hηpos.le
            calc |(a - μ) + 2 * μ| ≤ |a - μ| + |2 * μ| := abs_add_le _ _
              _ ≤ 2 * |μ| + 1 := by rw [abs_mul, abs_two]; linarith
        _ ≤ δ / 5 := hημ
    have hκδ : κ ≤ δ / 5 := min_le_left _ _
    have hVσ : |b - a ^ 2 - σ ^ 2| < δ := by
      have e1 := abs_lt.1 h1
      have e3 := abs_lt.1 hy
      have e4 := abs_le.1 ha2
      rw [abs_lt]
      constructor <;> linarith
    have hle : |Real.sqrt (b - a ^ 2) - σ| * σ ≤ |b - a ^ 2 - σ ^ 2| := by
      conv_rhs => rw [← Real.sq_sqrt hV0]
      rw [show Real.sqrt (b - a ^ 2) ^ 2 - σ ^ 2 =
        (Real.sqrt (b - a ^ 2) - σ) * (Real.sqrt (b - a ^ 2) + σ) by ring, abs_mul]
      gcongr
      rw [abs_of_nonneg (by positivity)]
      linarith [Real.sqrt_nonneg (b - a ^ 2)]
    exact lt_asymm hI (lt_of_mul_lt_mul_right (lt_of_le_of_lt hle hVσ) hσ.le)
  have hcard : ((Finset.univ.filter fun I : Fin m → Fin (n + 1) =>
        ε < |Real.sqrt ((m : ℝ)⁻¹ * ∑ j, (x (I j) - (m : ℝ)⁻¹ * ∑ l, x (I l)) ^ 2) - σ|).card : ℝ)
      ≤ (E₁.card : ℝ) + E₂.card + E₃.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hE1 : (((n + 1 : ℕ) : ℝ) ^ m)⁻¹ * (E₁.card : ℝ) ≤ (K : ℝ) ^ 2 / (m * (δ / 5) ^ 2) := by
    refine (chebyshev hN hm (fun i : Fin (n + 1) => min (x i ^ 2) (K : ℝ)) (t := δ / 5)
      (by positivity)).trans ?_
    gcongr
    have hle : ∀ i : Fin (n + 1), min (x i ^ 2) (K : ℝ) ^ 2 ≤ (K : ℝ) ^ 2 := fun i =>
      pow_le_pow_left₀ (le_min (sq_nonneg _) (Nat.cast_nonneg K)) (min_le_right _ _) 2
    calc ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (n + 1), min (x i ^ 2) (K : ℝ) ^ 2
        ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (n + 1), (K : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hle i) (by positivity)
      _ = (K : ℝ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hE2 : (((n + 1 : ℕ) : ℝ) ^ m)⁻¹ * (E₂.card : ℝ) ≤ κ / (δ / 5) :=
    (markov hN hm (fun i : Fin (n + 1) => max (x i ^ 2 - K) 0) (fun i => le_max_right _ _)
      (t := δ / 5) (by positivity)).trans (by gcongr)
  have hE3 : (((n + 1 : ℕ) : ℝ) ^ m)⁻¹ * (E₃.card : ℝ) ≤ (τ + 1) / (m * (η / 2) ^ 2) :=
    (chebyshev hN hm (fun i : Fin (n + 1) => x i) (t := η / 2) (by positivity)).trans
      (by gcongr)
  have hκγ : κ / (δ / 5) ≤ γ / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have := min_le_right (δ / 5) (γ * δ / 10)
    linarith
  calc (((n + 1 : ℕ) : ℝ) ^ m)⁻¹ * _
      ≤ (((n + 1 : ℕ) : ℝ) ^ m)⁻¹ * ((E₁.card : ℝ) + E₂.card + E₃.card) := by gcongr
    _ = (((n + 1 : ℕ) : ℝ) ^ m)⁻¹ * E₁.card + (((n + 1 : ℕ) : ℝ) ^ m)⁻¹ * E₂.card +
        (((n + 1 : ℕ) : ℝ) ^ m)⁻¹ * E₃.card := by ring
    _ ≤ (K : ℝ) ^ 2 / (m * (δ / 5) ^ 2) + κ / (δ / 5) + (τ + 1) / (m * (η / 2) ^ 2) :=
        add_le_add (add_le_add hE1 hE2) hE3
    _ = A / m + κ / (δ / 5) := by
        rw [hA]
        field_simp
        ring
    _ ≤ γ / 2 + γ / 2 := add_le_add hAm hκγ
    _ = γ := by ring

-- The measurability hypothesis `hmeas` of the wanted statement is kept for fidelity; the proof
-- does not need it, since `IdentDistrib` already carries almost-everywhere measurability.
set_option linter.unusedVariables false in
/-- **Consistency of the bootstrap standard deviation** (P. J. Bickel and D. A. Freedman,
*Ann. Statist.* 9 (1981), Theorem 2.1(b)). Under the hypotheses of
`bootstrap_mean_tendsto_gaussianReal`, along almost every sample sequence the bootstrap standard
deviation `s*_m = ((1/m) ∑_j (X*_j - μ*_m)²)^{1/2}` converges to `σ` in conditional probability:
for every `ε > 0` the proportion of resampling maps `I : Fin m → Fin (n + 1)` with
`|s*_m - σ| > ε` tends to `0` as `n, m → ∞`. -/
theorem bootstrap_sd_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hL2 : MemLp (X 0) 2 P) {σsq : ℝ≥0} (hvar : variance (X 0) P = σsq) (hpos : 0 < σsq) :
    ∀ᵐ ω ∂P, ∀ ε > 0, Tendsto (fun nm : ℕ × ℕ =>
        (((nm.1 + 1 : ℕ) : ℝ) ^ nm.2)⁻¹ *
          ((Finset.univ.filter fun I : Fin nm.2 → Fin (nm.1 + 1) =>
            ε < |Real.sqrt ((nm.2 : ℝ)⁻¹ * ∑ j, (X (I j) ω -
              (nm.2 : ℝ)⁻¹ * ∑ l, X (I l) ω) ^ 2) - Real.sqrt σsq|).card : ℝ))
      (atTop ×ˢ atTop) (𝓝 0) := by
  -- The strong law for a measurable function of the observations, along the sample sizes `n + 1`.
  have slln : ∀ φ : ℝ → ℝ, Measurable φ → Integrable (fun ω => φ (X 0 ω)) P →
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), φ (X i ω))
        atTop (𝓝 (∫ ω, φ (X 0 ω) ∂P)) := by
    intro φ hφ hint
    have H := strong_law_ae_real (fun i ω => φ (X i ω)) hint
      (fun i j hij => (hindep.indepFun hij).comp hφ hφ) (fun i => (hident i).comp hφ)
    filter_upwards [H] with ω hω
    exact (hω.comp (tendsto_add_atTop_nat 1)).congr fun n => by
      simp only [Function.comp_apply, div_eq_inv_mul]
  have hint2 : Integrable (fun ω => X 0 ω ^ 2) P := hL2.integrable_sq
  have h1 := slln (fun x => x) measurable_id (hL2.integrable one_le_two)
  have h2 := slln (fun x => x ^ 2) (measurable_id.pow_const 2) hint2
  have h3 : ∀ᵐ ω ∂P, ∀ K : ℕ, Tendsto (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), max (X i ω ^ 2 - K) 0)
      atTop (𝓝 (∫ ω, max (X 0 ω ^ 2 - K) 0 ∂P)) :=
    ae_all_iff.2 fun K => slln (fun x => max (x ^ 2 - K) 0)
      (((measurable_id.pow_const 2).sub_const _).max measurable_const)
      (hint2.sub (integrable_const _)).pos_part
  -- The truncated second moments `E (X₀² - K)⁺` tend to zero, by dominated convergence.
  have htrunc : Tendsto (fun K : ℕ => ∫ ω, max (X 0 ω ^ 2 - K) 0 ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (fun ω => X 0 ω ^ 2)
      (F := fun (K : ℕ) ω => max (X 0 ω ^ 2 - K) 0) (f := fun _ => (0 : ℝ))
      (fun K => ((hint2.sub (integrable_const _)).pos_part).aestronglyMeasurable) hint2
      (fun K => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) K]) (sq_nonneg _))
      (ae_of_all _ fun ω => tendsto_const_nhds.congr' ?_)
    · simpa using this
    · filter_upwards [eventually_ge_atTop ⌈X 0 ω ^ 2⌉₊] with K hK
      rw [max_eq_right]
      linarith [Nat.ceil_le.1 hK]
  have hσ : 0 < Real.sqrt σsq := Real.sqrt_pos.2 (by exact_mod_cast hpos)
  have hmoment : Real.sqrt σsq ^ 2 + (∫ ω, X 0 ω ∂P) ^ 2 = ∫ ω, X 0 ω ^ 2 ∂P := by
    rw [Real.sq_sqrt (NNReal.coe_nonneg _), ← hvar, variance_eq_sub hL2]
    simp only [Pi.pow_apply, sub_add_cancel]
  filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
  intro ε hε
  refine tendsto_card_bad (x := fun i => X i ω) hσ hω1 (hmoment ▸ hω2) (fun κ hκ => ?_) hε
  obtain ⟨K, hK⟩ := (htrunc.eventually (gt_mem_nhds hκ)).exists
  exact ⟨K, (hω3 K).eventually (gt_mem_nhds hK)⟩

end MathlibExt.Probability.Statistics.BootstrapWanted
