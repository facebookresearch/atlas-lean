/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.HierarchicalCountMLE

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Uniqueness of the joint MLE for the Gamma–Poisson hierarchy at a common size factor

`MathlibExt.Biology.Omics.HierarchicalCountMLE` fits the hyperparameters `(a, b)` (prior shape and
rate) of the hierarchy `kᵢ ∣ λᵢ ~ Po(sᵢ λᵢ)`, `λᵢ ~ Gamma(a, b)` by maximizing the marginal
(negative binomial) log likelihood `ℓ(a, b) = logMarginalLik a b s k`. At a common size factor
`σ` it reduces the joint score equations to the rate root `b = σ a / M` and the profile shape
score `profileShapeScore a k = ∑ᵢ ∑_{j<kᵢ} 1 / (a + j) - n log (1 + M / a)`
(`score_eq_zero_iff_const`), and shows a root exists under overdispersion `0 < M < V`
(`exists_score_root_of_overdispersed`). This file proves that root unique and that it is the
unique joint MLE, and conversely that no joint MLE exists when `0 < M` and `V ≤ M`.

## Source

B. Levin and J. Reeds, *Compound multinomial likelihood functions are unimodal: proof of a
conjecture of I. J. Good*, Ann. Statist. 5 (1977), 79–87, **Theorem 2** (§3.1), specialized to one
negative binomial component per observation (`t = 1`, `λ₁ = τ₁ = 1`, `m = n` observations,
`N = ∑ᵢ kᵢ = n M`): *the likelihood `L(p, k)` has at most one local maximum, at
`p̂ = N / (N + m k̂)`; the maximum occurs for `k̂ < ∞` iff `∑ᵢ kᵢ (kᵢ - 1) > N² / m`.* In this
file's notation `k̂` is the shape `a`, the condition `∑ᵢ kᵢ (kᵢ - 1) > N² / m` is `M < V` (`V` the
biased sample variance `countVar`), and `p̂` corresponds to the rate root `b̂ = σ a / M`. This
answers Anscombe's question (1950, p. 367) on uniqueness of the negative binomial MLE.

What is proved here, at a common size factor `σ > 0` and `0 < M < V`:

* `profileShapeScore_neg_of_le`: the profile shape score crosses zero at most once, from above
  (Levin–Reeds's "at most one root" of the likelihood equation in `k`);
* `existsUnique_score_root`: the joint score equations have exactly one positive root;
* `logMarginalLik_lt_of_score_root`: that root is the strict global maximizer of `ℓ` on `(0, ∞)²`;
* `existsUnique_isMaxOn_logMarginalLik`: `ℓ` has exactly one maximizer on `(0, ∞)²` (the joint
  MLE exists and is unique), and `score_eq_zero_of_isMaxOn`: it solves the score equations.

Conversely, at a common size factor `σ > 0` and `0 < M`, `V ≤ M` (the "only if" half of
Theorem 2):

* `smoothedDiscrepancy_nonneg`: `H ≥ 0` on `[0, ∞)`, and `profileShapeScore_pos_of_le`: the
  profile shape score is positive at every `a > 0`, so `score_ne_zero_of_le`: the joint score
  equations have no positive root;
* `strictMonoOn_logMarginalLik_rateRoot`: `ℓ` strictly increases along `a ↦ (a, σ a / M)`;
* `not_exists_isMaxOn_logMarginalLik`: `ℓ` has no maximizer on `(0, ∞)²`.

The score equations themselves (T86) are the merged file's `hasDerivAt_logMarginalLik_shape`,
`hasDerivAt_logMarginalLik_rate` and `score_eq_zero_iff_const`; none are taken as hypotheses.

## Proof (Levin and Reeds)

Write `G` for the distribution function of unit masses at `0, …, kᵢ - 1` (over all `i`), `F` for
that of `n` times Lebesgue measure on `[0, M]`, and `H(u) = ∫₀ᵘ (G - F)`
(`smoothedDiscrepancy`, built from the ramp sums `rampSum`). Then

* the modification of Lemma 2.2 used in the proof of Theorem 2 (p. 85), `∫₀ᵘ G ≥ (u / 2) G(u)`
  (`rampSum_mul_sq_le`): `u ↦ ∫₀ᵘ G / u²` is antitone, so (Lemma 2.3,
  `smoothedDiscrepancy_neg_of_le`) once `H < 0` it stays negative: `H` has one sign change;
* `smoothedDiscrepancy_eq_of_ge`: past every count, `H(T) = n (M - V) / 2 < 0`;
* `profileShapeScore_eq_integral`: two integrations by parts give
  `profileShapeScore a k = H(T) / (a + T)² + 2 ∫₀ᵀ H(u) / (a + u)³ du`.

Levin and Reeds conclude by the variation-diminishing property of the Laplace transform. Here the
one-sign-change case is done directly: with `u*` the sign-change point of `H`, the kernel
`((a + u*) / (a + u))³` decreases in `a` where `H ≥ 0` and increases where `H ≤ 0`, so
`a ↦ (a + u*)³ · profileShapeScore a k` is strictly decreasing (strict from `H(T) < 0`).

For the converse, when `V ≤ M` a negative value of `H` would persist to `H(T) = n (M - V) / 2 ≥ 0`,
so `H ≥ 0`; near `0`, `H(u) ≥ u - n u² / 2 > 0` (some count is positive, as `0 < M`), so the
transform above is positive at every `a > 0`.

## Not proved here

* The all-zero sample `M = 0`, which also has `V ≤ M`: the converse here assumes `0 < M`, since
  the rate root `σ a / M` is undefined at `M = 0`.
* The limit of `ℓ` as `a → ∞` (the Poisson fit), and any statement that `ℓ` is maximized or
  bounded in that limit; the converse only shows that no finite point maximizes `ℓ`.
* Heterogeneous size factors. The reduction to one profile equation uses a common size factor;
  with distinct `sᵢ` the rate root is no longer `s̄ a / M` (tests), and uniqueness is not claimed.
* Levin and Reeds's Theorem 1 (compound multinomial) and Theorem 3 (Poisson mixtures), and their
  statement about higher derivatives of `log L`.

## References

* B. Levin and J. Reeds, *Compound multinomial likelihood functions are unimodal: proof of a
  conjecture of I. J. Good*, Ann. Statist. 5 (1977), 79–87.
* F. J. Anscombe, *Sampling theory of the negative binomial and logarithmic series
  distributions*, Biometrika 37 (1950), 358–382.
* J. Aragón, D. Eberly and S. Eberly, *Existence and uniqueness of the maximum likelihood
  estimator for the two-parameter negative binomial distribution*, Statist. Probab. Lett. 15
  (1992), 375–379.
-/

@[expose] public section

open Real Finset Set
open scoped Nat

namespace MathlibExt.Biology.Omics.HierarchicalCount

variable {ι : Type*} [Fintype ι]

/-! ### Ramp sums -/

/-- The ramp sum `R_k(u) = ∑_{h<k} max (u - h) 0`: the twice-integrated point masses of one count
`k`, one unit mass at each of `0, 1, …, k - 1` (Levin and Reeds's measure `G` for one
observation). -/
noncomputable def rampSum (k : ℕ) (u : ℝ) : ℝ := ∑ h ∈ range k, max (u - h) 0

private lemma sum_range_natCast (m : ℕ) : ∑ h ∈ range m, (h : ℝ) = m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

/-- Ramp sums are nonnegative. -/
theorem rampSum_nonneg (k : ℕ) (u : ℝ) : 0 ≤ rampSum k u :=
  sum_nonneg fun _ _ => le_max_right _ _

/-- Ramp sums are continuous. -/
theorem continuous_rampSum (k : ℕ) : Continuous (rampSum k) :=
  continuous_finsetSum _ fun _ _ => (continuous_id.sub continuous_const).max continuous_const

/-- Each partial line `m u - m (m - 1) / 2` (`m ≤ k`) is a lower bound of the ramp sum. -/
theorem le_rampSum {k m : ℕ} (hmk : m ≤ k) (u : ℝ) :
    m * u - m * (m - 1) / 2 ≤ rampSum k u := by
  calc m * u - m * (m - 1) / 2 = ∑ h ∈ range m, (u - h) := by
        rw [sum_sub_distrib, sum_range_natCast]; simp
    _ ≤ ∑ h ∈ range m, max (u - h) 0 := sum_le_sum fun _ _ => le_max_left _ _
    _ ≤ rampSum k u := sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hmk)
        fun _ _ _ => le_max_right _ _

/-- On the piece where exactly the masses `0, …, m - 1` lie below `u`, the ramp sum is the line
`m u - m (m - 1) / 2`. -/
theorem rampSum_eq {k m : ℕ} {u : ℝ} (hmk : m ≤ k) (hm : (m : ℝ) - 1 ≤ u)
    (hm' : m < k → u ≤ m) : rampSum k u = m * u - m * (m - 1) / 2 := by
  rw [rampSum, ← sum_range_add_sum_Ico _ hmk]
  have h1 : ∑ h ∈ range m, max (u - h) 0 = ∑ h ∈ range m, (u - h) :=
    sum_congr rfl fun h hh => by
      have : (h : ℝ) + 1 ≤ m := by exact_mod_cast mem_range.1 hh
      exact max_eq_left (by linarith)
  have h2 : ∑ h ∈ Ico m k, max (u - h) 0 = 0 :=
    sum_eq_zero fun h hh => by
      obtain ⟨hmh, hhk⟩ := mem_Ico.1 hh
      have hu := hm' (lt_of_le_of_lt hmh hhk)
      have : (m : ℝ) ≤ h := by exact_mod_cast hmh
      exact max_eq_right (by linarith)
  rw [h1, h2, add_zero, sum_sub_distrib, sum_range_natCast]
  simp

/-- The line inequality behind Levin and Reeds's modified Lemma 2.2 (proof of Theorem 2): on
`[m - 1, ∞)`, `u ↦ (m u - m (m - 1) / 2) / u²` is antitone. -/
private lemma line_mul_sq_le {m : ℕ} {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hmx : (m : ℝ) - 1 ≤ x) :
    x ^ 2 * (m * y - m * (m - 1) / 2) ≤ y ^ 2 * (m * x - m * (m - 1) / 2) := by
  have hm : (0 : ℝ) ≤ m := m.cast_nonneg
  have key : y ^ 2 * (m * x - m * (m - 1) / 2) - x ^ 2 * (m * y - m * (m - 1) / 2) =
      (y - x) * (m / 2 * (x * (y - (m - 1)) + y * (x - (m - 1)))) := by ring
  have : 0 ≤ (y - x) * (m / 2 * (x * (y - (m - 1)) + y * (x - (m - 1)))) := by
    refine mul_nonneg (by linarith) (mul_nonneg (by positivity) ?_)
    have : 0 ≤ x * (y - (m - 1)) := mul_nonneg hx.le (by linarith)
    have : 0 ≤ y * (x - (m - 1)) := mul_nonneg (by linarith) (by linarith)
    linarith
  linarith

private lemma rampSum_mul_sq_le_aux (k m : ℕ) :
    ∀ x y : ℝ, 0 < x → x ≤ y → m ≤ k → (m : ℝ) - 1 ≤ y →
      rampSum k y = m * y - m * (m - 1) / 2 → x ^ 2 * rampSum k y ≤ y ^ 2 * rampSum k x := by
  induction m with
  | zero =>
    intro x y _ _ _ _ hy
    rw [hy]; simp only [CharP.cast_eq_zero, zero_mul, sub_zero, zero_div, mul_zero]
    exact mul_nonneg (sq_nonneg _) (rampSum_nonneg _ _)
  | succ m ih =>
    intro x y hx hxy hmk hmy hy
    have hdirect : ∀ z : ℝ, 0 < z → z ≤ y → ((m + 1 : ℕ) : ℝ) - 1 ≤ z →
        z ^ 2 * rampSum k y ≤ y ^ 2 * rampSum k z := fun z hz hzy hmz => by
      rw [hy]
      exact (line_mul_sq_le hz hzy hmz).trans
        (mul_le_mul_of_nonneg_left (le_rampSum hmk z) (sq_nonneg _))
    rcases le_or_gt (((m + 1 : ℕ) : ℝ) - 1) x with hmx | hmx
    · exact hdirect x hx hxy hmx
    · push_cast at hmx
      have hz : (0 : ℝ) < m := by linarith
      have hzy : (m : ℝ) ≤ y := by push_cast at hmy; linarith
      have h1 := hdirect m hz hzy (by push_cast; linarith)
      have hRz : rampSum k m = m * m - m * (m - 1) / 2 :=
        rampSum_eq (by omega) (by linarith) fun _ => le_rfl
      have h2 := ih x m hx (by linarith) (by omega) (by linarith) hRz
      have hz2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
      have hR := rampSum_nonneg k y
      have hRm := rampSum_nonneg k (m : ℝ)
      have : (m : ℝ) ^ 2 * (x ^ 2 * rampSum k y) ≤ (m : ℝ) ^ 2 * (y ^ 2 * rampSum k x) :=
        calc (m : ℝ) ^ 2 * (x ^ 2 * rampSum k y) = x ^ 2 * ((m : ℝ) ^ 2 * rampSum k y) := by ring
          _ ≤ x ^ 2 * (y ^ 2 * rampSum k m) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
          _ = y ^ 2 * (x ^ 2 * rampSum k m) := by ring
          _ ≤ y ^ 2 * ((m : ℝ) ^ 2 * rampSum k x) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
          _ = (m : ℝ) ^ 2 * (y ^ 2 * rampSum k x) := by ring
      exact le_of_mul_le_mul_left this hz2

/-- **Levin and Reeds's modified Lemma 2.2, integrated form.** The proof of their Theorem 2
(§3.1, p. 85) uses `∫₀ᵘ G ≥ (u / 2) G(u)`, "a simple modification of Lemma 2.2" (whose eq. 2.4
concerns the convolved measure `G*`). Integrated: `u ↦ R_k(u) / u²` is antitone on
`(0, ∞)`: for `0 < x ≤ y`, `x² R_k(y) ≤ y² R_k(x)`. Equivalently `u G(u) ≤ 2 ∫₀ᵘ G` for the
distribution function `G` of the masses `0, …, k - 1`. -/
theorem rampSum_mul_sq_le (k : ℕ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    x ^ 2 * rampSum k y ≤ y ^ 2 * rampSum k x := by
  have hy : 0 ≤ y := hx.le.trans hxy
  set m := min ⌈y⌉₊ k
  have hmk : m ≤ k := min_le_right _ _
  have hmy : (m : ℝ) - 1 ≤ y := by
    have : (m : ℝ) ≤ ⌈y⌉₊ := by exact_mod_cast min_le_left _ _
    linarith [Nat.ceil_lt_add_one hy]
  have hm' : m < k → y ≤ m := fun h => by
    have : m = ⌈y⌉₊ := by
      rcases min_choice ⌈y⌉₊ k with h' | h'
      · exact h'
      · exact absurd h' (by omega)
    rw [this]; exact Nat.le_ceil y
  exact rampSum_mul_sq_le_aux k m x y hx hxy hmk hmy (rampSum_eq hmk hmy hm')

/-- The ramp sum grows at slope at most `k`. -/
theorem rampSum_sub_le (k : ℕ) {x y : ℝ} (hxy : x ≤ y) :
    rampSum k y - rampSum k x ≤ k * (y - x) := by
  rw [rampSum, rampSum, ← sum_sub_distrib]
  calc ∑ h ∈ range k, (max (y - h) 0 - max (x - h) 0) ≤ ∑ _h ∈ range k, (y - x) :=
        sum_le_sum fun h _ => by
          rcases le_total (x - h) 0 with h1 | h1 <;> rcases le_total (y - h) 0 with h2 | h2 <;>
            simp only [max_eq_left, max_eq_right, h1, h2] <;> linarith
    _ = k * (y - x) := by rw [sum_const, card_range, nsmul_eq_mul]

/-! ### Levin and Reeds's smoothed discrepancy -/

/-- **Levin and Reeds's function `H`.** For counts `k₁, …, kₙ` with sample mean `M`,
`H(u) = ∑ᵢ R_{kᵢ}(u) - n (u² / 2 - max (u - M) 0 ² / 2)` is `∫₀ᵘ (G - F)`, where `G` is the
distribution function of the unit masses at `0, …, kᵢ - 1` (over all `i`) and `F` that of `n`
times Lebesgue measure on `[0, M]`. The profile shape score is a Stieltjes-type transform of
`H` (`profileShapeScore_eq_integral`). -/
noncomputable def smoothedDiscrepancy (k : ι → ℕ) (u : ℝ) : ℝ :=
  ∑ i, rampSum (k i) u - Fintype.card ι * (u ^ 2 / 2 - max (u - countMean k) 0 ^ 2 / 2)

/-- `H` is continuous. -/
theorem continuous_smoothedDiscrepancy (k : ι → ℕ) : Continuous (smoothedDiscrepancy k) := by
  unfold smoothedDiscrepancy
  exact (continuous_finsetSum _ fun i _ => continuous_rampSum (k i)).sub (continuous_const.mul
    ((continuous_pow 2).div_const 2 |>.sub
      ((((continuous_id.sub continuous_const).max continuous_const).pow 2).div_const 2)))

private lemma sum_count_eq [Nonempty ι] (k : ι → ℕ) :
    ∑ i, (k i : ℝ) = Fintype.card ι * countMean k := by
  have : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [countMean]; field_simp

private lemma sum_count_sq_eq [Nonempty ι] (k : ι → ℕ) :
    ∑ i, (k i : ℝ) ^ 2 = Fintype.card ι * (countVar k + countMean k ^ 2) := by
  have : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [countVar]; field_simp; ring

private lemma countMean_nonneg (k : ι → ℕ) : 0 ≤ countMean k :=
  div_nonneg (sum_nonneg fun _ _ => by positivity) (by positivity)

/-- Below the sample mean, `F(u) = n u`, so `H(u) = ∑ᵢ R_{kᵢ}(u) - n u² / 2`. -/
theorem smoothedDiscrepancy_eq_of_le {k : ι → ℕ} {u : ℝ} (hu : u ≤ countMean k) :
    smoothedDiscrepancy k u = ∑ i, rampSum (k i) u - Fintype.card ι * (u ^ 2 / 2) := by
  rw [smoothedDiscrepancy, max_eq_right (by linarith)]
  ring

/-- `H` is antitone beyond the sample mean, where `F` has reached its total mass `n M`. -/
theorem smoothedDiscrepancy_anti [Nonempty ι] {k : ι → ℕ} {x y : ℝ} (hx : countMean k ≤ x)
    (hxy : x ≤ y) : smoothedDiscrepancy k y ≤ smoothedDiscrepancy k x := by
  have hR : ∑ i, rampSum (k i) y - ∑ i, rampSum (k i) x ≤ ∑ i, (k i : ℝ) * (y - x) := by
    rw [← sum_sub_distrib]; exact sum_le_sum fun i _ => rampSum_sub_le _ hxy
  rw [← sum_mul, sum_count_eq] at hR
  rw [smoothedDiscrepancy, smoothedDiscrepancy, max_eq_left (by linarith),
    max_eq_left (by linarith)]
  nlinarith

/-- **Levin and Reeds's Lemma 2.3: `H` changes sign at most once.** Once negative at some
`u₀ ≥ 0`, `H` stays negative on `[u₀, ∞)`. -/
theorem smoothedDiscrepancy_neg_of_le [Nonempty ι] {k : ι → ℕ} {u₀ u : ℝ} (hu₀ : 0 ≤ u₀)
    (h₀ : smoothedDiscrepancy k u₀ < 0) (hu : u₀ ≤ u) : smoothedDiscrepancy k u < 0 := by
  set M := countMean k
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  -- on `(0, M]`, `H(u) / u²` is antitone
  have hlow : ∀ x y, 0 ≤ x → smoothedDiscrepancy k x < 0 → x ≤ y → y ≤ M →
      smoothedDiscrepancy k y < 0 := fun x y hx hxneg hxy hyM => by
    have hxM : x ≤ M := hxy.trans hyM
    rw [smoothedDiscrepancy_eq_of_le hxM] at hxneg
    rw [smoothedDiscrepancy_eq_of_le hyM]
    have hx0 : 0 < x := by
      rcases hx.lt_or_eq with h | h
      · exact h
      · subst h
        have : ∑ i, rampSum (k i) 0 = 0 :=
          sum_eq_zero fun i _ => sum_eq_zero fun h _ => max_eq_right (by simp)
        rw [this] at hxneg; simp at hxneg
    have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
    have hmono : x ^ 2 * ∑ i, rampSum (k i) y ≤ y ^ 2 * ∑ i, rampSum (k i) x := by
      rw [mul_sum, mul_sum]; exact sum_le_sum fun i _ => rampSum_mul_sq_le _ hx0 hxy
    have hxy2 : 0 < x ^ 2 := by positivity
    by_contra hc
    push Not at hc
    have hy2 : 0 < y ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left (show Fintype.card ι * (y ^ 2 / 2) ≤
      ∑ i, rampSum (k i) y by linarith) hxy2.le
    have h2 := mul_lt_mul_of_pos_left (show ∑ i, rampSum (k i) x <
      Fintype.card ι * (x ^ 2 / 2) by linarith) hy2
    nlinarith
  rcases le_total u M with huM | hMu
  · exact hlow u₀ u hu₀ h₀ hu huM
  · rcases le_total u₀ M with hu₀M | hMu₀
    · exact lt_of_le_of_lt (smoothedDiscrepancy_anti le_rfl hMu)
        (hlow u₀ M hu₀ h₀ hu₀M le_rfl)
    · exact lt_of_le_of_lt (smoothedDiscrepancy_anti hMu₀ hu) h₀

/-- **The terminal value of `H` is the overdispersion.** Beyond every count and the sample mean,
`H(T) = n (M - V) / 2`, with `V` the biased sample variance. -/
theorem smoothedDiscrepancy_eq_of_ge [Nonempty ι] {k : ι → ℕ} {T : ℝ} (hTM : countMean k ≤ T)
    (hTk : ∀ i, (k i : ℝ) ≤ T) :
    smoothedDiscrepancy k T = Fintype.card ι * (countMean k - countVar k) / 2 := by
  have hR : ∀ i, rampSum (k i) T = k i * T - k i * (k i - 1) / 2 := fun i =>
    rampSum_eq le_rfl (by linarith [hTk i]) fun h => absurd h (lt_irrefl _)
  have hA := sum_count_eq k
  have hB := sum_count_sq_eq k
  have hsum : ∑ i, rampSum (k i) T = (∑ i, (k i : ℝ)) * T - (∑ i, (k i : ℝ) ^ 2) / 2 +
      (∑ i, (k i : ℝ)) / 2 := by
    rw [sum_congr rfl fun i _ => hR i, sum_mul, sum_div, sum_div, ← sum_sub_distrib,
      ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [smoothedDiscrepancy, max_eq_left (by linarith), hsum, hA, hB]
  ring

/-! ### The profile shape score as a transform of `H` -/

private lemma intervalIntegrable_div_cube {f : ℝ → ℝ} (hf : Continuous f) {a T : ℝ} (ha : 0 < a)
    (hT : 0 ≤ T) : IntervalIntegrable (fun u => f u / (a + u) ^ 3) MeasureTheory.volume 0 T := by
  refine ContinuousOn.intervalIntegrable (hf.continuousOn.div (by fun_prop) fun u hu => ?_)
  rw [uIcc_of_le hT] at hu
  have := hu.1
  positivity

private lemma intervalIntegrable_div_cube' {f : ℝ → ℝ} (hf : Continuous f) {a x y : ℝ}
    (ha : 0 < a) (hx : 0 ≤ x) (hxy : x ≤ y) :
    IntervalIntegrable (fun u => f u / (a + u) ^ 3) MeasureTheory.volume x y := by
  refine ContinuousOn.intervalIntegrable (hf.continuousOn.div (by fun_prop) fun u hu => ?_)
  rw [uIcc_of_le hxy] at hu
  have := hx.trans hu.1
  positivity

private lemma hasDerivAt_inv_add {a u : ℝ} (hau : 0 < a + u) :
    HasDerivAt (fun u => (a + u)⁻¹) (-((a + u) ^ 2)⁻¹) u := by
  have h := ((hasDerivAt_id u).const_add a).inv hau.ne'
  refine h.congr_deriv ?_
  simp only [id]
  field_simp

private lemma hasDerivAt_inv_add_sq {a u : ℝ} (hau : 0 < a + u) :
    HasDerivAt (fun u => ((a + u) ^ 2)⁻¹) (-2 * ((a + u) ^ 3)⁻¹) u := by
  have h := (((hasDerivAt_id u).const_add a).pow 2).inv
    (by simp only [Pi.pow_apply, id]; positivity)
  refine h.congr_deriv ?_
  simp only [id, Pi.pow_apply]
  field_simp
  ring

/-- **Transform of one ramp.** For `0 ≤ h ≤ T` and `a > 0`,
`R(T) / (a + T)² + 2 ∫₀ᵀ R(u) / (a + u)³ du = 1 / (a + h) - 1 / (a + T)` for `R(u) = max (u - h) 0`:
two integrations by parts of `∫ 1 / (a + u) d δ_h` on `[0, T]`. -/
theorem ramp_transform {a h T : ℝ} (ha : 0 < a) (hh : 0 ≤ h) (hhT : h ≤ T) :
    max (T - h) 0 / (a + T) ^ 2 + 2 * ∫ u in (0 : ℝ)..T, max (u - h) 0 / (a + u) ^ 3 =
      (a + h)⁻¹ - (a + T)⁻¹ := by
  have hc : Continuous fun u : ℝ => max (u - h) 0 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_div_cube hc ha hh) (intervalIntegrable_div_cube' hc ha hh hhT)]
  have h0 : ∫ u in (0 : ℝ)..h, max (u - h) 0 / (a + u) ^ 3 = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => by
      rw [uIcc_of_le hh] at hu
      simp only [max_eq_right (by linarith [hu.2] : u - h ≤ 0), zero_div]]
    simp
  have hF : ∀ u ∈ uIcc h T, HasDerivAt (fun u => -(a + u)⁻¹ + (a + h) / 2 * ((a + u) ^ 2)⁻¹)
      ((u - h) / (a + u) ^ 3) u := fun u hu => by
    rw [uIcc_of_le hhT] at hu
    have hau : 0 < a + u := by linarith [hu.1]
    have := (hasDerivAt_inv_add hau).neg.add ((hasDerivAt_inv_add_sq hau).const_mul ((a + h) / 2))
    refine this.congr_deriv ?_
    field_simp
    ring
  have h1 : ∫ u in h..T, max (u - h) 0 / (a + u) ^ 3 = ∫ u in h..T, (u - h) / (a + u) ^ 3 :=
    intervalIntegral.integral_congr fun u hu => by
      rw [uIcc_of_le hhT] at hu
      simp only [max_eq_left (by linarith [hu.1] : 0 ≤ u - h)]
  rw [h0, h1, intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (intervalIntegrable_div_cube' (by fun_prop : Continuous fun u : ℝ => u - h) ha hh hhT),
    max_eq_left (by linarith)]
  have : 0 < a + h := by linarith
  have : 0 < a + T := by linarith
  field_simp
  ring

/-- The part of `H` coming from `F` (`n` times Lebesgue measure on `[0, M]`), per unit of `n`. -/
private noncomputable def quadPart (M u : ℝ) : ℝ := u ^ 2 / 2 - max (u - M) 0 ^ 2 / 2

private lemma continuous_quadPart (M : ℝ) : Continuous (quadPart M) := by
  unfold quadPart; fun_prop

/-- **Transform of the uniform part.** For `0 ≤ M ≤ T` and `a > 0`, with
`Q(u) = u² / 2 - max (u - M) 0 ² / 2`,
`Q(T) / (a + T)² + 2 ∫₀ᵀ Q(u) / (a + u)³ du = log (a + M) - log a - M / (a + T)`. -/
private lemma quadPart_transform {a M T : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (hMT : M ≤ T) :
    quadPart M T / (a + T) ^ 2 + 2 * ∫ u in (0 : ℝ)..T, quadPart M u / (a + u) ^ 3 =
      log (a + M) - log a - M / (a + T) := by
  have hc := continuous_quadPart M
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_div_cube hc ha hM) (intervalIntegrable_div_cube' hc ha hM hMT)]
  have e1 : ∫ u in (0 : ℝ)..M, quadPart M u / (a + u) ^ 3 =
      ∫ u in (0 : ℝ)..M, u ^ 2 / 2 / (a + u) ^ 3 :=
    intervalIntegral.integral_congr fun u hu => by
      rw [uIcc_of_le hM] at hu
      simp only [quadPart, max_eq_right (by linarith [hu.2] : u - M ≤ 0)]
      ring
  have e2 : ∫ u in M..T, quadPart M u / (a + u) ^ 3 =
      ∫ u in M..T, (M * u - M ^ 2 / 2) / (a + u) ^ 3 :=
    intervalIntegral.integral_congr fun u hu => by
      rw [uIcc_of_le hMT] at hu
      simp only [quadPart, max_eq_left (by linarith [hu.1] : 0 ≤ u - M)]
      ring
  have hF1 : ∀ u ∈ uIcc 0 M, HasDerivAt
      (fun u => (log (a + u) + 2 * a * (a + u)⁻¹ - a ^ 2 / 2 * ((a + u) ^ 2)⁻¹) / 2)
      (u ^ 2 / 2 / (a + u) ^ 3) u := fun u hu => by
    rw [uIcc_of_le hM] at hu
    have hau : 0 < a + u := by linarith [hu.1]
    have hl := ((hasDerivAt_id u).const_add a).log hau.ne'
    have := ((hl.add ((hasDerivAt_inv_add hau).const_mul (2 * a))).sub
      ((hasDerivAt_inv_add_sq hau).const_mul (a ^ 2 / 2))).div_const 2
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hF2 : ∀ u ∈ uIcc M T, HasDerivAt
      (fun u => -M * (a + u)⁻¹ + (a * M + M ^ 2 / 2) / 2 * ((a + u) ^ 2)⁻¹)
      ((M * u - M ^ 2 / 2) / (a + u) ^ 3) u := fun u hu => by
    rw [uIcc_of_le hMT] at hu
    have hau : 0 < a + u := by linarith [hu.1]
    have := ((hasDerivAt_inv_add hau).const_mul (-M)).add
      ((hasDerivAt_inv_add_sq hau).const_mul ((a * M + M ^ 2 / 2) / 2))
    refine this.congr_deriv ?_
    field_simp
    ring
  rw [e1, e2, intervalIntegral.integral_eq_sub_of_hasDerivAt hF1
      (intervalIntegrable_div_cube (by fun_prop : Continuous fun u : ℝ => u ^ 2 / 2) ha hM),
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF2
      (intervalIntegrable_div_cube' (by fun_prop : Continuous fun u : ℝ => M * u - M ^ 2 / 2)
        ha hM hMT),
    quadPart, max_eq_left (by linarith : 0 ≤ T - M)]
  have : 0 < a + M := by linarith
  have : 0 < a + T := by linarith
  simp only [add_zero]
  field_simp
  ring

/-- **The profile shape score is a transform of `H`** (Levin and Reeds 1977, §3.1). For `a > 0`
and any `T` at least the sample mean and every count,
`profileShapeScore a k = H(T) / (a + T)² + 2 ∫₀ᵀ H(u) / (a + u)³ du`. -/
theorem profileShapeScore_eq_integral [Nonempty ι] {k : ι → ℕ} {a T : ℝ} (ha : 0 < a)
    (hTM : countMean k ≤ T) (hTk : ∀ i, (k i : ℝ) ≤ T) :
    profileShapeScore a k = smoothedDiscrepancy k T / (a + T) ^ 2 +
      2 * ∫ u in (0 : ℝ)..T, smoothedDiscrepancy k u / (a + u) ^ 3 := by
  set M := countMean k
  have hM := countMean_nonneg k
  have hT : 0 ≤ T := hM.trans hTM
  set n : ℝ := (Fintype.card ι : ℝ)
  have hcont : ∀ h : ℕ, ContinuousOn (fun u : ℝ => max (u - h) 0 / (a + u) ^ 3) (uIcc 0 T) :=
    fun h => (Continuous.continuousOn (by fun_prop)).div (by fun_prop) fun u hu => by
      rw [uIcc_of_le hT] at hu
      have := hu.1
      positivity
  have hramp : ∀ h : ℕ, IntervalIntegrable (fun u : ℝ => max (u - h) 0 / (a + u) ^ 3)
      MeasureTheory.volume 0 T := fun h => (hcont h).intervalIntegrable
  have hint : ∫ u in (0 : ℝ)..T, smoothedDiscrepancy k u / (a + u) ^ 3 =
      ∑ i, ∑ h ∈ range (k i), (∫ u in (0 : ℝ)..T, max (u - h) 0 / (a + u) ^ 3) -
        n * ∫ u in (0 : ℝ)..T, quadPart M u / (a + u) ^ 3 := by
    have e : (fun u => smoothedDiscrepancy k u / (a + u) ^ 3) = fun u : ℝ =>
        ∑ i, ∑ h ∈ range (k i), max (u - (h : ℝ)) 0 / (a + u) ^ 3 -
          n * (quadPart M u / (a + u) ^ 3) := by
      funext u
      simp only [smoothedDiscrepancy, rampSum, quadPart, sub_div, sum_div, mul_div_assoc]
      rfl
    rw [e, intervalIntegral.integral_sub, intervalIntegral.integral_finsetSum,
      intervalIntegral.integral_const_mul]
    · congr 1
      exact sum_congr rfl fun i _ =>
        intervalIntegral.integral_finsetSum fun h _ => hramp h
    · exact fun i _ => (continuousOn_finsetSum _ fun h _ => hcont h).intervalIntegrable
    · exact (continuousOn_finsetSum _ fun i _ =>
        continuousOn_finsetSum _ fun h _ => hcont h).intervalIntegrable
    · exact (intervalIntegrable_div_cube (continuous_quadPart M) ha hT).const_mul n
  have hTe : smoothedDiscrepancy k T / (a + T) ^ 2 =
      ∑ i, ∑ h ∈ range (k i), max (T - h) 0 / (a + T) ^ 2 - n * (quadPart M T / (a + T) ^ 2) := by
    simp only [smoothedDiscrepancy, rampSum, quadPart, sub_div, sum_div, mul_div_assoc]
    rfl
  have hkey : ∀ i, ∀ h ∈ range (k i), max (T - h) 0 / (a + T) ^ 2 +
      2 * ∫ u in (0 : ℝ)..T, max (u - h) 0 / (a + u) ^ 3 = (a + h)⁻¹ - (a + T)⁻¹ :=
    fun i h hh => ramp_transform ha h.cast_nonneg (by
      have : (h : ℝ) + 1 ≤ k i := by exact_mod_cast mem_range.1 hh
      linarith [hTk i])
  rw [hTe, hint]
  have hre : ∑ i, ∑ h ∈ range (k i), max (T - h) 0 / (a + T) ^ 2 -
      n * (quadPart M T / (a + T) ^ 2) + 2 * (∑ i, ∑ h ∈ range (k i),
        (∫ u in (0 : ℝ)..T, max (u - h) 0 / (a + u) ^ 3) -
          n * ∫ u in (0 : ℝ)..T, quadPart M u / (a + u) ^ 3) =
      ∑ i, ∑ h ∈ range (k i), (max (T - h) 0 / (a + T) ^ 2 +
        2 * ∫ u in (0 : ℝ)..T, max (u - h) 0 / (a + u) ^ 3) -
      n * (quadPart M T / (a + T) ^ 2 +
        2 * ∫ u in (0 : ℝ)..T, quadPart M u / (a + u) ^ 3) := by
    simp only [sum_add_distrib, mul_sum, mul_sub, mul_add]
    ring
  rw [hre, sum_congr rfl fun i _ => sum_congr rfl (hkey i), quadPart_transform ha hM hTM]
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  rw [← sum_mul, sum_count_eq, profileShapeScore]
  simp only [digammaIncrement]
  have : 0 < a + T := by linarith
  field_simp
  ring

/-! ### Single crossing of the profile shape score -/

private lemma boundary_factor_lt {a a' u T : ℝ} (ha : 0 < a) (haa' : a < a') (hu : 0 ≤ u)
    (huT : u ≤ T) : (a + u) ^ 3 / (a + T) ^ 2 < (a' + u) ^ 3 / (a' + T) ^ 2 := by
  have ha' : 0 < a' := ha.trans haa'
  have hT : 0 ≤ T := hu.trans huT
  have hp : 0 < a + u := by linarith
  have hq : 0 < a + T := by linarith
  have h1 : (a + u) * (a' + T) ≤ (a' + u) * (a + T) := by nlinarith
  have h2 : ((a + u) * (a' + T)) ^ 2 ≤ ((a' + u) * (a + T)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have h3 : (a + u) * ((a' + u) * (a + T)) ^ 2 < (a' + u) * ((a' + u) * (a + T)) ^ 2 :=
    mul_lt_mul_of_pos_right (by linarith) (by positivity)
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hp.le]

private lemma ratio_le_of_le {a a' u v : ℝ} (ha : 0 < a) (haa' : a < a') (hu : 0 ≤ u)
    (hv : 0 ≤ v) (huv : u ≤ v) : (a' + v) ^ 3 / (a' + u) ^ 3 ≤ (a + v) ^ 3 / (a + u) ^ 3 := by
  have ha' : 0 < a' := ha.trans haa'
  rw [← div_pow, ← div_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ 3
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Single crossing (Levin and Reeds 1977, Theorem 2).** At an overdispersed sample
(`0 < M < V`), once the profile shape score is `≤ 0` at some `a > 0`, it is `< 0` at every larger
shape. The proof writes the score as `H(T) / (a + T)² + 2 ∫₀ᵀ H(u) / (a + u)³ du`
(`profileShapeScore_eq_integral`), uses the single sign change of `H` at `u*`
(`smoothedDiscrepancy_neg_of_le`), and shows `a ↦ (a + u*)³ · profileShapeScore a k` strictly
decreasing: the kernel `((a + u*) / (a + u))³` is decreasing in `a` where `H ≥ 0` (`u ≤ u*`) and
increasing where `H ≤ 0`, and `H(T) = n (M - V) / 2 < 0` makes the boundary term strict. -/
theorem profileShapeScore_neg_of_le [Nonempty ι] {k : ι → ℕ} (hMV : countMean k < countVar k)
    {a a' : ℝ} (ha : 0 < a) (haa' : a < a') (h : profileShapeScore a k ≤ 0) :
    profileShapeScore a' k < 0 := by
  have ha' : 0 < a' := ha.trans haa'
  set T : ℝ := countMean k + ∑ i, (k i : ℝ)
  have hM := countMean_nonneg k
  have hTM : countMean k ≤ T := by
    have : 0 ≤ ∑ i, (k i : ℝ) := sum_nonneg fun _ _ => by positivity
    linarith
  have hTk : ∀ i, (k i : ℝ) ≤ T := fun i => by
    have := single_le_sum (f := fun i => (k i : ℝ)) (fun _ _ => by positivity) (mem_univ i)
    linarith
  have hT : 0 ≤ T := hM.trans hTM
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hHT : smoothedDiscrepancy k T < 0 := by
    rw [smoothedDiscrepancy_eq_of_ge hTM hTk]
    have : 0 < (Fintype.card ι : ℝ) * (countVar k - countMean k) := mul_pos hn (by linarith)
    linarith
  -- the sign-change point `u*`
  set S := {u : ℝ | 0 ≤ u ∧ u ≤ T ∧ smoothedDiscrepancy k u < 0}
  have hS : S.Nonempty := ⟨T, hT, le_rfl, hHT⟩
  have hSb : BddBelow S := ⟨0, fun u hu => hu.1⟩
  set us := sInf S
  have hus0 : 0 ≤ us := le_csInf hS fun u hu => hu.1
  have husT : us ≤ T := csInf_le hSb ⟨hT, le_rfl, hHT⟩
  have hsign : ∀ u, 0 ≤ u → u ≤ T → (0 ≤ smoothedDiscrepancy k u → u ≤ us) ∧
      (smoothedDiscrepancy k u < 0 → us ≤ u) := fun u hu huT => by
    refine ⟨fun hpos => ?_, fun hneg => csInf_le hSb ⟨hu, huT, hneg⟩⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨s, hsS, hsu⟩ := exists_lt_of_csInf_lt hS hlt
    exact absurd hpos (not_le.2 (smoothedDiscrepancy_neg_of_le hsS.1 hsS.2.2 hsu.le))
  -- pointwise comparison of the integrands
  have hmono : ∀ u ∈ Icc (0 : ℝ) T,
      smoothedDiscrepancy k u * ((a' + us) ^ 3 / (a' + u) ^ 3) ≤
        smoothedDiscrepancy k u * ((a + us) ^ 3 / (a + u) ^ 3) := fun u hu => by
    rcases le_or_gt 0 (smoothedDiscrepancy k u) with hpos | hneg
    · exact mul_le_mul_of_nonneg_left
        (ratio_le_of_le ha haa' hu.1 hus0 ((hsign u hu.1 hu.2).1 hpos)) hpos
    · have h1 : (a + us) ^ 3 / (a + u) ^ 3 ≤ (a' + us) ^ 3 / (a' + u) ^ 3 := by
        have hu' := (hsign u hu.1 hu.2).2 hneg
        have e1 := ratio_le_of_le ha haa' hus0 hu.1 hu'
        have hp : ∀ x : ℝ, 0 < x → (x + us) ^ 3 / (x + u) ^ 3 = ((x + u) ^ 3 / (x + us) ^ 3)⁻¹ :=
          fun x _ => (inv_div _ _).symm
        rw [hp a ha, hp a' (ha.trans haa')]
        exact inv_anti₀ (by have := hu.1; positivity) e1
      exact mul_le_mul_of_nonpos_left h1 hneg.le
  have hcont : ∀ x : ℝ, 0 < x → IntervalIntegrable
      (fun u => smoothedDiscrepancy k u * ((x + us) ^ 3 / (x + u) ^ 3))
        MeasureTheory.volume 0 T := fun x hx => by
    refine ContinuousOn.intervalIntegrable ((continuous_smoothedDiscrepancy k).continuousOn.mul
      (continuousOn_const.div (by fun_prop) fun u hu => ?_))
    rw [uIcc_of_le hT] at hu
    have := hu.1
    positivity
  have hrep : ∀ x : ℝ, 0 < x → (x + us) ^ 3 * profileShapeScore x k =
      smoothedDiscrepancy k T * ((x + us) ^ 3 / (x + T) ^ 2) +
        2 * ∫ u in (0 : ℝ)..T, smoothedDiscrepancy k u * ((x + us) ^ 3 / (x + u) ^ 3) :=
      fun x hx => by
    have hi : ∫ u in (0 : ℝ)..T, smoothedDiscrepancy k u * ((x + us) ^ 3 / (x + u) ^ 3) =
        (x + us) ^ 3 * ∫ u in (0 : ℝ)..T, smoothedDiscrepancy k u / (x + u) ^ 3 := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun u _ => by ring
    rw [profileShapeScore_eq_integral hx hTM hTk, hi]
    ring
  have hint := intervalIntegral.integral_mono_on hT (hcont a' (ha.trans haa')) (hcont a ha) hmono
  have hbd := mul_lt_mul_of_neg_left (boundary_factor_lt ha haa' hus0 husT) hHT
  have key : (a' + us) ^ 3 * profileShapeScore a' k < (a + us) ^ 3 * profileShapeScore a k := by
    rw [hrep a' (ha.trans haa'), hrep a ha]; linarith
  have hpos : 0 < (a' + us) ^ 3 := by have := ha.trans haa'; positivity
  have : (a + us) ^ 3 * profileShapeScore a k ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) h
  by_contra hc
  push Not at hc
  linarith [mul_nonneg hpos.le hc]

/-- **At most one root of the profile shape score** at an overdispersed sample. -/
theorem profileShapeScore_eq_zero_unique [Nonempty ι] {k : ι → ℕ}
    (hMV : countMean k < countVar k) {a a' : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (h : profileShapeScore a k = 0) (h' : profileShapeScore a' k = 0) : a = a' := by
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · exact absurd h' (profileShapeScore_neg_of_le hMV ha hlt h.le).ne
  · exact heq
  · exact absurd h (profileShapeScore_neg_of_le hMV ha' hgt h'.le).ne

/-- Left of a root the profile shape score is positive. -/
theorem profileShapeScore_pos_of_lt [Nonempty ι] {k : ι → ℕ} (hMV : countMean k < countVar k)
    {a ahat : ℝ} (ha : 0 < a) (hlt : a < ahat) (h : profileShapeScore ahat k = 0) :
    0 < profileShapeScore a k := by
  by_contra hc
  exact (profileShapeScore_neg_of_le hMV ha hlt (not_lt.1 hc)).ne h

/-- Right of a root the profile shape score is negative. -/
theorem profileShapeScore_neg_of_gt [Nonempty ι] {k : ι → ℕ} (hMV : countMean k < countVar k)
    {a ahat : ℝ} (hahat : 0 < ahat) (hlt : ahat < a) (h : profileShapeScore ahat k = 0) :
    profileShapeScore a k < 0 :=
  profileShapeScore_neg_of_le hMV hahat hlt h.le

/-! ### Uniqueness of the joint score root -/

/-- **The joint score equations have at most one positive root** at a common size factor
`σ > 0` and an overdispersed sample. -/
theorem score_root_unique [Nonempty ι] {σ : ℝ} (hσ : 0 < σ) {k : ι → ℕ}
    (hM : 0 < countMean k) (hMV : countMean k < countVar k) {a b a' b' : ℝ} (ha : 0 < a)
    (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b')
    (h : shapeScore a b (fun _ => σ) k = 0 ∧ rateScore a b (fun _ => σ) k = 0)
    (h' : shapeScore a' b' (fun _ => σ) k = 0 ∧ rateScore a' b' (fun _ => σ) k = 0) :
    a = a' ∧ b = b' := by
  obtain ⟨rfl, hP⟩ := (score_eq_zero_iff_const ha hb hσ hM).1 h
  obtain ⟨rfl, hP'⟩ := (score_eq_zero_iff_const ha' hb' hσ hM).1 h'
  obtain rfl := profileShapeScore_eq_zero_unique hMV ha ha' hP hP'
  exact ⟨rfl, rfl⟩

/-- **Existence and uniqueness of the joint score root** (Anscombe's question, answered by
Levin and Reeds 1977, Theorem 2): at a common size factor `σ > 0` and an overdispersed sample
`0 < M < V`, the joint score equations have exactly one positive solution. -/
theorem existsUnique_score_root [Nonempty ι] {σ : ℝ} (hσ : 0 < σ) {k : ι → ℕ}
    (hM : 0 < countMean k) (hMV : countMean k < countVar k) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ shapeScore p.1 p.2 (fun _ => σ) k = 0 ∧
      rateScore p.1 p.2 (fun _ => σ) k = 0 := by
  obtain ⟨a, b, ha, hb, hs, hr⟩ := exists_score_root_of_overdispersed hσ hM hMV
  refine ⟨(a, b), ⟨ha, hb, hs, hr⟩, fun q hq => ?_⟩
  obtain ⟨h1, h2⟩ := score_root_unique hσ hM hMV hq.1 hq.2.1 ha hb ⟨hq.2.2.1, hq.2.2.2⟩ ⟨hs, hr⟩
  exact Prod.ext h1 h2

/-! ### The profile likelihood and the joint MLE -/

/-- The profile log likelihood of the shape at a common size factor, up to an additive constant:
`∑ᵢ ∑_{j<kᵢ} log (a + j) + n (a log a - (a + M) log (a + M))`, the value of
`ℓ(a, σ a / M) - ∑ᵢ (kᵢ log M - log kᵢ!)` (`logMarginalLik_rateRoot`). -/
noncomputable def profileLogLik (a : ℝ) (k : ι → ℕ) : ℝ :=
  ∑ i, ∑ j ∈ range (k i), log (a + j) +
    Fintype.card ι * (a * log a - (a + countMean k) * log (a + countMean k))

/-- Along the rate root `b̂(a) = σ a / M`, the log marginal likelihood is the profile log
likelihood plus a constant. -/
theorem logMarginalLik_rateRoot [Nonempty ι] {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) {k : ι → ℕ}
    (hM : 0 < countMean k) :
    logMarginalLik a (σ * a / countMean k) (fun _ => σ) k =
      profileLogLik a k + ∑ i, ((k i : ℝ) * log (countMean k) - log ((k i)! : ℝ)) := by
  set M := countMean k
  have hb : 0 < σ * a / M := by positivity
  rw [logMarginalLik_eq ha hb (fun _ => hσ)]
  have hl1 : log (σ * a / M) = log σ + log a - log M := by
    rw [log_div (by positivity) hM.ne', log_mul hσ.ne' ha.ne']
  have hl2 : log (σ * a / M + σ) = log σ + log (a + M) - log M := by
    have : σ * a / M + σ = σ * (a + M) / M := by field_simp
    rw [this, log_div (by positivity) hM.ne', log_mul hσ.ne' (by positivity)]
  have hterm : ∀ i, ∑ j ∈ range (k i), log (a + j) + k i * log σ - log ((k i)! : ℝ) +
      a * log (σ * a / M) - (a + k i) * log (σ * a / M + σ) =
      ∑ j ∈ range (k i), log (a + j) + ((k i : ℝ) * log M - log ((k i)! : ℝ)) +
        (a * log a - (a + k i) * log (a + M)) := fun i => by
    rw [hl1, hl2]; ring
  rw [sum_congr rfl fun i _ => hterm i, sum_add_distrib, sum_add_distrib, profileLogLik]
  have hA : ∑ i, (k i : ℝ) = Fintype.card ι * M := sum_count_eq k
  have : ∑ i, (a * log a - (a + k i) * log (a + M)) =
      Fintype.card ι * (a * log a - (a + M) * log (a + M)) := by
    rw [sum_sub_distrib, ← sum_mul, ← sum_mul, sum_add_distrib, hA]
    simp only [sum_const, card_univ, nsmul_eq_mul]
    ring
  rw [this]; ring

/-- The profile log likelihood has derivative the profile shape score. -/
theorem hasDerivAt_profileLogLik {a : ℝ} (ha : 0 < a) {k : ι → ℕ} (hM : 0 ≤ countMean k) :
    HasDerivAt (fun x => profileLogLik x k) (profileShapeScore a k) a := by
  have haM : 0 < a + countMean k := by linarith
  have h1 : HasDerivAt (fun x => ∑ i, ∑ j ∈ range (k i), log (x + j))
      (∑ i, digammaIncrement a (k i)) a := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    rw [digammaIncrement]
    refine HasDerivAt.fun_sum fun j _ => ?_
    have h := ((hasDerivAt_id a).add_const (j : ℝ)).log (by simp only [id]; positivity)
    simpa [one_div] using h
  have h2 := (hasDerivAt_id a).mul ((hasDerivAt_id a).log ha.ne')
  have h3 := ((hasDerivAt_id a).add_const (countMean k)).mul
    (((hasDerivAt_id a).add_const (countMean k)).log (by simp only [id]; positivity))
  have := h1.add ((h2.sub h3).const_mul (Fintype.card ι : ℝ))
  refine this.congr_deriv ?_
  simp only [id, profileShapeScore]
  field_simp
  ring

/-- **The joint score root is the strict global maximizer** of the log marginal likelihood over
`(0, ∞)²`, at a common size factor `σ > 0` and an overdispersed sample. -/
theorem logMarginalLik_lt_of_score_root [Nonempty ι] {σ : ℝ} (hσ : 0 < σ) {k : ι → ℕ}
    (hM : 0 < countMean k) (hMV : countMean k < countVar k) {ahat bhat a b : ℝ}
    (hahat : 0 < ahat) (hbhat : 0 < bhat)
    (hroot : shapeScore ahat bhat (fun _ => σ) k = 0 ∧ rateScore ahat bhat (fun _ => σ) k = 0)
    (ha : 0 < a) (hb : 0 < b) (hne : (a, b) ≠ (ahat, bhat)) :
    logMarginalLik a b (fun _ => σ) k < logMarginalLik ahat bhat (fun _ => σ) k := by
  obtain ⟨rfl, hP⟩ := (score_eq_zero_iff_const hahat hbhat hσ hM).1 hroot
  set M := countMean k
  -- step 1: profile out the rate
  have hstep1 : logMarginalLik a b (fun _ => σ) k ≤ logMarginalLik a (σ * a / M) (fun _ => σ) k ∧
      (b ≠ σ * a / M → logMarginalLik a b (fun _ => σ) k <
        logMarginalLik a (σ * a / M) (fun _ => σ) k) := by
    have hlt : b ≠ σ * a / M → logMarginalLik a b (fun _ => σ) k <
        logMarginalLik a (σ * a / M) (fun _ => σ) k := fun hne =>
      logMarginalLik_lt_of_rateScore_eq_zero ha (by positivity) hb hne (fun _ => hσ)
        (rateScore_const_eq_zero ha hσ hM)
    refine ⟨?_, hlt⟩
    by_cases hbe : b = σ * a / M
    · rw [hbe]
    · exact (hlt hbe).le
  -- step 2: the profile likelihood peaks at `ahat`
  have hcont : ContinuousOn (fun x => profileLogLik x k) (Ioi 0) := fun x hx =>
    (hasDerivAt_profileLogLik hx hM.le).continuousAt.continuousWithinAt
  have hderiv : ∀ x, 0 < x → deriv (fun x => profileLogLik x k) x = profileShapeScore x k :=
    fun x hx => (hasDerivAt_profileLogLik hx hM.le).deriv
  have hstep2 : a ≠ ahat → profileLogLik a k < profileLogLik ahat k := fun hne => by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmono : StrictMonoOn (fun x => profileLogLik x k) (Ioc 0 ahat) := by
        refine strictMonoOn_of_deriv_pos (convex_Ioc 0 ahat) (hcont.mono fun x hx => hx.1)
          fun x hx => ?_
        rw [interior_Ioc] at hx
        rw [hderiv x hx.1]
        exact profileShapeScore_pos_of_lt hMV hx.1 hx.2 hP
      exact hmono ⟨ha, hlt.le⟩ ⟨hahat, le_rfl⟩ hlt
    · have hanti : StrictAntiOn (fun x => profileLogLik x k) (Ici ahat) := by
        refine strictAntiOn_of_deriv_neg (convex_Ici ahat)
          (hcont.mono fun x hx => lt_of_lt_of_le hahat hx) fun x hx => ?_
        rw [interior_Ici] at hx
        rw [hderiv x (hahat.trans hx)]
        exact profileShapeScore_neg_of_gt hMV hahat hx hP
      exact hanti le_rfl hgt.le hgt
  have e := logMarginalLik_rateRoot hσ ha hM
  have e' := logMarginalLik_rateRoot hσ hahat hM
  by_cases hae : a = ahat
  · subst hae
    have hbne : b ≠ σ * a / M := fun h => hne (by rw [h])
    exact hstep1.2 hbne
  · have := hstep2 hae
    linarith [hstep1.1]

/-- **Existence and uniqueness of the joint MLE at a common size factor** (Levin and Reeds 1977,
Theorem 2; Anscombe 1950). At a common size factor `σ > 0` and an overdispersed sample
`0 < M < V`, the log marginal likelihood `ℓ(a, b)` has exactly one maximizer over `(0, ∞)²`;
it is the unique positive root of the joint score equations, with rate `σ â / M`. -/
theorem existsUnique_isMaxOn_logMarginalLik [Nonempty ι] {σ : ℝ} (hσ : 0 < σ) {k : ι → ℕ}
    (hM : 0 < countMean k) (hMV : countMean k < countVar k) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ ∀ q : ℝ × ℝ, 0 < q.1 → 0 < q.2 →
      logMarginalLik q.1 q.2 (fun _ => σ) k ≤ logMarginalLik p.1 p.2 (fun _ => σ) k := by
  obtain ⟨a, b, ha, hb, hs, hr⟩ := exists_score_root_of_overdispersed hσ hM hMV
  have hmax : ∀ q : ℝ × ℝ, 0 < q.1 → 0 < q.2 → q ≠ (a, b) →
      logMarginalLik q.1 q.2 (fun _ => σ) k < logMarginalLik a b (fun _ => σ) k :=
    fun q hq1 hq2 hne => logMarginalLik_lt_of_score_root hσ hM hMV ha hb ⟨hs, hr⟩ hq1 hq2 hne
  refine ⟨(a, b), ⟨ha, hb, fun q hq1 hq2 => ?_⟩, fun p hp => ?_⟩
  · by_cases hq : q = (a, b)
    · rw [hq]
    · exact (hmax q hq1 hq2 hq).le
  · by_contra hne
    exact absurd (hp.2.2 (a, b) ha hb) (not_le.2 (hmax p hp.1 hp.2.1 hne))

/-- **Every joint MLE solves the score equations.** At a common size factor and an overdispersed
sample, a maximizer of `ℓ` over `(0, ∞)²` is the root of the joint score equations. -/
theorem score_eq_zero_of_isMaxOn [Nonempty ι] {σ : ℝ} (hσ : 0 < σ) {k : ι → ℕ}
    (hM : 0 < countMean k) (hMV : countMean k < countVar k) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hmax : ∀ q : ℝ × ℝ, 0 < q.1 → 0 < q.2 →
      logMarginalLik q.1 q.2 (fun _ => σ) k ≤ logMarginalLik a b (fun _ => σ) k) :
    shapeScore a b (fun _ => σ) k = 0 ∧ rateScore a b (fun _ => σ) k = 0 := by
  obtain ⟨a', b', ha', hb', hs, hr⟩ := exists_score_root_of_overdispersed hσ hM hMV
  by_contra hc
  have hne : (a, b) ≠ (a', b') := fun h => by
    simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hc ⟨hs, hr⟩
  exact absurd (hmax (a', b') ha' hb')
    (not_le.2 (logMarginalLik_lt_of_score_root hσ hM hMV ha' hb' ⟨hs, hr⟩ ha hb hne))

/-! ### The converse: no finite MLE when `0 < M` and `V ≤ M` -/

/-- **`H ≥ 0` without overdispersion.** If `V ≤ M`, Levin and Reeds's `H` is nonnegative on
`[0, ∞)`: a negative value would persist (`smoothedDiscrepancy_neg_of_le`) up to the terminal
value `n (M - V) / 2 ≥ 0` (`smoothedDiscrepancy_eq_of_ge`). -/
theorem smoothedDiscrepancy_nonneg [Nonempty ι] {k : ι → ℕ} (hVM : countVar k ≤ countMean k)
    {u : ℝ} (hu : 0 ≤ u) : 0 ≤ smoothedDiscrepancy k u := by
  by_contra hneg
  push Not at hneg
  set T : ℝ := max u (countMean k + ∑ i, (k i : ℝ))
  have hs : 0 ≤ ∑ i, (k i : ℝ) := sum_nonneg fun _ _ => by positivity
  have hTk : ∀ i, (k i : ℝ) ≤ T := fun i => by
    have := single_le_sum (f := fun i => (k i : ℝ)) (fun _ _ => by positivity) (mem_univ i)
    have := countMean_nonneg k
    exact le_max_of_le_right (by linarith)
  have hT := smoothedDiscrepancy_neg_of_le hu hneg (le_max_left _ _ : u ≤ T)
  rw [smoothedDiscrepancy_eq_of_ge (le_max_of_le_right (by linarith)) hTk] at hT
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  linarith [mul_nonneg hn.le (sub_nonneg.2 hVM)]

/-- Just right of `0`, `H(u) ≥ u - n u² / 2 > 0` once some count is positive. -/
private lemma smoothedDiscrepancy_pos_of_small [Nonempty ι] {k : ι → ℕ} (hM : 0 < countMean k)
    {u : ℝ} (hu : 0 < u) (huM : u ≤ countMean k) (hun : Fintype.card ι * u < 1) :
    0 < smoothedDiscrepancy k u := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, 1 ≤ k i := by
    by_contra h
    push Not at h
    have : countMean k = 0 := by simp [countMean, fun i => Nat.lt_one_iff.1 (h i)]
    linarith
  have h1 := le_rampSum hi₀ u
  norm_num at h1
  have h2 := single_le_sum (f := fun i => rampSum (k i) u) (fun i _ => rampSum_nonneg _ _)
    (mem_univ i₀)
  rw [smoothedDiscrepancy_eq_of_le huM]
  linarith [mul_lt_mul_of_pos_right hun hu]

/-- **The profile shape score is positive when `0 < M` and `V ≤ M`** (Levin and Reeds 1977,
Theorem 2, converse half). In `profileShapeScore_eq_integral` the boundary term is `≥ 0` by
`smoothedDiscrepancy_nonneg`, and `H > 0` just right of `0` makes the integral positive. -/
theorem profileShapeScore_pos_of_le [Nonempty ι] {k : ι → ℕ} (hM : 0 < countMean k)
    (hVM : countVar k ≤ countMean k) {a : ℝ} (ha : 0 < a) : 0 < profileShapeScore a k := by
  set T : ℝ := countMean k + ∑ i, (k i : ℝ)
  have hs : 0 ≤ ∑ i, (k i : ℝ) := sum_nonneg fun _ _ => by positivity
  have hTM : countMean k ≤ T := by linarith
  have hTk : ∀ i, (k i : ℝ) ≤ T := fun i => by
    have := single_le_sum (f := fun i => (k i : ℝ)) (fun _ _ => by positivity) (mem_univ i)
    linarith
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set ε : ℝ := min (countMean k) (1 / (2 * Fintype.card ι))
  have hε : 0 < ε := lt_min hM (by positivity)
  have hεM : ε ≤ countMean k := min_le_left _ _
  have hεn : Fintype.card ι * ε ≤ 1 / 2 :=
    calc (Fintype.card ι : ℝ) * ε ≤ Fintype.card ι * (1 / (2 * Fintype.card ι)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hn.le
      _ = 1 / 2 := by field_simp
  have hc := continuous_smoothedDiscrepancy k
  have hint := intervalIntegrable_div_cube hc ha hε.le
  have hpos : 0 < ∫ u in (0 : ℝ)..ε, smoothedDiscrepancy k u / (a + u) ^ 3 :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hint (fun u hu => div_pos
      (smoothedDiscrepancy_pos_of_small hM hu.1 (hu.2.le.trans hεM)
        (by linarith [mul_lt_mul_of_pos_left hu.2 hn]))
      (by have := hu.1; positivity)) hε
  have hrest : 0 ≤ ∫ u in ε..T, smoothedDiscrepancy k u / (a + u) ^ 3 :=
    intervalIntegral.integral_nonneg (hεM.trans hTM) fun u hu => by
      have hu0 : 0 ≤ u := hε.le.trans hu.1
      exact div_nonneg (smoothedDiscrepancy_nonneg hVM hu0) (by positivity)
  rw [profileShapeScore_eq_integral ha hTM hTk,
    ← intervalIntegral.integral_add_adjacent_intervals hint
      (intervalIntegrable_div_cube' hc ha hε.le (hεM.trans hTM))]
  have := div_nonneg (smoothedDiscrepancy_nonneg hVM (hM.le.trans hTM))
    (sq_nonneg (a + T))
  linarith

/-- **Without overdispersion the joint score equations have no positive root.** At a common size
factor `σ > 0` and a sample with `0 < M` and `V ≤ M`, no `(a, b) ∈ (0, ∞)²` solves both score
equations. -/
theorem score_ne_zero_of_le [Nonempty ι] {σ : ℝ} (hσ : 0 < σ) {k : ι → ℕ}
    (hM : 0 < countMean k) (hVM : countVar k ≤ countMean k) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ¬ (shapeScore a b (fun _ => σ) k = 0 ∧ rateScore a b (fun _ => σ) k = 0) := fun h =>
  (profileShapeScore_pos_of_le hM hVM ha).ne' ((score_eq_zero_iff_const ha hb hσ hM).1 h).2

/-- **The likelihood increases along the rate root when `0 < M` and `V ≤ M`.** At a common size
factor `σ > 0`, `ℓ` strictly increases along the explicit path `a ↦ (a, σ a / M)`, so `ℓ` has no
finite maximizer along this path. -/
theorem strictMonoOn_logMarginalLik_rateRoot [Nonempty ι] {σ : ℝ} (hσ : 0 < σ) {k : ι → ℕ}
    (hM : 0 < countMean k) (hVM : countVar k ≤ countMean k) :
    StrictMonoOn (fun a => logMarginalLik a (σ * a / countMean k) (fun _ => σ) k) (Ioi 0) := by
  have hP : StrictMonoOn (fun x => profileLogLik x k) (Ioi 0) :=
    strictMonoOn_of_deriv_pos (convex_Ioi 0)
      (fun x hx => (hasDerivAt_profileLogLik hx hM.le).continuousAt.continuousWithinAt)
      fun x hx => by
        rw [interior_Ioi] at hx
        rw [(hasDerivAt_profileLogLik hx hM.le).deriv]
        exact profileShapeScore_pos_of_le hM hVM hx
  intro a ha a' ha' h
  dsimp only
  rw [logMarginalLik_rateRoot hσ ha hM, logMarginalLik_rateRoot hσ ha' hM]
  linarith [hP ha ha' h]

/-- **No finite joint MLE when `V ≤ M`** (Levin and Reeds 1977, Theorem 2, converse half: the
maximum occurs at a finite shape only if `M < V`). At a common size factor `σ > 0` and a sample
with `0 < M` and `V ≤ M`, the log marginal likelihood has no maximizer on `(0, ∞)²`: every
`(a, b)` is beaten by `(a + 1, σ (a + 1) / M)`. -/
theorem not_exists_isMaxOn_logMarginalLik [Nonempty ι] {σ : ℝ} (hσ : 0 < σ) {k : ι → ℕ}
    (hM : 0 < countMean k) (hVM : countVar k ≤ countMean k) :
    ¬ ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ ∀ q : ℝ × ℝ, 0 < q.1 → 0 < q.2 →
      logMarginalLik q.1 q.2 (fun _ => σ) k ≤ logMarginalLik p.1 p.2 (fun _ => σ) k := by
  rintro ⟨⟨a, b⟩, ha, hb, hmax⟩
  dsimp only at ha hb hmax
  have h1 : logMarginalLik a b (fun _ => σ) k ≤
      logMarginalLik a (σ * a / countMean k) (fun _ => σ) k := by
    by_cases hbe : b = σ * a / countMean k
    · rw [hbe]
    · exact (logMarginalLik_lt_of_rateScore_eq_zero ha (by positivity) hb hbe (fun _ => hσ)
        (rateScore_const_eq_zero ha hσ hM)).le
  have ha1 : (0 : ℝ) < a + 1 := by linarith
  have h2 := strictMonoOn_logMarginalLik_rateRoot hσ hM hVM (mem_Ioi.2 ha) (mem_Ioi.2 ha1)
    (lt_add_one a)
  have h3 := hmax (a + 1, σ * (a + 1) / countMean k) ha1 (by dsimp only; positivity)
  dsimp only at h2 h3
  linarith

end MathlibExt.Biology.Omics.HierarchicalCount
