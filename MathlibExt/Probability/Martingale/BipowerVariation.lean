/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Martingale.RealizedQV
public import MathlibExt.Probability.Martingale.McLeishCLT
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Bipower variation: jump-robust realized quadratic variation

Realized variance `∑ᵢ (Δᵢ X)²` of a process with jumps converges to the integrated variance
*plus* the sum of squared jumps. Barndorff-Nielsen and Shephard's realized bipower variation
`∑ᵢ |Δᵢ X| |Δᵢ₊₁ X|` discards the jumps: a jump enters one increment, which is multiplied by a
neighbouring continuous increment that shrinks to zero. This file proves that robustness and the
convergence of bipower variation for a Gaussian-type continuous part.

The setting is a triangular array of increments over a grid of mesh `1/n`:
`Δ n i = c n i + J n i`, where `J n i` is the increment of a pure-jump path
`t ↦ ∑_{k < K} ξ k 𝟙{τ k ≤ t}` with finitely many (random) jumps over `(i/n, (i+1)/n]`
(`jumpIncrement`), and `c n i` is the continuous part.

## Main results

* `abs_bipowerVariation_add_jumpIncrement_sub_le` (pathwise): if `|c i| ≤ M` for `i ≤ N` and
  any two jump times are at least `2/n` apart, then adding the jumps moves the bipower variation
  by at most `2 M ∑ₖ |ξ k|`.
* `eventually_jumpIncrement_mul_succ_eq_zero`: finitely many distinct jump times eventually lie
  in non-adjacent grid cells, so the products of adjacent jump increments vanish.
* `tendstoInMeasure_bipowerVariation_add_jump_sub` (**jump robustness**): if the largest
  continuous increment tends to `0` in probability, then for a.s. distinct random jump times
  `BPV(c + J) - BPV(c) → 0` in probability.
* `tendstoInMeasure_mul_of_tendstoInMeasure_zero`: `f n → 0` in probability and a fixed real
  random variable `A` give `f n * A → 0` in probability.
* `tendstoInMeasure_sup_abs_mul`: under the fourth-moment condition below, the largest continuous
  increment `max_{i ≤ L n} |s n i * Z n i|` tends to `0` in probability.
* `tendstoInMeasure_bipowerVariation_sub`: for `c n i = s n i * Z n i`, where each row
  `Z n 0, Z n 1, …` is independent, every `Z n i` has the law of `Z 0 0`, `E (Z 0 0)⁴ < ∞` and
  `∑_{i ≤ L n} (s n i)⁴ → 0`: `BPV(c) - (E|Z 0 0|)² ∑ᵢ |s n i| |s n (i+1)| → 0` in probability.
* `tendstoInMeasure_bipowerVariation_add_jump` (**bipower variation convergence with jumps**):
  if moreover `∑ᵢ |s n i| |s n (i+1)| → V`, then `BPV(c + J) → (E|Z 0 0|)² V` in probability.
* `tendstoInMeasure_bipowerVariation_add_jump_const`: the constant-volatility case
  `s n i = σ / √n` on the grid of `[0, 1]` (`L n = n - 1` bipower terms):
  `BPV → (E|Z 0 0|)² σ²`.
* `integral_abs_gaussianReal`: `E|N(0,1)| = √(2/π)`.
* `tendstoInMeasure_bipowerVariation_add_jump_gaussian`: rows of i.i.d. standard Gaussians, e.g.
  the normalised Brownian increments `Z n i = √n (W_{(i+1)/n} - W_{i/n})`, so that
  `σ / √n * Z n i = σ (W_{(i+1)/n} - W_{i/n})`, plus finitely many jumps (which may depend on
  `W`): `BPV → (2/π) σ²`, i.e. the classical normalisation `(π/2) BPV → σ² = ∫₀¹ σ²`.

## Proof

Pathwise, `||a + b| |c + d| - |a| |c|| ≤ |a| |d| + |b| |c| + 3 |b| |d|`, so the jumps move the
bipower variation by at most `2 M ∑ᵢ |J i| + 3 ∑ᵢ |J i| |J (i+1)|`. Each jump lies in one grid
cell, so `∑ᵢ |J i| ≤ ∑ₖ |ξ k|`; when the jump times are `2/n`-separated no two adjacent cells
both contain jumps. In probability, the event that two jump times are within `1/(j+1)` shrinks to
a null set as `j → ∞`, and `M_n ∑ₖ |ξ k| → 0` in probability because `∑ₖ |ξ k|` is an a.s. finite
random variable.

For the continuous part fix a row `n` and write `Yᵢ = |Z n i| |Z n (i+1)|`, so
`E Yᵢ = (E|Z 0 0|)²` and `E Yᵢ² ≤ E (Z 0 0)⁴`. The terms with even `i` are pairwise independent
(disjoint index pairs), and so are those with odd `i`; Chebyshev's inequality on each half bounds
the deviation probability by `4 E (Z 0 0)⁴ ∑ᵢ (s n i s n (i+1))² / ε² ≤
4 E (Z 0 0)⁴ ∑ᵢ (s n i)⁴ / ε²`. A union bound with Markov's inequality for `(s n i Z n i)⁴` shows
the largest continuous increment tends to `0`. Only independence within a row is used; rows may
depend on each other arbitrarily, as the normalised increments of one Brownian path over
different grids do.

## Scope and what is not proved

* The continuous part is `s n i * Z n i` with deterministic scales `s n i` and rows of i.i.d.
  innovations: the increments of `∫ σ dW` over the grid of mesh `1/n` for a deterministic
  volatility `σ`, with `s n i = (∫_{i/n}^{(i+1)/n} σ²)^{1/2}` and
  `Z n i = (∫_{i/n}^{(i+1)/n} σ dW) / s n i`. No independence between the jumps and `W` is
  assumed. A random volatility process, as in
  Barndorff-Nielsen–Shephard, is not treated, nor is the Riemann-sum step
  `∑ᵢ |s n i| |s n (i+1)| → ∫ σ²` for a general continuous `σ`; that limit is the hypothesis `hV`.
* The jump part has finitely many jumps (finite activity, e.g. compound Poisson). Infinite
  activity jumps are not treated.
* Only consistency is proved. The bipower CLT and the jump test based on `RV - (π/2) BPV` are not.
* A fourth moment of `Z 0 0` is assumed; Gaussian innovations satisfy it.

## Source

O. E. Barndorff-Nielsen and N. Shephard, *Power and bipower variation with stochastic volatility
and jumps*, Journal of Financial Econometrics 2 (2004), 1–37: for `X = ∫ σ dW + J` with `J` of
finite activity, `μ₁⁻² ∑ᵢ |Δᵢ X| |Δᵢ₊₁ X| → ∫₀¹ σ²` in probability, where `μ₁ = E|N(0,1)| = √(2/π)`.
(Statement paraphrased; no theorem number checked against the text.)
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace MathlibExt.Probability.Martingale

noncomputable section

variable {Ω : Type*}

/-! ### Definitions -/

/-- Realized bipower variation `∑_{i < N} |d i| |d (i+1)|` of the increments `d 0, …, d N`. -/
def bipowerVariation (d : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, |d i| * |d (i + 1)|

/-- The pure-jump path `t ↦ ∑_{k ∈ s} ξ k 𝟙{τ k ≤ t}`: jumps of size `ξ k` at the times `τ k`. -/
def jumpPath {ι : Type*} (s : Finset ι) (τ ξ : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ s, if τ k ≤ t then ξ k else 0

/-- Increment of `jumpPath s τ ξ` over the `i`-th cell `(i/n, (i+1)/n]` of the grid of mesh
`1/n`. -/
def jumpIncrement {ι : Type*} (s : Finset ι) (τ ξ : ι → ℝ) (n i : ℕ) : ℝ :=
  jumpPath s τ ξ (((i : ℝ) + 1) / n) - jumpPath s τ ξ ((i : ℝ) / n)

/-! ### Jump increments -/

/-- A jump increment collects the jumps in its grid cell. -/
lemma jumpIncrement_eq {ι : Type*} (s : Finset ι) (τ ξ : ι → ℝ) (n i : ℕ) :
    jumpIncrement s τ ξ n i =
      ∑ k ∈ s, if τ k ∈ Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n) then ξ k else 0 := by
  have hle : (i : ℝ) / n ≤ ((i : ℝ) + 1) / n :=
    div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
  rw [jumpIncrement, jumpPath, jumpPath, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h2 : τ k ≤ (i : ℝ) / n
  · have h1 : τ k ≤ ((i : ℝ) + 1) / n := h2.trans hle
    have h3 : τ k ∉ Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n) := fun h => not_lt.2 h2 h.1
    rw [ite_eq_left h1, ite_eq_left h2, ite_eq_right h3, sub_self]
  · have h2' : (i : ℝ) / n < τ k := not_le.1 h2
    by_cases h1 : τ k ≤ ((i : ℝ) + 1) / n
    · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left ⟨h2', h1⟩, sub_zero]
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right fun h => h1 h.2, sub_zero]

/-- A time lies in at most one grid cell. -/
private lemma eq_of_mem_Ioc_div {n i j : ℕ} {t : ℝ}
    (hi : t ∈ Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n))
    (hj : t ∈ Set.Ioc ((j : ℝ) / n) (((j : ℝ) + 1) / n)) : i = j := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, div_zero, Set.mem_Ioc] at hi
    exact absurd hi.2 (not_le.2 hi.1)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h1 : (i : ℝ) < j + 1 := (div_lt_div_iff_of_pos_right hn').1 (hi.1.trans_le hj.2)
  have h2 : (j : ℝ) < i + 1 := (div_lt_div_iff_of_pos_right hn').1 (hj.1.trans_le hi.2)
  have h1' : i < j + 1 := by exact_mod_cast h1
  have h2' : j < i + 1 := by exact_mod_cast h2
  omega

/-- The jump increments of a row have total size at most the total jump size. -/
theorem sum_abs_jumpIncrement_le {ι : Type*} (s : Finset ι) (τ ξ : ι → ℝ) (n N : ℕ) :
    ∑ i ∈ Finset.range N, |jumpIncrement s τ ξ n i| ≤ ∑ k ∈ s, |ξ k| := by
  classical
  calc ∑ i ∈ Finset.range N, |jumpIncrement s τ ξ n i|
      ≤ ∑ i ∈ Finset.range N, ∑ k ∈ s,
          if τ k ∈ Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n) then |ξ k| else 0 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [jumpIncrement_eq]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> simp
    _ = ∑ k ∈ s, ∑ i ∈ Finset.range N,
          if τ k ∈ Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n) then |ξ k| else 0 :=
        Finset.sum_comm
    _ ≤ ∑ k ∈ s, |ξ k| := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have hcard : ((Finset.range N).filter fun i : ℕ =>
            τ k ∈ Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n)).card ≤ 1 :=
          Finset.card_le_one.2 fun i hi j hj =>
            eq_of_mem_Ioc_div (Finset.mem_filter.1 hi).2 (Finset.mem_filter.1 hj).2
        calc _ ≤ (1 : ℝ) * |ξ k| :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (abs_nonneg _)
          _ = |ξ k| := one_mul _

/-- If any two jump times are at least `2/n` apart, no two adjacent grid cells both contain
jumps. -/
theorem jumpIncrement_mul_succ_eq_zero {ι : Type*} {s : Finset ι} {τ : ι → ℝ} (ξ : ι → ℝ)
    {n : ℕ} (hgap : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → 2 / (n : ℝ) ≤ |τ k - τ l|) (i : ℕ) :
    jumpIncrement s τ ξ n i * jumpIncrement s τ ξ n (i + 1) = 0 := by
  classical
  by_contra hne
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
  rw [jumpIncrement_eq] at h1 h2
  obtain ⟨k, hk, hk'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  obtain ⟨l, hl, hl'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
  have hτk : τ k ∈ Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n) := by
    by_contra h
    exact hk' (by rw [ite_eq_right h])
  have hτl : τ l ∈ Set.Ioc (((i + 1 : ℕ) : ℝ) / n) ((((i + 1 : ℕ) : ℝ) + 1) / n) := by
    by_contra h
    exact hl' (by rw [ite_eq_right h])
  push_cast at hτl
  have hkl : k ≠ l := by
    rintro rfl
    exact absurd hτl.1 (not_lt.2 hτk.2)
  have hg := hgap k hk l hl hkl
  have hlt : τ l - τ k < 2 / n := by
    have : ((i : ℝ) + 1 + 1) / n - (i : ℝ) / n = 2 / n := by ring
    linarith [hτk.1, hτl.2]
  have hpos : 0 < τ l - τ k := by linarith [hτk.2, hτl.1]
  rw [abs_sub_comm, abs_of_pos hpos] at hg
  linarith

/-- Finitely many distinct jump times eventually lie in non-adjacent grid cells. -/
theorem eventually_jumpIncrement_mul_succ_eq_zero {ι : Type*} {s : Finset ι} {τ : ι → ℝ}
    (hτ : Set.InjOn τ s) (ξ : ι → ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ i, jumpIncrement s τ ξ n i * jumpIncrement s τ ξ n (i + 1) = 0 := by
  have h : ∀ᶠ n : ℕ in atTop, ∀ k ∈ s, ∀ l ∈ s, k ≠ l → 2 / (n : ℝ) ≤ |τ k - τ l| := by
    refine (eventually_all_finset s).2 fun k hk => (eventually_all_finset s).2 fun l hl => ?_
    by_cases hkl : k = l
    · exact Eventually.of_forall fun _ h => absurd hkl h
    · have hpos : 0 < |τ k - τ l| := abs_pos.2 (sub_ne_zero.2 fun h => hkl (hτ hk hl h))
      filter_upwards [(tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).eventually
        (eventually_le_nhds hpos)] with n hn _ using hn
  filter_upwards [h] with n hn i using jumpIncrement_mul_succ_eq_zero ξ hn i

/-! ### Pathwise jump robustness -/

/-- `||a + b| |c + d| - |a| |c|| ≤ |a| |d| + |b| |c| + 3 |b| |d|`. -/
private lemma abs_mul_abs_add_sub_le (a b c d : ℝ) :
    |(|a + b| * |c + d| - |a| * |c|)| ≤ |a| * |d| + |b| * |c| + 3 * (|b| * |d|) := by
  have h1 : |a + b| ≤ |a| + |b| := abs_add_le a b
  have h2 : |c + d| ≤ |c| + |d| := abs_add_le c d
  have h3 : |a| ≤ |a + b| + |b| := by
    calc |a| = |(a + b) + -b| := by rw [add_neg_cancel_right]
      _ ≤ |a + b| + |-b| := abs_add_le _ _
      _ = |a + b| + |b| := by rw [abs_neg]
  have h4 : |c| ≤ |c + d| + |d| := by
    calc |c| = |(c + d) + -d| := by rw [add_neg_cancel_right]
      _ ≤ |c + d| + |-d| := abs_add_le _ _
      _ = |c + d| + |d| := by rw [abs_neg]
  have u : |a + b| * |c + d| ≤ (|a| + |b|) * (|c| + |d|) :=
    mul_le_mul h1 h2 (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have l : |a| * |c| ≤ (|a + b| + |b|) * (|c + d| + |d|) :=
    mul_le_mul h3 h4 (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have l2 : |a + b| * |d| ≤ (|a| + |b|) * |d| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have l3 : |b| * |c + d| ≤ |b| * (|c| + |d|) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  rw [abs_sub_le_iff]
  constructor <;> nlinarith [u, l, l2, l3]

/-- **Pathwise perturbation bound.** Adding increments `J` to increments `c` bounded by `M`
moves the bipower variation by at most `2 M ∑ᵢ |J i| + 3 ∑ᵢ |J i| |J (i+1)|`. -/
theorem abs_bipowerVariation_add_sub_le (c J : ℕ → ℝ) (N : ℕ) {M : ℝ}
    (hM : ∀ i ≤ N, |c i| ≤ M) :
    |bipowerVariation (fun i => c i + J i) N - bipowerVariation c N| ≤
      2 * M * (∑ i ∈ Finset.range (N + 1), |J i|) +
        3 * ∑ i ∈ Finset.range N, |J i| * |J (i + 1)| := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (Nat.zero_le _))
  have hterm : ∀ i ∈ Finset.range N,
      |(|c i + J i| * |c (i + 1) + J (i + 1)| - |c i| * |c (i + 1)|)| ≤
        M * |J i| + M * |J (i + 1)| + 3 * (|J i| * |J (i + 1)|) := by
    intro i hi
    have hi' : i + 1 ≤ N := Finset.mem_range.1 hi
    refine (abs_mul_abs_add_sub_le _ _ _ _).trans ?_
    have e1 : |c i| * |J (i + 1)| ≤ M * |J (i + 1)| :=
      mul_le_mul_of_nonneg_right (hM i (by omega)) (abs_nonneg _)
    have e2 : |J i| * |c (i + 1)| ≤ M * |J i| := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hM (i + 1) hi') (abs_nonneg _)
    linarith
  have hs1 : ∑ i ∈ Finset.range N, |J i| ≤ ∑ i ∈ Finset.range (N + 1), |J i| := by
    rw [Finset.sum_range_succ]
    linarith [abs_nonneg (J N)]
  have hs2 : ∑ i ∈ Finset.range N, |J (i + 1)| ≤ ∑ i ∈ Finset.range (N + 1), |J i| := by
    rw [Finset.sum_range_succ']
    linarith [abs_nonneg (J 0)]
  unfold bipowerVariation
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ i ∈ Finset.range N,
          |(|c i + J i| * |c (i + 1) + J (i + 1)| - |c i| * |c (i + 1)|)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, (M * |J i| + M * |J (i + 1)| + 3 * (|J i| * |J (i + 1)|)) :=
        Finset.sum_le_sum hterm
    _ = M * (∑ i ∈ Finset.range N, |J i|) + M * (∑ i ∈ Finset.range N, |J (i + 1)|) +
          3 * ∑ i ∈ Finset.range N, |J i| * |J (i + 1)| := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hs1 hM0, mul_le_mul_of_nonneg_left hs2 hM0]

/-- **Pathwise jump robustness.** If the continuous increments are bounded by `M` and any two
jump times are at least `2/n` apart, adding the jumps moves the bipower variation by at most
`2 M ∑ₖ |ξ k|`. -/
theorem abs_bipowerVariation_add_jumpIncrement_sub_le {ι : Type*} (c : ℕ → ℝ) (s : Finset ι)
    (τ ξ : ι → ℝ) (n N : ℕ) {M : ℝ} (hM : ∀ i ≤ N, |c i| ≤ M)
    (hgap : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → 2 / (n : ℝ) ≤ |τ k - τ l|) :
    |bipowerVariation (fun i => c i + jumpIncrement s τ ξ n i) N - bipowerVariation c N| ≤
      2 * M * ∑ k ∈ s, |ξ k| := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (Nat.zero_le _))
  have hB := abs_bipowerVariation_add_sub_le c (jumpIncrement s τ ξ n) N hM
  have hadj : ∑ i ∈ Finset.range N,
      |jumpIncrement s τ ξ n i| * |jumpIncrement s τ ξ n (i + 1)| = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [← abs_mul, jumpIncrement_mul_succ_eq_zero ξ hgap i, abs_zero]
  rw [hadj, mul_zero, add_zero] at hB
  exact hB.trans (mul_le_mul_of_nonneg_left (sum_abs_jumpIncrement_le s τ ξ n (N + 1))
    (by positivity))

/-! ### Convergence in probability: jump robustness -/

/-- Two-set covering argument: if `F n ⊆ E j ∪ G j n` eventually in `n` for each `j`, with
`μ (E j) → 0` and `μ (G j n) → 0` for each `j`, then `μ (F n) → 0`. -/
private lemma tendsto_measure_of_cover {m : MeasurableSpace Ω} {μ : Measure Ω}
    {F : ℕ → Set Ω} (E : ℕ → Set Ω) (hE : Tendsto (fun j => μ (E j)) atTop (𝓝 0))
    (G : ℕ → ℕ → Set Ω) (hG : ∀ j, Tendsto (fun n => μ (G j n)) atTop (𝓝 0))
    (hcov : ∀ j, ∀ᶠ n in atTop, F n ⊆ E j ∪ G j n) :
    Tendsto (fun n => μ (F n)) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at hE ⊢
  intro η hη
  obtain ⟨j, hj⟩ := (hE (η / 2) (ENNReal.half_pos hη.ne')).exists
  filter_upwards [hcov j, ENNReal.tendsto_nhds_zero.1 (hG j) (η / 2)
    (ENNReal.half_pos hη.ne')] with n hn hn'
  calc μ (F n) ≤ μ (E j ∪ G j n) := measure_mono hn
    _ ≤ μ (E j) + μ (G j n) := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hj hn'
    _ = η := ENNReal.add_halves η

/-- A sequence tending to `0` in probability, times a fixed real random variable, tends to `0`
in probability. -/
theorem tendstoInMeasure_mul_of_tendstoInMeasure_zero {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} (hf : TendstoInMeasure μ f atTop 0) {A : Ω → ℝ}
    (hA : Measurable A) : TendstoInMeasure μ (fun n ω => f n ω * A ω) atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hf ⊢
  intro ε hε
  have hEm : ∀ j : ℕ, MeasurableSet {ω | (j : ℝ) < |A ω|} := fun j =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp hA)
  have hinter : (⋂ j : ℕ, {ω | (j : ℝ) < |A ω|}) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_lt]
    exact exists_nat_ge _
  have hE : Tendsto (fun j : ℕ => μ {ω | (j : ℝ) < |A ω|}) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := μ) (s := fun j : ℕ => {ω | (j : ℝ) < |A ω|})
      (fun j => (hEm j).nullMeasurableSet)
      (fun i j hij ω hω => by
        simp only [Set.mem_ofPred_eq] at hω ⊢
        exact (Nat.cast_le.2 hij).trans_lt hω) ⟨0, measure_ne_top _ _⟩
    rwa [hinter, measure_empty] at this
  refine tendsto_measure_of_cover (fun j : ℕ => {ω | (j : ℝ) < |A ω|}) hE
    (fun j n => {x | ε / ((j : ℝ) + 1) ≤ ‖f n x - (0 : Ω → ℝ) x‖})
    (fun j => hf (ε / ((j : ℝ) + 1)) (by positivity)) fun j => Eventually.of_forall fun n ω hω => ?_
  simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω ⊢
  by_cases hA' : (j : ℝ) < |A ω|
  · exact Or.inl hA'
  · right
    rw [abs_mul] at hω
    have hj : 0 < (j : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hj]
    calc ε ≤ |f n ω| * |A ω| := hω
      _ ≤ |f n ω| * ((j : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [not_lt.1 hA']) (abs_nonneg _)

/-- `ω ↦ ∑_{k < K ω} f k ω` is measurable for measurable `K` and `f k`. -/
private lemma measurable_sum_range_rand {m : MeasurableSpace Ω} {K : Ω → ℕ} (hK : Measurable K)
    {f : ℕ → Ω → ℝ} (hf : ∀ k, Measurable (f k)) :
    Measurable fun ω => ∑ k ∈ Finset.range (K ω), f k ω := by
  have : Measurable fun p : Ω × ℕ => ∑ k ∈ Finset.range p.2, f k p.1 :=
    measurable_from_prod_countable_left fun N =>
      show Measurable fun x => ∑ k ∈ Finset.range N, f k x from
        Finset.measurable_fun_sum _ fun k _ => hf k
  exact this.comp (measurable_id.prodMk hK)

/-- **Jump robustness of bipower variation.** Let `c n i` be continuous increments whose largest
one, over the `L n + 1` increments used, tends to `0` in probability, and add the increments of
`K` random jumps of sizes `ξ k` at a.s. distinct times `τ k`. Then the bipower variation changes
by an amount tending to `0` in probability. -/
theorem tendstoInMeasure_bipowerVariation_add_jump_sub {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (c : ℕ → ℕ → Ω → ℝ) (L : ℕ → ℕ)
    (hc : TendstoInMeasure μ (fun n ω => (Finset.range (L n + 1)).sup'
      Finset.nonempty_range_add_one fun i => |c n i ω|) atTop 0)
    {K : Ω → ℕ} {τ ξ : ℕ → Ω → ℝ} (hK : Measurable K) (hτ : ∀ k, Measurable (τ k))
    (hξ : ∀ k, Measurable (ξ k))
    (hinj : ∀ᵐ ω ∂μ, Set.InjOn (fun k => τ k ω) (Finset.range (K ω))) :
    TendstoInMeasure μ (fun n ω =>
      bipowerVariation (fun i => c n i ω +
          jumpIncrement (Finset.range (K ω)) (fun k => τ k ω) (fun k => ξ k ω) n i) (L n) -
        bipowerVariation (fun i => c n i ω) (L n)) atTop 0 := by
  have hAm : Measurable fun ω => ∑ k ∈ Finset.range (K ω), |ξ k ω| :=
    measurable_sum_range_rand hK fun k => continuous_abs.measurable.comp (hξ k)
  have hMA := tendstoInMeasure_mul_of_tendstoInMeasure_zero hc hAm
  rw [tendstoInMeasure_iff_norm] at hMA ⊢
  intro ε hε
  -- `E j`: two of the jump times are closer than `1/(j+1)`.
  let E : ℕ → Set Ω := fun j => {ω | ∃ k l, k < K ω ∧ l < K ω ∧ k ≠ l ∧
    |τ k ω - τ l ω| < 1 / ((j : ℝ) + 1)}
  have hEm : ∀ j, MeasurableSet (E j) := by
    intro j
    refine measurableSet_setOfPred.2 (Measurable.exists fun k => Measurable.exists fun l => ?_)
    refine (measurable_from_nat.comp hK).and ((measurable_from_nat.comp hK).and
      (measurable_const.and ?_))
    exact measurableSet_setOfPred.1 (measurableSet_lt
      (continuous_abs.measurable.comp ((hτ k).sub (hτ l))) measurable_const)
  have hEanti : Antitone E := by
    intro i j hij ω ⟨k, l, hk, hl, hkl, h⟩
    refine ⟨k, l, hk, hl, hkl, h.trans_le (one_div_le_one_div_of_le (by positivity) ?_)⟩
    exact_mod_cast Nat.add_le_add_right hij 1
  have hEnull : μ (⋂ j, E j) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hinj)
    simp only [Set.mem_iInter] at hω
    simp only [Set.mem_ofPred_eq]
    intro hω'
    have hev : ∀ᶠ j : ℕ in atTop, ∀ k ∈ Finset.range (K ω), ∀ l ∈ Finset.range (K ω), k ≠ l →
        1 / ((j : ℝ) + 1) ≤ |τ k ω - τ l ω| := by
      refine (eventually_all_finset _).2 fun k hk => (eventually_all_finset _).2 fun l hl => ?_
      by_cases hkl : k = l
      · exact Eventually.of_forall fun _ h => absurd hkl h
      · have hpos : 0 < |τ k ω - τ l ω| :=
          abs_pos.2 (sub_ne_zero.2 fun h => hkl (hω' hk hl h))
        filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually
          (eventually_le_nhds hpos)] with j hj _ using hj
    obtain ⟨j, hj⟩ := hev.exists
    obtain ⟨k, l, hk, hl, hkl, h⟩ := hω j
    exact absurd (hj k (Finset.mem_range.2 hk) l (Finset.mem_range.2 hl) hkl) (not_le.2 h)
  have hE : Tendsto (fun j => μ (E j)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := μ) (fun j => (hEm j).nullMeasurableSet) hEanti
      ⟨0, measure_ne_top _ _⟩
    rwa [hEnull] at this
  refine tendsto_measure_of_cover E hE (fun _ n => {ω | ε / 2 ≤
      ‖(Finset.range (L n + 1)).sup' Finset.nonempty_range_add_one (fun i => |c n i ω|) *
        (∑ k ∈ Finset.range (K ω), |ξ k ω|) - (0 : Ω → ℝ) ω‖})
    (fun _ => hMA (ε / 2) (by positivity)) fun j => ?_
  filter_upwards [eventually_ge_atTop (2 * (j + 1))] with n hn ω hω
  by_cases hωE : ω ∈ E j
  · exact Or.inl hωE
  right
  have hgap : ∀ k ∈ Finset.range (K ω), ∀ l ∈ Finset.range (K ω), k ≠ l →
      2 / (n : ℝ) ≤ |τ k ω - τ l ω| := by
    intro k hk l hl hkl
    have h1 : 1 / ((j : ℝ) + 1) ≤ |τ k ω - τ l ω| := not_lt.1 fun h =>
      hωE ⟨k, l, Finset.mem_range.1 hk, Finset.mem_range.1 hl, hkl, h⟩
    have hn' : (2 : ℝ) * ((j : ℝ) + 1) ≤ n := by exact_mod_cast hn
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h2 : 2 / (n : ℝ) ≤ 1 / ((j : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      linarith
    linarith
  set M := (Finset.range (L n + 1)).sup' Finset.nonempty_range_add_one fun i => |c n i ω|
  have hMn : ∀ i ≤ L n, |c n i ω| ≤ M := fun i hi =>
    Finset.le_sup' (fun i => |c n i ω|) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hMn 0 (Nat.zero_le _))
  have hB := abs_bipowerVariation_add_jumpIncrement_sub_le (fun i => c n i ω)
    (Finset.range (K ω)) (fun k => τ k ω) (fun k => ξ k ω) n (L n) hMn hgap
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω ⊢
  have : ε ≤ 2 * (M * ∑ k ∈ Finset.range (K ω), |ξ k ω|) := by
    calc ε ≤ _ := hω
      _ ≤ 2 * M * ∑ k ∈ Finset.range (K ω), |ξ k ω| := hB
      _ = _ := by ring
  calc ε / 2 ≤ M * ∑ k ∈ Finset.range (K ω), |ξ k ω| := by linarith
    _ ≤ |M * (∑ k ∈ Finset.range (K ω), |ξ k ω|)| := le_abs_self _

/-! ### Convergence in probability: the continuous part -/

section Continuous

variable {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
  {Y : Ω → ℝ}

omit [IsProbabilityMeasure μ] in
private lemma integrable_pow_four (hid : ∀ i, IdentDistrib (X i) Y μ μ)
    (hZ4 : Integrable (fun ω => Y ω ^ 4) μ) (i : ℕ) :
    Integrable (fun ω => X i ω ^ 4) μ :=
  ((hid i).comp (measurable_id.pow_const 4)).integrable_iff.2 hZ4

omit [IsProbabilityMeasure μ] in
private lemma integral_pow_four (hid : ∀ i, IdentDistrib (X i) Y μ μ) (i : ℕ) :
    ∫ ω, X i ω ^ 4 ∂μ = ∫ ω, Y ω ^ 4 ∂μ :=
  ((hid i).comp (measurable_id.pow_const 4)).integral_eq

private lemma sq_abs_mul_abs_le (a b : ℝ) : (|a| * |b|) ^ 2 ≤ (a ^ 4 + b ^ 4) / 2 := by
  rw [mul_pow, sq_abs, sq_abs]
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]

omit [IsProbabilityMeasure μ] in
private lemma aestronglyMeasurable_abs_mul_abs (hmeas : ∀ i, Measurable (X i)) (i : ℕ) :
    AEStronglyMeasurable (fun ω => |X i ω| * |X (i + 1) ω|) μ :=
  ((continuous_abs.measurable.comp (hmeas i)).mul
    (continuous_abs.measurable.comp (hmeas (i + 1)))).aestronglyMeasurable

omit [IsProbabilityMeasure μ] in
private lemma integrable_sq_abs_mul_abs (hmeas : ∀ i, Measurable (X i))
    (hid : ∀ i, IdentDistrib (X i) Y μ μ) (hZ4 : Integrable (fun ω => Y ω ^ 4) μ)
    (i : ℕ) : Integrable (fun ω => (|X i ω| * |X (i + 1) ω|) ^ 2) μ := by
  refine Integrable.mono' (((integrable_pow_four hid hZ4 i).add
    (integrable_pow_four hid hZ4 (i + 1))).div_const 2)
    ((aestronglyMeasurable_abs_mul_abs hmeas i).pow 2) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_abs_mul_abs_le _ _

omit [IsProbabilityMeasure μ] in
private lemma memLp_abs_mul_abs (hmeas : ∀ i, Measurable (X i))
    (hid : ∀ i, IdentDistrib (X i) Y μ μ) (hZ4 : Integrable (fun ω => Y ω ^ 4) μ)
    (i : ℕ) : MemLp (fun ω => |X i ω| * |X (i + 1) ω|) 2 μ :=
  (memLp_two_iff_integrable_sq (aestronglyMeasurable_abs_mul_abs hmeas i)).2
    (integrable_sq_abs_mul_abs hmeas hid hZ4 i)

omit [IsProbabilityMeasure μ] in
private lemma integral_abs_mul_abs (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hid : ∀ i, IdentDistrib (X i) Y μ μ) (i : ℕ) :
    ∫ ω, |X i ω| * |X (i + 1) ω| ∂μ = (∫ ω, |Y ω| ∂μ) ^ 2 := by
  have hi : IndepFun (fun ω => |X i ω|) (fun ω => |X (i + 1) ω|) μ :=
    (hind.indepFun (show i ≠ i + 1 by omega)).comp continuous_abs.measurable
      continuous_abs.measurable
  have h0 : ∀ j, ∫ ω, |X j ω| ∂μ = ∫ ω, |Y ω| ∂μ := fun j =>
    ((hid j).comp continuous_abs.measurable).integral_eq
  rw [IndepFun.integral_fun_mul_eq_mul_integral hi
    (continuous_abs.measurable.comp (hmeas i)).aestronglyMeasurable
    (continuous_abs.measurable.comp (hmeas (i + 1))).aestronglyMeasurable,
    h0 i, h0 (i + 1), sq]

private lemma variance_abs_mul_abs_le (hmeas : ∀ i, Measurable (X i))
    (hid : ∀ i, IdentDistrib (X i) Y μ μ) (hZ4 : Integrable (fun ω => Y ω ^ 4) μ)
    (i : ℕ) : variance (fun ω => |X i ω| * |X (i + 1) ω|) μ ≤ ∫ ω, Y ω ^ 4 ∂μ := by
  refine (variance_le_expectation_sq (aestronglyMeasurable_abs_mul_abs hmeas i)).trans ?_
  calc ∫ ω, ((fun ω => |X i ω| * |X (i + 1) ω|) ^ 2) ω ∂μ
      ≤ ∫ ω, (X i ω ^ 4 + X (i + 1) ω ^ 4) / 2 ∂μ := by
        refine integral_mono (integrable_sq_abs_mul_abs hmeas hid hZ4 i)
          (((integrable_pow_four hid hZ4 i).add (integrable_pow_four hid hZ4 (i + 1))).div_const 2)
          fun ω => ?_
        simp only [Pi.pow_apply]
        exact sq_abs_mul_abs_le _ _
    _ = ∫ ω, Y ω ^ 4 ∂μ := by
        rw [integral_div, integral_add (integrable_pow_four hid hZ4 i)
          (integrable_pow_four hid hZ4 (i + 1)), integral_pow_four hid i,
          integral_pow_four hid (i + 1)]
        ring

/-- **Chebyshev for separated index sets.** If no two indices of `T` are adjacent, the products
`|X i| |X (i+1)|`, `i ∈ T`, are pairwise independent, and the weighted sum deviates from its
mean by at least `ε` with probability at most `E Z₀⁴ ∑_{i ∈ T} (w i)² / ε²`. -/
private lemma measure_abs_sum_sub_ge_le (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hid : ∀ i, IdentDistrib (X i) Y μ μ) (hZ4 : Integrable (fun ω => Y ω ^ 4) μ)
    (w : ℕ → ℝ) (T : Finset ℕ) (hT : ∀ i ∈ T, ∀ j ∈ T, j ≠ i + 1) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |(∑ i ∈ T, w i * (|X i ω| * |X (i + 1) ω|)) -
        (∫ ω, |Y ω| ∂μ) ^ 2 * ∑ i ∈ T, w i|} ≤
      ENNReal.ofReal ((∫ ω, Y ω ^ 4 ∂μ) * (∑ i ∈ T, w i ^ 2) / ε ^ 2) := by
  have hXm : ∀ i, MemLp (fun ω => w i * (|X i ω| * |X (i + 1) ω|)) 2 μ := fun i =>
    (memLp_abs_mul_abs hmeas hid hZ4 i).const_mul (w i)
  have hS : MemLp (∑ i ∈ T, fun ω => w i * (|X i ω| * |X (i + 1) ω|)) 2 μ :=
    memLp_finsetSum' T fun i _ => hXm i
  have hmean : μ[∑ i ∈ T, fun ω => w i * (|X i ω| * |X (i + 1) ω|)] =
      (∫ ω, |Y ω| ∂μ) ^ 2 * ∑ i ∈ T, w i := by
    simp only [Finset.sum_apply]
    rw [integral_finsetSum T fun i _ => (hXm i).integrable one_le_two, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_abs_mul_abs hmeas hind hid i, mul_comm]
  have hpair : Set.Pairwise (T : Set ℕ) fun i j =>
      IndepFun (fun ω => w i * (|X i ω| * |X (i + 1) ω|))
        (fun ω => w j * (|X j ω| * |X (j + 1) ω|)) μ := by
    intro i hi j hj hij
    have h1 := hT i (Finset.mem_coe.1 hi) j (Finset.mem_coe.1 hj)
    have h2 := hT j (Finset.mem_coe.1 hj) i (Finset.mem_coe.1 hi)
    have hdisj : Disjoint ({i, i + 1} : Finset ℕ) {j, j + 1} := by
      simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left, Finset.mem_insert,
        Finset.mem_singleton]
      omega
    have h := hind.indepFun_finset {i, i + 1} {j, j + 1} hdisj hmeas
    have hφ : ∀ a : ℕ, Measurable fun x : ({a, a + 1} : Finset ℕ) → ℝ =>
        w a * (|x ⟨a, by simp⟩| * |x ⟨a + 1, by simp⟩|) := by
      intro a
      have h1 : Measurable fun x : ({a, a + 1} : Finset ℕ) → ℝ => |x ⟨a, by simp⟩| :=
        continuous_abs.measurable.comp (measurable_pi_apply _)
      have h2 : Measurable fun x : ({a, a + 1} : Finset ℕ) → ℝ => |x ⟨a + 1, by simp⟩| :=
        continuous_abs.measurable.comp (measurable_pi_apply _)
      exact measurable_const.mul (h1.mul h2)
    exact h.comp (hφ i) (hφ j)
  have hvar : variance (∑ i ∈ T, fun ω => w i * (|X i ω| * |X (i + 1) ω|)) μ ≤
      (∫ ω, Y ω ^ 4 ∂μ) * ∑ i ∈ T, w i ^ 2 := by
    rw [IndepFun.variance_sum (fun i _ => hXm i) hpair, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [variance_const_mul]
    nlinarith [variance_abs_mul_abs_le hmeas hid hZ4 i, sq_nonneg (w i)]
  have hcheb := meas_ge_le_variance_div_sq hS hε
  rw [hmean] at hcheb
  refine le_trans (le_of_eq ?_) (hcheb.trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right hvar (by positivity))))
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, Finset.sum_apply]

variable {Z : ℕ → ℕ → Ω → ℝ}

/-- **Bipower variation of the continuous part.** For increments `s n i * Z n i`, with each row
`Z n` independent, every `Z n i` distributed as `Z 0 0` with finite fourth moment, and
`∑_{i ≤ L n} (s n i)⁴ → 0`, the bipower variation is asymptotically
`(E|Z 0 0|)² ∑_{i < L n} |s n i| |s n (i+1)|`. -/
theorem tendstoInMeasure_bipowerVariation_sub (hmeas : ∀ n i, Measurable (Z n i))
    (hind : ∀ n, iIndepFun (Z n) μ) (hid : ∀ n i, IdentDistrib (Z n i) (Z 0 0) μ μ)
    (hZ4 : Integrable (fun ω => Z 0 0 ω ^ 4) μ) (s : ℕ → ℕ → ℝ) (L : ℕ → ℕ)
    (hs : Tendsto (fun n => ∑ i ∈ Finset.range (L n + 1), s n i ^ 4) atTop (𝓝 0)) :
    TendstoInMeasure μ (fun n ω => bipowerVariation (fun i => s n i * Z n i ω) (L n) -
      (∫ ω, |Z 0 0 ω| ∂μ) ^ 2 * ∑ i ∈ Finset.range (L n), |s n i| * |s n (i + 1)|) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hv : 0 ≤ ∫ ω, Z 0 0 ω ^ 4 ∂μ := integral_nonneg fun ω => by positivity
  have hlim : Tendsto (fun n => ENNReal.ofReal (4 * (∫ ω, Z 0 0 ω ^ 4 ∂μ) / ε ^ 2 *
      ∑ i ∈ Finset.range (L n + 1), s n i ^ 4)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => 4 * (∫ ω, Z 0 0 ω ^ 4 ∂μ) / ε ^ 2 *
        ∑ i ∈ Finset.range (L n + 1), s n i ^ 4) atTop (𝓝 0) := by
      simpa using hs.const_mul (4 * (∫ ω, Z 0 0 ω ^ 4 ∂μ) / ε ^ 2)
    simpa using ENNReal.tendsto_ofReal h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun n => ?_
  set w : ℕ → ℝ := fun i => |s n i| * |s n (i + 1)| with hw
  set Te := (Finset.range (L n)).filter Even
  set To := (Finset.range (L n)).filter fun i => ¬Even i
  have hTe : ∀ i ∈ Te, ∀ j ∈ Te, j ≠ i + 1 := by
    intro i hi j hj hji
    subst hji
    exact Nat.even_add_one.1 (Finset.mem_filter.1 hj).2 (Finset.mem_filter.1 hi).2
  have hTo : ∀ i ∈ To, ∀ j ∈ To, j ≠ i + 1 := by
    intro i hi j hj hji
    subst hji
    exact (Finset.mem_filter.1 hj).2 (Nat.even_add_one.2 (Finset.mem_filter.1 hi).2)
  have hsplit : ∀ ω, bipowerVariation (fun i => s n i * Z n i ω) (L n) -
      (∫ ω, |Z 0 0 ω| ∂μ) ^ 2 * ∑ i ∈ Finset.range (L n), w i =
      ((∑ i ∈ Te, w i * (|Z n i ω| * |Z n (i + 1) ω|)) - (∫ ω, |Z 0 0 ω| ∂μ) ^ 2 * ∑ i ∈ Te, w i) +
      ((∑ i ∈ To, w i * (|Z n i ω| * |Z n (i + 1) ω|)) -
        (∫ ω, |Z 0 0 ω| ∂μ) ^ 2 * ∑ i ∈ To, w i) := by
    intro ω
    have h1 : bipowerVariation (fun i => s n i * Z n i ω) (L n) =
        ∑ i ∈ Finset.range (L n), w i * (|Z n i ω| * |Z n (i + 1) ω|) := by
      unfold bipowerVariation
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hw, abs_mul]
      ring
    rw [h1, ← Finset.sum_filter_add_sum_filter_not (Finset.range (L n)) Even
      (fun i => w i * (|Z n i ω| * |Z n (i + 1) ω|)),
      ← Finset.sum_filter_add_sum_filter_not (Finset.range (L n)) Even w]
    ring
  have hw2 : ∑ i ∈ Finset.range (L n), w i ^ 2 ≤ ∑ i ∈ Finset.range (L n + 1), s n i ^ 4 := by
    have hterm : ∀ i ∈ Finset.range (L n), w i ^ 2 ≤ (s n i ^ 4 + s n (i + 1) ^ 4) / 2 :=
      fun i _ => sq_abs_mul_abs_le _ _
    have hs1 : ∑ i ∈ Finset.range (L n), s n i ^ 4 ≤
        ∑ i ∈ Finset.range (L n + 1), s n i ^ 4 := by
      rw [Finset.sum_range_succ]
      linarith [pow_nonneg (sq_nonneg (s n (L n))) 2, show s n (L n) ^ 4 = (s n (L n) ^ 2) ^ 2
        by ring]
    have hs2 : ∑ i ∈ Finset.range (L n), s n (i + 1) ^ 4 ≤
        ∑ i ∈ Finset.range (L n + 1), s n i ^ 4 := by
      rw [Finset.sum_range_succ']
      linarith [pow_nonneg (sq_nonneg (s n 0)) 2, show s n 0 ^ 4 = (s n 0 ^ 2) ^ 2 by ring]
    calc ∑ i ∈ Finset.range (L n), w i ^ 2
        ≤ ∑ i ∈ Finset.range (L n), (s n i ^ 4 + s n (i + 1) ^ 4) / 2 :=
          Finset.sum_le_sum hterm
      _ = ((∑ i ∈ Finset.range (L n), s n i ^ 4) +
            ∑ i ∈ Finset.range (L n), s n (i + 1) ^ 4) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
      _ ≤ _ := by linarith
  have hE := measure_abs_sum_sub_ge_le (hmeas n) (hind n) (hid n) hZ4 w Te hTe (half_pos hε)
  have hO := measure_abs_sum_sub_ge_le (hmeas n) (hind n) (hid n) hZ4 w To hTo (half_pos hε)
  calc μ {x | ε ≤ ‖bipowerVariation (fun i => s n i * Z n i x) (L n) -
        (∫ ω, |Z 0 0 ω| ∂μ) ^ 2 * ∑ i ∈ Finset.range (L n), |s n i| * |s n (i + 1)| -
        (0 : Ω → ℝ) x‖}
      ≤ μ ({ω | ε / 2 ≤ |(∑ i ∈ Te, w i * (|Z n i ω| * |Z n (i + 1) ω|)) -
            (∫ ω, |Z 0 0 ω| ∂μ) ^ 2 * ∑ i ∈ Te, w i|} ∪
          {ω | ε / 2 ≤ |(∑ i ∈ To, w i * (|Z n i ω| * |Z n (i + 1) ω|)) -
            (∫ ω, |Z 0 0 ω| ∂μ) ^ 2 * ∑ i ∈ To, w i|}) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω
        rw [← hw, hsplit ω] at hω
        by_contra hcon
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hcon
        linarith [abs_add_le
          ((∑ i ∈ Te, w i * (|Z n i ω| * |Z n (i + 1) ω|)) -
            (∫ ω, |Z 0 0 ω| ∂μ) ^ 2 * ∑ i ∈ Te, w i)
          ((∑ i ∈ To, w i * (|Z n i ω| * |Z n (i + 1) ω|)) -
            (∫ ω, |Z 0 0 ω| ∂μ) ^ 2 * ∑ i ∈ To, w i)]
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((∫ ω, Z 0 0 ω ^ 4 ∂μ) * (∑ i ∈ Te, w i ^ 2) / (ε / 2) ^ 2) +
          ENNReal.ofReal ((∫ ω, Z 0 0 ω ^ 4 ∂μ) * (∑ i ∈ To, w i ^ 2) / (ε / 2) ^ 2) :=
        add_le_add hE hO
    _ = ENNReal.ofReal ((∫ ω, Z 0 0 ω ^ 4 ∂μ) * (∑ i ∈ Finset.range (L n), w i ^ 2) /
          (ε / 2) ^ 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_div, ← mul_add,
          Finset.sum_filter_add_sum_filter_not]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hε2 : (ε / 2) ^ 2 = ε ^ 2 / 4 := by ring
        rw [hε2, div_div_eq_mul_div,
          show 4 * (∫ ω, Z 0 0 ω ^ 4 ∂μ) / ε ^ 2 * ∑ i ∈ Finset.range (L n + 1), s n i ^ 4 =
            (∫ ω, Z 0 0 ω ^ 4 ∂μ) * (∑ i ∈ Finset.range (L n + 1), s n i ^ 4) * 4 / ε ^ 2 by ring]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hw2 hv) (by norm_num)) (by positivity)

/-- **The largest continuous increment tends to `0`.** For increments `s n i * Z n i` with every
`Z n i` distributed as `Z 0 0` with finite fourth moment and `∑_{i ≤ L n} (s n i)⁴ → 0`, the
largest of `|s n i * Z n i|`, `i ≤ L n`, tends to `0` in probability. -/
theorem tendstoInMeasure_sup_abs_mul (hid : ∀ n i, IdentDistrib (Z n i) (Z 0 0) μ μ)
    (hZ4 : Integrable (fun ω => Z 0 0 ω ^ 4) μ) (s : ℕ → ℕ → ℝ) (L : ℕ → ℕ)
    (hs : Tendsto (fun n => ∑ i ∈ Finset.range (L n + 1), s n i ^ 4) atTop (𝓝 0)) :
    TendstoInMeasure μ (fun n ω => (Finset.range (L n + 1)).sup' Finset.nonempty_range_add_one
      fun i => |s n i * Z n i ω|) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hlim : Tendsto (fun n => ENNReal.ofReal ((∫ ω, Z 0 0 ω ^ 4 ∂μ) / ε ^ 4 *
      ∑ i ∈ Finset.range (L n + 1), s n i ^ 4)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => (∫ ω, Z 0 0 ω ^ 4 ∂μ) / ε ^ 4 *
        ∑ i ∈ Finset.range (L n + 1), s n i ^ 4) atTop (𝓝 0) := by
      simpa using hs.const_mul ((∫ ω, Z 0 0 ω ^ 4 ∂μ) / ε ^ 4)
    simpa using ENNReal.tendsto_ofReal h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun n => ?_
  calc μ {x | ε ≤ ‖(Finset.range (L n + 1)).sup' Finset.nonempty_range_add_one
        (fun i => |s n i * Z n i x|) - (0 : Ω → ℝ) x‖}
      ≤ μ (⋃ i ∈ Finset.range (L n + 1), {ω | ε ^ 4 ≤ s n i ^ 4 * Z n i ω ^ 4}) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω
        have h0 : 0 ≤ (Finset.range (L n + 1)).sup' Finset.nonempty_range_add_one
            (fun i => |s n i * Z n i ω|) :=
          (abs_nonneg _).trans (Finset.le_sup' (fun i => |s n i * Z n i ω|)
            (Finset.mem_range.2 (Nat.succ_pos _)))
        rw [abs_of_nonneg h0] at hω
        obtain ⟨i, hi, hle⟩ := (Finset.le_sup'_iff _).1 hω
        refine Set.mem_iUnion₂.2 ⟨i, hi, ?_⟩
        calc ε ^ 4 ≤ |s n i * Z n i ω| ^ 4 := pow_le_pow_left₀ hε.le hle 4
          _ = s n i ^ 4 * Z n i ω ^ 4 := by rw [Even.pow_abs ⟨2, rfl⟩, mul_pow]
    _ ≤ ∑ i ∈ Finset.range (L n + 1), μ {ω | ε ^ 4 ≤ s n i ^ 4 * Z n i ω ^ 4} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ Finset.range (L n + 1),
          ENNReal.ofReal ((∫ ω, s n i ^ 4 * Z n i ω ^ 4 ∂μ) / ε ^ 4) :=
        Finset.sum_le_sum fun i _ => measure_ge_le_ofReal_integral_div
          (ae_of_all _ fun ω => by positivity) ((integrable_pow_four (hid n) hZ4 i).const_mul _)
          (by positivity)
    _ = ENNReal.ofReal (∑ i ∈ Finset.range (L n + 1),
          (∫ ω, s n i ^ 4 * Z n i ω ^ 4 ∂μ) / ε ^ 4) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ =>
          div_nonneg (integral_nonneg fun ω => by positivity) (by positivity)).symm
    _ = _ := by
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul, integral_pow_four (hid n) i]
        ring

/-- **Convergence of bipower variation in the presence of jumps.** Let the continuous increments
be `s n i * Z n i`, with each row `Z n` independent and every `Z n i` distributed as `Z 0 0`
with finite fourth moment, `∑_{i ≤ L n} (s n i)⁴ → 0` and
`∑_{i < L n} |s n i| |s n (i+1)| → V`, and add the increments of `K` random jumps of sizes `ξ k`
at a.s. distinct times `τ k`. Then the bipower variation tends to `(E|Z 0 0|)² V` in probability:
the jumps do not contribute. -/
theorem tendstoInMeasure_bipowerVariation_add_jump (hmeas : ∀ n i, Measurable (Z n i))
    (hind : ∀ n, iIndepFun (Z n) μ) (hid : ∀ n i, IdentDistrib (Z n i) (Z 0 0) μ μ)
    (hZ4 : Integrable (fun ω => Z 0 0 ω ^ 4) μ) (s : ℕ → ℕ → ℝ) (L : ℕ → ℕ)
    (hs : Tendsto (fun n => ∑ i ∈ Finset.range (L n + 1), s n i ^ 4) atTop (𝓝 0)) {V : ℝ}
    (hV : Tendsto (fun n => ∑ i ∈ Finset.range (L n), |s n i| * |s n (i + 1)|) atTop (𝓝 V))
    {K : Ω → ℕ} {τ ξ : ℕ → Ω → ℝ} (hK : Measurable K) (hτ : ∀ k, Measurable (τ k))
    (hξ : ∀ k, Measurable (ξ k))
    (hinj : ∀ᵐ ω ∂μ, Set.InjOn (fun k => τ k ω) (Finset.range (K ω))) :
    TendstoInMeasure μ (fun n ω => bipowerVariation (fun i => s n i * Z n i ω +
        jumpIncrement (Finset.range (K ω)) (fun k => τ k ω) (fun k => ξ k ω) n i) (L n))
      atTop (fun _ => (∫ ω, |Z 0 0 ω| ∂μ) ^ 2 * V) := by
  have h1 := tendstoInMeasure_bipowerVariation_add_jump_sub (fun n i ω => s n i * Z n i ω) L
    (tendstoInMeasure_sup_abs_mul hid hZ4 s L hs) hK hτ hξ hinj
  have h2 := tendstoInMeasure_bipowerVariation_sub hmeas hind hid hZ4 s L hs
  have h3 : TendstoInMeasure μ (fun n (_ : Ω) => (∫ ω, |Z 0 0 ω| ∂μ) ^ 2 *
      ∑ i ∈ Finset.range (L n), |s n i| * |s n (i + 1)|) atTop
      (fun _ => (∫ ω, |Z 0 0 ω| ∂μ) ^ 2 * V) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => hV.const_mul _)
  refine (tendstoInMeasure_add (tendstoInMeasure_add h1 h2) h3).congr
    (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
  · simp only
    ring
  · simp

/-- **Constant volatility.** On the grid of mesh `1/n` of `[0, 1]`, with continuous increments
`σ / √n * Z n i` (each row `Z n` i.i.d. with the law of `Z 0 0`, finite fourth moment) plus
finitely many jumps at a.s. distinct times, the bipower variation over the `n` increments tends
to `(E|Z 0 0|)² σ²` in probability. -/
theorem tendstoInMeasure_bipowerVariation_add_jump_const (hmeas : ∀ n i, Measurable (Z n i))
    (hind : ∀ n, iIndepFun (Z n) μ) (hid : ∀ n i, IdentDistrib (Z n i) (Z 0 0) μ μ)
    (hZ4 : Integrable (fun ω => Z 0 0 ω ^ 4) μ) (σ : ℝ)
    {K : Ω → ℕ} {τ ξ : ℕ → Ω → ℝ} (hK : Measurable K) (hτ : ∀ k, Measurable (τ k))
    (hξ : ∀ k, Measurable (ξ k))
    (hinj : ∀ᵐ ω ∂μ, Set.InjOn (fun k => τ k ω) (Finset.range (K ω))) :
    TendstoInMeasure μ (fun (n : ℕ) ω => bipowerVariation (fun i => σ / Real.sqrt n * Z n i ω +
        jumpIncrement (Finset.range (K ω)) (fun k => τ k ω) (fun k => ξ k ω) n i) (n - 1))
      atTop (fun _ => (∫ ω, |Z 0 0 ω| ∂μ) ^ 2 * σ ^ 2) := by
  have hsq : ∀ n : ℕ, (σ / Real.sqrt n) ^ 2 = σ ^ 2 / n := fun n => by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  refine tendstoInMeasure_bipowerVariation_add_jump hmeas hind hid hZ4
    (fun n _ => σ / Real.sqrt n) (fun n => n - 1) ?_ ?_ hK hτ hξ hinj
  · refine (tendsto_const_div_atTop_nhds_zero_nat (σ ^ 4)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    rw [Finset.sum_const, Finset.card_range, Nat.sub_add_cancel hn, nsmul_eq_mul,
      show (σ / Real.sqrt n) ^ 4 = ((σ / Real.sqrt n) ^ 2) ^ 2 by ring, hsq]
    field_simp
  · have := (tendsto_const_nhds (x := σ ^ 2)).sub (tendsto_const_div_atTop_nhds_zero_nat (σ ^ 2))
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, abs_mul_abs_self, ← sq, hsq,
      Nat.cast_sub hn, Nat.cast_one]
    field_simp

/-- `∫₀^∞ x e^{-x²/2} dx = 1`. -/
private lemma integral_Ioi_mul_exp_neg_half_sq :
    ∫ x in Ioi (0 : ℝ), x * Real.exp (-(1 / 2) * x ^ 2) = 1 := by
  have h := integral_mul_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)
  have h2 : ∫ r : ℝ in Ioi 0, (r : ℂ) * Complex.exp (-(1 / 2 : ℂ) * (r : ℂ) ^ 2) =
      ((∫ r in Ioi (0 : ℝ), r * Real.exp (-(1 / 2) * r ^ 2) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    push_cast
    ring_nf
  have h3 : ((∫ r in Ioi (0 : ℝ), r * Real.exp (-(1 / 2) * r ^ 2) : ℝ) : ℂ) = 1 := by
    rw [← h2, h]
    norm_num
  exact_mod_cast h3

/-- **`E|N(0,1)| = √(2/π)`.** -/
theorem integral_abs_gaussianReal : ∫ x, |x| ∂(gaussianReal 0 1) = Real.sqrt (2 / Real.pi) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  let f : ℝ → ℝ := fun y => (Real.sqrt (2 * Real.pi))⁻¹ * (y * Real.exp (-(1 / 2) * y ^ 2))
  have hf : (fun x : ℝ => gaussianPDFReal 0 1 x • |x|) = fun x => f |x| := by
    funext x
    simp only [f, gaussianPDFReal_def, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero, sq_abs]
    rw [show -x ^ 2 / 2 = -(1 / 2) * x ^ 2 by ring]
    ring
  rw [hf, integral_comp_abs]
  simp only [f]
  rw [integral_const_mul, integral_Ioi_mul_exp_neg_half_sq, mul_one]
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [show (2 : ℝ) / Real.pi = 4 / (2 * Real.pi) by
      rw [div_eq_div_iff (by positivity) (by positivity)]; ring, Real.sqrt_div' _
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- **Brownian increments with jumps.** On the grid of mesh `1/n` of `[0, 1]`, with continuous
increments `σ / √n * Z n i`, where each row `Z n` is i.i.d. standard Gaussian (for a Brownian
motion `W`, `Z n i = √n (W_{(i+1)/n} - W_{i/n})`, so the increments are those of `σ W`), plus
finitely many jumps at a.s. distinct times, which may depend on `W`, the bipower variation tends
to `(2/π) σ²` in probability: `(π/2) BPV` estimates the integrated variance `σ²` and ignores the
jumps. -/
theorem tendstoInMeasure_bipowerVariation_add_jump_gaussian (hmeas : ∀ n i, Measurable (Z n i))
    (hind : ∀ n, iIndepFun (Z n) μ) (hgauss : ∀ n i, μ.map (Z n i) = gaussianReal 0 1) (σ : ℝ)
    {K : Ω → ℕ} {τ ξ : ℕ → Ω → ℝ} (hK : Measurable K) (hτ : ∀ k, Measurable (τ k))
    (hξ : ∀ k, Measurable (ξ k))
    (hinj : ∀ᵐ ω ∂μ, Set.InjOn (fun k => τ k ω) (Finset.range (K ω))) :
    TendstoInMeasure μ (fun (n : ℕ) ω => bipowerVariation (fun i => σ / Real.sqrt n * Z n i ω +
        jumpIncrement (Finset.range (K ω)) (fun k => τ k ω) (fun k => ξ k ω) n i) (n - 1))
      atTop (fun _ => 2 / Real.pi * σ ^ 2) := by
  have hid : ∀ n i, IdentDistrib (Z n i) (Z 0 0) μ μ := fun n i =>
    ⟨(hmeas n i).aemeasurable, (hmeas 0 0).aemeasurable, by rw [hgauss n i, hgauss 0 0]⟩
  have hZ4 : Integrable (fun ω => Z 0 0 ω ^ 4) μ := by
    have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) ((4 : ℕ) : ℝ≥0∞)
      (ENNReal.natCast_ne_top 4)).integrable_norm_pow (by norm_num)
    rw [← hgauss 0 0] at h
    refine ((integrable_map_measure h.aestronglyMeasurable (hmeas 0 0).aemeasurable).1 h).congr
      (ae_of_all _ fun ω => ?_)
    simp only [Function.comp, id, Real.norm_eq_abs]
    exact Even.pow_abs ⟨2, rfl⟩ _
  have hm : ∫ ω, |Z 0 0 ω| ∂μ = Real.sqrt (2 / Real.pi) := by
    rw [← integral_abs_gaussianReal, ← hgauss 0 0,
      integral_map (hmeas 0 0).aemeasurable continuous_abs.aestronglyMeasurable]
  have := tendstoInMeasure_bipowerVariation_add_jump_const hmeas hind hid hZ4 σ hK hτ hξ hinj
  rwa [hm, Real.sq_sqrt (by positivity)] at this

end Continuous

end

end MathlibExt.Probability.Martingale
