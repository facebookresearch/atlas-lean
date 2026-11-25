/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Order.Monotone.Basic

/-!
# Effective ranks of a covariance operator

Bartlett, Long, Lugosi and Tsigler (*Benign overfitting in linear regression*, PNAS 117, 2020,
arXiv:1906.11300) characterize when the minimum-norm interpolating estimator in linear
regression predicts well through two effective ranks of the covariance `Σ`, defined from its
eigenvalues `λ₁ ≥ λ₂ ≥ ⋯ ≥ 0` with `∑ λᵢ < ∞` (their Definition 3): for `k ≥ 0` with
`λ_{k+1} > 0`,

`r_k(Σ) = (∑_{i>k} λᵢ) / λ_{k+1}`,   `R_k(Σ) = (∑_{i>k} λᵢ)² / ∑_{i>k} λᵢ²`.

Here the eigenvalues are a sequence `ev : ℕ → ℝ` indexed from `0`, so `ev j = λ_{j+1}`, the
tail `∑_{i>k} λᵢ` is `∑' j, ev (j + k)` and `λ_{k+1}` is `ev k`. The effective ranks of `Σ²`
are those of the squared sequence.

Main results (their Lemma 5), for a nonnegative, antitone, summable `ev` with `ev k > 0`:

* `one_le_effRank`: `1 ≤ r_k(Σ)`;
* `effRank_sq_eq`: `r_k(Σ)² = r_k(Σ²) R_k(Σ)`;
* `effRank_sq_le_effRank`, `effRank_le_effRankLarge`, `effRankLarge_le_effRank_sq`:
  `r_k(Σ²) ≤ r_k(Σ) ≤ R_k(Σ) ≤ r_k(Σ)²`.

All of them follow from three facts about the tail: its sum is at least its first term
`λ_{k+1}`, its sum of squares is at least `λ_{k+1}²`, and its sum of squares is at most
`λ_{k+1}` times its sum (because every tail eigenvalue is at most `λ_{k+1}`).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.EffectiveRank

/-- The **effective rank** `r_k(Σ) = (∑_{i>k} λᵢ) / λ_{k+1}` of a covariance with eigenvalues
`ev 0 ≥ ev 1 ≥ ⋯` (so `ev j = λ_{j+1}`); Bartlett, Long, Lugosi and Tsigler, *Benign
overfitting in linear regression*, Definition 3. It is the effective rank for a nonnegative
summable spectrum with `λ_{k+1} > 0`, the hypotheses of the results below. Outside that range
the value is a totalised ratio: an infinite trace is read as `0` by `tsum`, and `λ_{k+1} = 0`
gives `0` (`x / 0 = 0`). -/
noncomputable def effRank (ev : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑' j, ev (j + k)) / ev k

/-- The **large effective rank** `R_k(Σ) = (∑_{i>k} λᵢ)² / ∑_{i>k} λᵢ²` of a covariance with
eigenvalues `ev 0 ≥ ev 1 ≥ ⋯`; Bartlett, Long, Lugosi and Tsigler, *Benign overfitting in
linear regression*, Definition 3. As for `effRank`, it is the large effective rank for a
nonnegative summable spectrum that does not vanish beyond `k`; otherwise the value is a
totalised ratio (a non-summable tail is read as `0`, and a zero tail gives `0 / 0 = 0`). -/
noncomputable def effRankLarge (ev : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑' j, ev (j + k)) ^ 2 / ∑' j, ev (j + k) ^ 2

variable {ev : ℕ → ℝ} {k : ℕ}

section Tail

variable (h0 : ∀ j, 0 ≤ ev j) (hanti : Antitone ev) (hs : Summable ev)
include h0 hanti hs

omit h0 hanti in
lemma summable_tail : Summable fun j => ev (j + k) := (summable_nat_add_iff k).2 hs

omit hs in
lemma sq_tail_le (j : ℕ) : ev (j + k) ^ 2 ≤ ev k * ev (j + k) := by
  rw [sq]
  exact mul_le_mul_of_nonneg_right (hanti (Nat.le_add_left k j)) (h0 _)

lemma summable_sq_tail : Summable fun j => ev (j + k) ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (sq_tail_le h0 hanti)
    ((summable_tail hs).mul_left (ev k))

/-- The tail sum of squares is at most `λ_{k+1}` times the tail sum. -/
lemma tsum_sq_tail_le : ∑' j, ev (j + k) ^ 2 ≤ ev k * ∑' j, ev (j + k) := by
  rw [← tsum_mul_left]
  exact (summable_sq_tail h0 hanti hs).tsum_le_tsum (sq_tail_le h0 hanti)
    ((summable_tail hs).mul_left _)

omit hanti in
/-- The tail sum is at least its first term `λ_{k+1}`. -/
lemma le_tsum_tail : ev k ≤ ∑' j, ev (j + k) := by
  have := (summable_tail hs (k := k)).le_tsum 0 (fun j _ => h0 _)
  simpa using this

/-- The tail sum of squares is at least `λ_{k+1}²`. -/
lemma sq_le_tsum_sq_tail : ev k ^ 2 ≤ ∑' j, ev (j + k) ^ 2 := by
  have := (summable_sq_tail h0 hanti hs (k := k)).le_tsum 0 (fun j _ => sq_nonneg _)
  simpa using this

end Tail

variable (h0 : ∀ j, 0 ≤ ev j) (hanti : Antitone ev) (hs : Summable ev) (hk : 0 < ev k)
include h0 hanti hs hk

omit hanti in
/-- `1 ≤ r_k(Σ)` (Bartlett, Long, Lugosi and Tsigler, Lemma 5); monotonicity of the
eigenvalues is not needed. -/
theorem one_le_effRank : 1 ≤ effRank ev k := by
  rw [effRank, le_div_iff₀ hk, one_mul]
  exact le_tsum_tail h0 hs

/-- `r_k(Σ)² = r_k(Σ²) R_k(Σ)` (Bartlett, Long, Lugosi and Tsigler, Lemma 5). -/
theorem effRank_sq_eq :
    effRank ev k ^ 2 = effRank (fun j => ev j ^ 2) k * effRankLarge ev k := by
  have hS2 : 0 < ∑' j, ev (j + k) ^ 2 :=
    lt_of_lt_of_le (by positivity) (sq_le_tsum_sq_tail h0 hanti hs)
  simp only [effRank, effRankLarge]
  field_simp

/-- `r_k(Σ²) ≤ r_k(Σ)` (Bartlett, Long, Lugosi and Tsigler, Lemma 5). -/
theorem effRank_sq_le_effRank : effRank (fun j => ev j ^ 2) k ≤ effRank ev k := by
  simp only [effRank]
  rw [div_le_div_iff₀ (by positivity) hk]
  have := tsum_sq_tail_le h0 hanti hs (k := k)
  nlinarith

/-- `r_k(Σ) ≤ R_k(Σ)` (Bartlett, Long, Lugosi and Tsigler, Lemma 5). -/
theorem effRank_le_effRankLarge : effRank ev k ≤ effRankLarge ev k := by
  have hS2 : 0 < ∑' j, ev (j + k) ^ 2 :=
    lt_of_lt_of_le (by positivity) (sq_le_tsum_sq_tail h0 hanti hs)
  have hS1 : 0 ≤ ∑' j, ev (j + k) := tsum_nonneg fun j => h0 _
  simp only [effRank, effRankLarge]
  rw [div_le_div_iff₀ hk hS2]
  have := tsum_sq_tail_le h0 hanti hs (k := k)
  nlinarith [mul_le_mul_of_nonneg_left this hS1]

/-- `R_k(Σ) ≤ r_k(Σ)²` (Bartlett, Long, Lugosi and Tsigler, Lemma 5). -/
theorem effRankLarge_le_effRank_sq : effRankLarge ev k ≤ effRank ev k ^ 2 := by
  have hS2 : 0 < ∑' j, ev (j + k) ^ 2 :=
    lt_of_lt_of_le (by positivity) (sq_le_tsum_sq_tail h0 hanti hs)
  simp only [effRank, effRankLarge, div_pow]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    (sq_le_tsum_sq_tail h0 hanti hs)

end Cslib.MachineLearning.EffectiveRank
