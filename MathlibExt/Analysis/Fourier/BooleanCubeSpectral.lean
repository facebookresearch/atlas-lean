/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCubeBLR
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Spectral structure of Boolean functions

Elementary facts relating the Fourier spectrum of `f : BoolCube n → ℝ` to its influences, degree
and sign, from Chapters 2, 3 and 5 of O'Donnell's book. The degree-`> t` Fourier weight is
`W^{>t}[f] = ∑_{|S| > t} f̂(S)²`; the spectrum of `f` is `ε`-concentrated on degree up to `t`
when `W^{>t}[f] ≤ ε` (Definition 3.1).

## Main statements

* `BooleanCube.sum_sq_card_gt_le`: `W^{>t}[f] ≤ I[f] / t` for `t > 0`.
* `BooleanCube.sum_sq_card_gt_le_of_pos`: Proposition 3.2, the spectrum is `ε`-concentrated on
  degree up to `I[f]/ε`.
* `BooleanCube.boolTotalInfluence_le_degree`: Fact 3.7, `I[f] ≤ deg(f)` for Boolean `f`.
* `BooleanCube.boolDist_le_expect_sq_sub`: Proposition 3.31, rounding `g` to its sign costs at
  most `‖f - g‖₂²` in distance.
* `BooleanCube.boolInfluence_eq_boolFourierCoeff_of_monotone`: Proposition 2.21, a monotone
  Boolean function has `Inf_i[f] = f̂({i})`.
* `BooleanCube.eq_of_boolFourierCoeff_eq_of_ltf`: Theorem 5.1 (Chow), a linear threshold
  function is determined among Boolean functions by its Fourier coefficients of degree `≤ 1`.

## References

* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014
  (arXiv:2105.10386), Proposition 2.21, Definition 3.1, Proposition 3.2, Fact 3.7,
  Proposition 3.31 and Theorem 5.1.
* C. K. Chow, "On the characterization of threshold functions", Proc. 2nd FOCS (1961), 34-38.
-/

@[expose] public section

namespace BooleanCube

open scoped BigOperators

variable {n : ℕ}

/-- **Markov bound for high-degree Fourier weight.** For every `f : BoolCube n → ℝ` and real
`t > 0`, `∑_{|S| > t} f̂(S)² ≤ I[f] / t` (R. O'Donnell, *Analysis of Boolean Functions*, 2014,
proof of Proposition 3.2 from Theorem 2.38). -/
theorem sum_sq_card_gt_le (f : BoolCube n → ℝ) {t : ℝ} (ht : 0 < t) :
    ∑ S with t < (S.card : ℝ), boolFourierCoeff n f S ^ 2 ≤ boolTotalInfluence f / t := by
  rw [boolTotalInfluence_eq_sum_card_mul_sq, le_div_iff₀ ht, Finset.sum_mul]
  calc ∑ S with t < (S.card : ℝ), boolFourierCoeff n f S ^ 2 * t
      ≤ ∑ S with t < (S.card : ℝ), (S.card : ℝ) * boolFourierCoeff n f S ^ 2 :=
        Finset.sum_le_sum fun S hS => by
          have h := (Finset.mem_filter.mp hS).2
          nlinarith [sq_nonneg (boolFourierCoeff n f S)]
    _ ≤ ∑ S, (S.card : ℝ) * boolFourierCoeff n f S ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun S _ _ => by positivity

/-- **Low total influence implies low-degree spectral concentration.** For every
`f : BoolCube n → ℝ` and `ε > 0`, the Fourier spectrum of `f` is `ε`-concentrated on degree up to
`I[f]/ε`: `∑_{|S| > I[f]/ε} f̂(S)² ≤ ε` (R. O'Donnell, *Analysis of Boolean Functions*, 2014,
Proposition 3.2). -/
theorem sum_sq_card_gt_le_of_pos (f : BoolCube n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∑ S with boolTotalInfluence f / ε < (S.card : ℝ), boolFourierCoeff n f S ^ 2 ≤ ε := by
  rcases (boolTotalInfluence_nonneg f).eq_or_lt with h0 | hpos
  · -- `I[f] = 0`: all the weight above degree `0` vanishes.
    have hz : ∀ S : Finset (Fin n), (S.card : ℝ) * boolFourierCoeff n f S ^ 2 = 0 := by
      have hsum := boolTotalInfluence_eq_sum_card_mul_sq f
      rw [← h0] at hsum
      exact fun S => (Finset.sum_eq_zero_iff_of_nonneg (fun T _ => by positivity)).mp
        hsum.symm S (Finset.mem_univ S)
    rw [← h0, zero_div]
    refine le_of_eq_of_le (Finset.sum_eq_zero fun S hS => ?_) hε.le
    have hc : (0 : ℝ) < S.card := (Finset.mem_filter.mp hS).2
    rcases mul_eq_zero.mp (hz S) with h | h
    · exact absurd h hc.ne'
    · exact h
  · have h := sum_sq_card_gt_le f (div_pos hpos hε)
    refine h.trans_eq ?_
    field_simp

/-- **Total influence is at most the degree.** If `f : BoolCube n → ℝ` takes values `±1` and has
degree at most `d`, then `I[f] ≤ d` (R. O'Donnell, *Analysis of Boolean Functions*, 2014,
Fact 3.7). -/
theorem boolTotalInfluence_le_degree {f : BoolCube n → ℝ} (hf : ∀ x, f x = 1 ∨ f x = -1)
    {d : ℕ} (hd : MultilinearDegreeLE n f d) : boolTotalInfluence f ≤ d := by
  have hsq : ∑ S, boolFourierCoeff n f S ^ 2 = 1 := by
    rw [← expect_sq_eq_sum_boolFourierCoeff_sq]
    have h1 : ∀ x, f x ^ 2 = 1 := fun x => by rcases hf x with h | h <;> simp [h]
    simp [h1]
  rw [boolTotalInfluence_eq_sum_card_mul_sq]
  calc ∑ S, (S.card : ℝ) * boolFourierCoeff n f S ^ 2
      ≤ ∑ S, (d : ℝ) * boolFourierCoeff n f S ^ 2 := Finset.sum_le_sum fun S _ => by
        by_cases hS : d < S.card
        · simp [hd S hS]
        · have : (S.card : ℝ) ≤ d := by exact_mod_cast not_lt.mp hS
          exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    _ = d := by rw [← Finset.mul_sum, hsq, mul_one]

/-- **Rounding to the sign.** Let `f : BoolCube n → ℝ` take values `±1` and `g : BoolCube n → ℝ`
be arbitrary, and let `h` take values `±1` with `h(x) g(x) ≥ 0` for all `x` (that is,
`h = sgn(g)`, with `sgn(0)` chosen arbitrarily). Then `dist(f, h) ≤ ‖f - g‖₂²`
(R. O'Donnell, *Analysis of Boolean Functions*, 2014, Proposition 3.31). -/
theorem boolDist_le_expect_sq_sub {f g h : BoolCube n → ℝ} (hf : ∀ x, f x = 1 ∨ f x = -1)
    (hh : ∀ x, h x = 1 ∨ h x = -1) (hhg : ∀ x, 0 ≤ h x * g x) :
    boolDist f h ≤ 𝔼 x, (f x - g x) ^ 2 := by
  refine Finset.expect_le_expect fun x _ => ?_
  split_ifs with hne
  · have hfx : f x = -h x := by
      rcases hf x with h1 | h1 <;> rcases hh x with h2 | h2 <;> simp_all
    have hh2 : h x ^ 2 = 1 := by rcases hh x with h2 | h2 <;> simp [h2]
    rw [hfx]
    nlinarith [hhg x, sq_nonneg (g x)]
  · positivity

/-- **Influences of a monotone Boolean function.** If `f : BoolCube n → ℝ` takes values `±1` and
is monotone (`f x ≤ f y` whenever `x ≤ y` coordinatewise, with `false < true`, i.e. `-1 < 1`),
then `Inf_i[f] = f̂({i})` for every coordinate `i` (R. O'Donnell, *Analysis of Boolean
Functions*, 2014, Proposition 2.21). -/
theorem boolInfluence_eq_boolFourierCoeff_of_monotone {f : BoolCube n → ℝ}
    (hf : ∀ x, f x = 1 ∨ f x = -1) (hmono : Monotone f) (i : Fin n) :
    boolInfluence f i = boolFourierCoeff n f {i} := by
  -- Pointwise, `((f x - f x^i)/2)² = ((f x - f x^i)/2) x_i` by monotonicity.
  have hpt : ∀ x : BoolCube n,
      ((f x - f (flipCoord x i)) / 2) ^ 2 = (f x - f (flipCoord x i)) / 2 * cubeVal (x i) := by
    intro x
    have hle : ∀ y : BoolCube n, y i = false → f y ≤ f (flipCoord y i) := by
      intro y hy
      refine hmono fun j => ?_
      by_cases hj : j = i
      · subst hj
        simp [hy]
      · simp [flipCoord_apply_of_ne _ hj]
    cases hxi : x i
    · have h := hle x hxi
      rw [cubeVal_false]
      rcases hf x with h1 | h1 <;> rcases hf (flipCoord x i) with h2 | h2 <;>
        (try rw [h1, h2] at h ⊢) <;> linarith
    · have h := hle (flipCoord x i) (by simp [hxi])
      rw [flipCoord_flipCoord] at h
      rw [cubeVal_true]
      rcases hf x with h1 | h1 <;> rcases hf (flipCoord x i) with h2 | h2 <;>
        (try rw [h1, h2] at h ⊢) <;> linarith
  -- `𝔼[f x^i x_i] = -𝔼[f x x_i]`, by the flip symmetry of the uniform average.
  have hflip : 𝔼 x, f (flipCoord x i) * cubeVal (x i) = -𝔼 x, f x * cubeVal (x i) := by
    have h := expect_comp_flipCoord (fun x => f x * cubeVal (x i)) i
    simp only [flipCoord_apply_self, cubeVal_not] at h
    rw [← h, ← Finset.expect_neg_distrib]
    refine Finset.expect_congr rfl fun x _ => ?_
    ring
  rw [boolInfluence, Finset.expect_congr rfl fun x _ => hpt x, boolFourierCoeff_eq_expect]
  simp only [cubeChi_singleton]
  have hsplit : ∀ x : BoolCube n, (f x - f (flipCoord x i)) / 2 * cubeVal (x i) =
      (1 / 2) * (f x * cubeVal (x i)) - (1 / 2) * (f (flipCoord x i) * cubeVal (x i)) :=
    fun x => by ring
  simp_rw [hsplit, Finset.expect_sub_distrib, ← Finset.mul_expect, hflip]
  ring

/-- **Chow's theorem.** Let `f : BoolCube n → ℝ` be a linear threshold function, written as
`f = sgn(ℓ)` for some `ℓ` of degree at most `1` that never vanishes (so `f(x) ℓ(x) > 0` for all
`x`), and let `g : BoolCube n → ℝ` take values `±1`. If `ĝ(S) = f̂(S)` for all `|S| ≤ 1`, then
`g = f` (C. K. Chow, 1961; R. O'Donnell, *Analysis of Boolean Functions*, 2014, Theorem 5.1, whose
proof uses this normalization of `ℓ`). -/
theorem eq_of_boolFourierCoeff_eq_of_ltf {f g ℓ : BoolCube n → ℝ}
    (hℓ : MultilinearDegreeLE n ℓ 1) (hfℓ : ∀ x, 0 < f x * ℓ x) (hf : ∀ x, f x = 1 ∨ f x = -1)
    (hg : ∀ x, g x = 1 ∨ g x = -1)
    (hcoeff : ∀ S : Finset (Fin n), S.card ≤ 1 → boolFourierCoeff n g S = boolFourierCoeff n f S) :
    g = f := by
  -- Plancherel: `𝔼[f ℓ] = 𝔼[g ℓ]`, since `ℓ` has no weight above degree `1`.
  have hcorr : 𝔼 x, f x * ℓ x = 𝔼 x, g x * ℓ x := by
    rw [expect_mul_eq_sum_boolFourierCoeff_mul, expect_mul_eq_sum_boolFourierCoeff_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hS : 1 < S.card
    · simp [hℓ S hS]
    · rw [hcoeff S (not_lt.mp hS)]
  -- Pointwise `g ℓ ≤ f ℓ = |ℓ|`.
  have hle : ∀ x, g x * ℓ x ≤ f x * ℓ x := fun x => by
    have := hfℓ x
    rcases hf x with h1 | h1 <;> rcases hg x with h2 | h2 <;> simp_all <;> linarith
  have hzero : ∀ x ∈ (Finset.univ : Finset (BoolCube n)), f x * ℓ x - g x * ℓ x = 0 := by
    have hsum : ∑ x, (f x * ℓ x - g x * ℓ x) = 0 := by
      have h := congrArg (fun t => t * (Fintype.card (BoolCube n) : ℝ)) hcorr
      simp only [Fintype.expect_eq_sum_div_card] at h
      have hc : (Fintype.card (BoolCube n) : ℝ) ≠ 0 := by positivity
      rw [div_mul_cancel₀ _ hc, div_mul_cancel₀ _ hc] at h
      rw [Finset.sum_sub_distrib, h, sub_self]
    exact (Finset.sum_eq_zero_iff_of_nonneg fun x _ => sub_nonneg.mpr (hle x)).mp hsum
  funext x
  have hx := hzero x (Finset.mem_univ x)
  have hℓx : ℓ x ≠ 0 := fun h => by simpa [h] using hfℓ x
  have : (f x - g x) * ℓ x = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h hℓx

end BooleanCube
