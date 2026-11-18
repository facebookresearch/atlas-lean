/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DirichletForm.SpectralGap
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The log-Sobolev constant is at most half the spectral gap

For a finite chain with stochastic matrix `P` and positive probability vector `π`,
`2 α(P, π) ≤ λ(P, π)` (P. Diaconis and L. Saloff-Coste, *Logarithmic Sobolev inequalities for
finite Markov chains*, Ann. Appl. Probab. 6 (1996), Lemma 3.1). The proof is theirs: apply the
log-Sobolev inequality to `f = 1 + ε g`, for which `E(f, f) = ε² E(g, g)` and
`L(f) = 2 ε² Var(g) + O(ε³)`, divide by `ε²` and let `ε → 0`. We make the error term explicit:
with `φ(t) = t log t`, `L(f) = ∑ π φ(f²) - φ(‖f‖₂²)`, and `|φ(1 + u) - u - u²/2| ≤ 4 |u|³` for
`|u| ≤ 1/2` (from `Real.abs_log_sub_add_sum_range_le`).

## Main results

* `abs_mul_log_one_add_sub_le`: the cubic Taylor bound for `t log t` at `1`.
* `two_mul_logSobolevConstant_le_spectralGap`: `2α ≤ λ`.
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Probability.DirichletForm

/-- **Second-order expansion of `t log t` at `1`.** For `|u| ≤ 1/2`,
`|(1 + u) log(1 + u) - (u + u²/2)| ≤ 4 |u|³` (from the bound
`|-u + u²/2 + log(1 + u)| ≤ |u|³/(1 - |u|)` of `Real.abs_log_sub_add_sum_range_le`). -/
theorem abs_mul_log_one_add_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |(1 + u) * Real.log (1 + u) - (u + u ^ 2 / 2)| ≤ 4 * |u| ^ 3 := by
  have h1 : |-u| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h
  set r := Real.log (1 + u) - u + u ^ 2 / 2 with hr
  have hr' : |r| ≤ 2 * |u| ^ 3 := by
    have e : (0 : ℝ) + (-u) ^ (0 + 1) / (0 + 1 : ℕ) + (-u) ^ (1 + 1) / (1 + 1 : ℕ) +
        Real.log (1 + u) = r := by
      rw [hr]; push_cast; ring
    have hden : 1 / 2 ≤ 1 - |u| := by linarith
    have hpos : 0 < 1 - |u| := by linarith
    calc |r| ≤ |u| ^ (2 + 1) / (1 - |u|) := by rw [← e]; exact_mod_cast h
      _ ≤ |u| ^ 3 / (1 / 2) := by
          gcongr
      _ = 2 * |u| ^ 3 := by ring
  have hlog : Real.log (1 + u) = u - u ^ 2 / 2 + r := by rw [hr]; ring
  have e2 : (1 + u) * Real.log (1 + u) - (u + u ^ 2 / 2) = -u ^ 3 / 2 + (1 + u) * r := by
    rw [hlog]; ring
  rw [e2]
  have hu0 : 0 ≤ |u| := abs_nonneg u
  have h1u : |1 + u| ≤ 3 / 2 := by
    calc |1 + u| ≤ |1| + |u| := abs_add_le _ _
      _ ≤ 3 / 2 := by rw [abs_one]; linarith
  calc |-u ^ 3 / 2 + (1 + u) * r| ≤ |-u ^ 3 / 2| + |(1 + u) * r| := abs_add_le _ _
    _ = |u| ^ 3 / 2 + |1 + u| * |r| := by
        rw [abs_mul, abs_div, abs_neg, abs_pow]; norm_num
    _ ≤ |u| ^ 3 / 2 + 3 / 2 * (2 * |u| ^ 3) := by
        gcongr
    _ ≤ 4 * |u| ^ 3 := by nlinarith [pow_nonneg hu0 3]

variable {S : Type*} [Fintype S] [DecidableEq S]

omit [DecidableEq S] in
private theorem weightedVariance_eq_sum_sq_sub {π : S → ℝ} (hπ1 : ∑ x, π x = 1) (u : S → ℝ) :
    weightedVariance π u = ∑ x, π x * u x ^ 2 - (∑ x, π x * u x) ^ 2 := by
  unfold weightedVariance
  have e : ∀ x y, (u x - u y) ^ 2 * (π x * π y) =
      π y * (π x * u x ^ 2) + π x * (π y * u y ^ 2) - 2 * ((π x * u x) * (π y * u y)) := by
    intro x y; ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, hπ1]
  ring

omit [DecidableEq S] in
private theorem weightedVariance_smul (π : S → ℝ) (c : ℝ) (w : S → ℝ) :
    weightedVariance π (fun x => c * w x) = c ^ 2 * weightedVariance π w := by
  unfold weightedVariance
  have e : ∀ x y, (c * w x - c * w y) ^ 2 * (π x * π y) =
      c ^ 2 * ((w x - w y) ^ 2 * (π x * π y)) := by
    intro x y; ring
  simp only [e, ← Finset.mul_sum]
  ring

omit [DecidableEq S] in
/-- The variance of `2 g + ε g²` is at least `4 Var(g) - 4 ε K`. -/
private theorem weightedVariance_two_mul_add_ge {π : S → ℝ} (hπ : ∀ x, 0 ≤ π x) (g : S → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    4 * weightedVariance π g - 4 * ε * (1 / 2 * ∑ x, ∑ y, |g x - g y| * |g x ^ 2 - g y ^ 2| *
      (π x * π y)) ≤ weightedVariance π (fun x => 2 * g x + ε * g x ^ 2) := by
  unfold weightedVariance
  have hpt : ∀ x y, 4 * ((g x - g y) ^ 2 * (π x * π y)) -
      4 * ε * (|g x - g y| * |g x ^ 2 - g y ^ 2| * (π x * π y)) ≤
      (2 * g x + ε * g x ^ 2 - (2 * g y + ε * g y ^ 2)) ^ 2 * (π x * π y) := by
    intro x y
    have hpp : 0 ≤ π x * π y := mul_nonneg (hπ x) (hπ y)
    have hab : -(|g x - g y| * |g x ^ 2 - g y ^ 2|) ≤ (g x - g y) * (g x ^ 2 - g y ^ 2) := by
      rw [← abs_mul]; exact neg_abs_le _
    have key : 4 * (g x - g y) ^ 2 - 4 * ε * (|g x - g y| * |g x ^ 2 - g y ^ 2|) ≤
        (2 * g x + ε * g x ^ 2 - (2 * g y + ε * g y ^ 2)) ^ 2 := by
      have : (2 * g x + ε * g x ^ 2 - (2 * g y + ε * g y ^ 2)) ^ 2 =
          4 * (g x - g y) ^ 2 + 4 * ε * ((g x - g y) * (g x ^ 2 - g y ^ 2)) +
            ε ^ 2 * (g x ^ 2 - g y ^ 2) ^ 2 := by ring
      rw [this]
      nlinarith [sq_nonneg (ε * (g x ^ 2 - g y ^ 2)), mul_le_mul_of_nonneg_left hab hε]
    nlinarith [mul_le_mul_of_nonneg_right key hpp]
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ (univ : Finset S)) =>
    Finset.sum_le_sum fun y (_ : y ∈ (univ : Finset S)) => hpt x y
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  linarith

omit [DecidableEq S] in
/-- **Expansion of the entropy functional near the constant `1`.** Let `π > 0` be a probability
vector, `g` a function, `ε ≥ 0` and `A` with `|2 g(x) + ε g(x)²| ≤ A` for all `x` and
`ε A ≤ 1/2`. Then
`L_π(1 + ε g) ≥ 2 ε² Var_π(g) - ε³ (2 K + 8 A³)`, with
`K = ½ ∑ |g x - g y| |g x² - g y²| π(x) π(y)`. -/
theorem entropyFunctional_one_add_mul_ge {π : S → ℝ} (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    (g : S → ℝ) {ε A : ℝ} (hε : 0 ≤ ε) (hA : ∀ x, |2 * g x + ε * g x ^ 2| ≤ A)
    (hεA : ε * A ≤ 1 / 2) :
    2 * ε ^ 2 * weightedVariance π g - ε ^ 3 * (2 * (1 / 2 * ∑ x, ∑ y, |g x - g y| *
      |g x ^ 2 - g y ^ 2| * (π x * π y)) + 8 * A ^ 3) ≤
      entropyFunctional π (fun x => 1 + ε * g x) := by
  set K := 1 / 2 * ∑ x, ∑ y, |g x - g y| * |g x ^ 2 - g y ^ 2| * (π x * π y) with hK
  set w : S → ℝ := fun x => 2 * g x + ε * g x ^ 2 with hw
  set u : S → ℝ := fun x => ε * w x with hu
  set U := ∑ x, π x * u x with hU
  have hfu : ∀ x, (1 + ε * g x) ^ 2 = 1 + u x := fun x => by simp only [hu, hw]; ring
  have hN : ∑ y, π y * (1 + ε * g y) ^ 2 = 1 + U := by
    simp only [hfu, mul_add, mul_one, Finset.sum_add_distrib, hπ1, hU]
  have hux : ∀ x, |u x| ≤ ε * A := fun x => by
    simp only [hu, abs_mul, abs_of_nonneg hε]; exact mul_le_mul_of_nonneg_left (hA x) hε
  have hUb : |U| ≤ ε * A := by
    calc |U| ≤ ∑ x, |π x * u x| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, π x * |u x| := Finset.sum_congr rfl fun x _ => by
          rw [abs_mul, abs_of_pos (hπ x)]
      _ ≤ ∑ x, π x * (ε * A) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hux x) (hπ x).le
      _ = ε * A := by rw [← Finset.sum_mul, hπ1, one_mul]
  have hux2 : ∀ x, |u x| ≤ 1 / 2 := fun x => (hux x).trans hεA
  have hU2 : |U| ≤ 1 / 2 := hUb.trans hεA
  have hpos : ∀ x, 0 < 1 + u x := fun x => by
    have := neg_abs_le (u x); linarith [hux2 x]
  have hUpos : 0 < 1 + U := by have := neg_abs_le U; linarith
  -- `L = ∑ π φ(1 + u) - φ(1 + U)`.
  have hL : entropyFunctional π (fun x => 1 + ε * g x) =
      ∑ x, π x * ((1 + u x) * Real.log (1 + u x)) - (1 + U) * Real.log (1 + U) := by
    change ∑ x, (1 + ε * g x) ^ 2 * Real.log ((1 + ε * g x) ^ 2 / ∑ y, π y * (1 + ε * g y) ^ 2) *
      π x = _
    rw [hN]
    simp only [hfu]
    have e : ∀ x, (1 + u x) * Real.log ((1 + u x) / (1 + U)) * π x =
        π x * ((1 + u x) * Real.log (1 + u x)) - Real.log (1 + U) * (π x * (1 + u x)) := by
      intro x
      rw [Real.log_div (hpos x).ne' hUpos.ne']; ring
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have : ∑ x, π x * (1 + u x) = 1 + U := by
      simp only [mul_add, mul_one, Finset.sum_add_distrib, hπ1, hU]
    rw [this]; ring
  -- Second-order bounds on each `φ`.
  have hlow : ∀ x, π x * (u x + u x ^ 2 / 2 - 4 * |u x| ^ 3) ≤
      π x * ((1 + u x) * Real.log (1 + u x)) := by
    intro x
    refine mul_le_mul_of_nonneg_left ?_ (hπ x).le
    have := abs_mul_log_one_add_sub_le (hux2 x)
    have := neg_abs_le ((1 + u x) * Real.log (1 + u x) - (u x + u x ^ 2 / 2))
    linarith
  have hup : (1 + U) * Real.log (1 + U) ≤ U + U ^ 2 / 2 + 4 * |U| ^ 3 := by
    have := abs_mul_log_one_add_sub_le hU2
    have := le_abs_self ((1 + U) * Real.log (1 + U) - (U + U ^ 2 / 2))
    linarith
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ (univ : Finset S)) => hlow x
  have hsplit : ∑ x, π x * (u x + u x ^ 2 / 2 - 4 * |u x| ^ 3) =
      U + (∑ x, π x * u x ^ 2) / 2 - 4 * ∑ x, π x * |u x| ^ 3 := by
    rw [hU, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  -- The quadratic part is half the variance of `u = ε w`.
  have hvar : (∑ x, π x * u x ^ 2) - U ^ 2 = ε ^ 2 * weightedVariance π w := by
    rw [← weightedVariance_smul, weightedVariance_eq_sum_sq_sub hπ1]
  have hw4 := weightedVariance_two_mul_add_ge (fun x => (hπ x).le) g hε
  -- Cubic remainders.
  have hcube : ∑ x, π x * |u x| ^ 3 ≤ (ε * A) ^ 3 := by
    calc ∑ x, π x * |u x| ^ 3 ≤ ∑ x, π x * (ε * A) ^ 3 :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg _) (hux x) 3) (hπ x).le
      _ = (ε * A) ^ 3 := by rw [← Finset.sum_mul, hπ1, one_mul]
  have hUcube : |U| ^ 3 ≤ (ε * A) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hUb 3
  rw [hL]
  have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hw4' : ε ^ 2 * (4 * weightedVariance π g - 4 * ε * K) ≤ ε ^ 2 * weightedVariance π w :=
    mul_le_mul_of_nonneg_left hw4 hε2
  nlinarith

omit [DecidableEq S] in
/-- On a space with two distinct points of positive weight, an indicator has positive variance. -/
private theorem exists_weightedVariance_ne_zero {π : S → ℝ} (hπ : ∀ x, 0 < π x) {x y : S}
    (hxy : x ≠ y) :
    ∃ f, weightedVariance π f ≠ 0 := by
  classical
  set e : S → ℝ := fun z => if z = x then 1 else 0 with he
  refine ⟨e, ne_of_gt ?_⟩
  set F : S → S → ℝ := fun a b => (e a - e b) ^ 2 * (π a * π b) with hF
  have hnn : ∀ a b, 0 ≤ F a b := fun a b =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (hπ a).le (hπ b).le)
  have hterm : 0 < F x y := by
    have h1 : e x = 1 := by simp [he]
    have h2 : e y = 0 := by simp [he, Ne.symm hxy]
    simp only [hF, h1, h2]
    norm_num
    exact mul_pos (hπ x) (hπ y)
  have h1 : F x y ≤ ∑ b, F x b := Finset.single_le_sum (fun b _ => hnn x b) (Finset.mem_univ y)
  have h2 : ∑ b, F x b ≤ ∑ a, ∑ b, F a b :=
    Finset.single_le_sum (f := fun a => ∑ b, F a b)
      (fun a _ => Finset.sum_nonneg fun b _ => hnn a b) (Finset.mem_univ x)
  change 0 < 1 / 2 * ∑ a, ∑ b, F a b
  linarith

/-- **The log-Sobolev constant is at most half the spectral gap.** For a finite chain with a
stochastic matrix `P` (entries `≥ 0`, rows summing to `1`) and a positive probability vector
`π`, `2 α(P, π) ≤ λ(P, π)` (P. Diaconis and L. Saloff-Coste, *Logarithmic Sobolev inequalities
for finite Markov chains*, Ann. Appl. Probab. 6 (1996), Lemma 3.1, proved there by expanding
`L(1 + ε g)` to second order, as here). Diaconis and Saloff-Coste state it for irreducible chains
with stationary `π`; neither irreducibility nor stationarity is used. For a non-stationary `π`
the constants are those of the symmetric form `½ ∑ π(x) P(x, y) (f x - f y)²`, which equals
Diaconis and Saloff-Coste's `⟨(I - P) f, f⟩_π` only when `π` is stationary. On a one-point space
both constants are `0`. -/
theorem two_mul_logSobolevConstant_le_spectralGap {π : S → ℝ} (hπ : ∀ x, 0 < π x)
    (hπ1 : ∑ x, π x = 1) {P : Matrix S S ℝ} (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) :
    2 * logSobolevConstant π P ≤ spectralGap π P := by
  have hπ0 : ∀ x, 0 ≤ π x := fun x => (hπ x).le
  have hα0 := logSobolevConstant_nonneg hπ0 hπ1 hP hrow
  set α := logSobolevConstant π P with hα
  by_cases hne : ∃ f, weightedVariance π f ≠ 0
  swap
  · -- All points coincide: the entropyFunctional functional vanishes identically, so `α = 0`.
    have hsub : ∀ x y : S, x = y := by
      intro x y; by_contra hxy; exact hne (exists_weightedVariance_ne_zero hπ hxy)
    have hent : ∀ f, entropyFunctional π f = 0 := by
      intro f
      unfold entropyFunctional
      refine Finset.sum_eq_zero fun x _ => ?_
      have hπx : π x = 1 := by
        rw [← hπ1, Finset.sum_eq_single x (fun b _ hb => absurd (hsub b x) hb)
          (fun h => absurd (Finset.mem_univ x) h)]
      have hN : ∑ y, π y * f y ^ 2 = f x ^ 2 := by
        rw [Finset.sum_eq_single x (fun b _ hb => absurd (hsub b x) hb)
          (fun h => absurd (Finset.mem_univ x) h), hπx, one_mul]
      rw [hN]
      by_cases hf : f x ^ 2 = 0
      · rw [hf]; simp
      · rw [div_self hf, Real.log_one]; ring
    have hset : {f : S → ℝ | entropyFunctional π f ≠ 0} = ∅ := by
      ext f; simp [hent f]
    have : α = 0 := by rw [hα, logSobolevConstant, hset, Set.image_empty, Real.sInf_empty]
    rw [this, mul_zero]
    exact spectralGap_nonneg hπ0 hP hrow
  refine le_spectralGap hπ0 hne fun g => ?_
  set V := weightedVariance π g
  set E := form π (P - 1) g g
  set M := ∑ x, |g x| with hMdef
  have hM : ∀ x, |g x| ≤ M := fun x =>
    Finset.single_le_sum (fun y _ => abs_nonneg (g y)) (Finset.mem_univ x)
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun y _ => abs_nonneg (g y)
  set A := 2 * M + M ^ 2 with hAdef
  have hA0 : 0 ≤ A := by positivity
  set K := 1 / 2 * ∑ x, ∑ y, |g x - g y| * |g x ^ 2 - g y ^ 2| * (π x * π y) with hKdef
  have hK0 : 0 ≤ K := mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun y _ => mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (hπ0 x) (hπ0 y)))
  set C := 2 * K + 8 * A ^ 3 with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hstep : ∀ ε, 0 < ε → ε ≤ 1 → ε * A ≤ 1 / 2 → α * (2 * V - ε * C) ≤ E := by
    intro ε hε0 hε1 hεA
    have hAx : ∀ x, |2 * g x + ε * g x ^ 2| ≤ A := by
      intro x
      have hgx := hM x
      have hsq : g x ^ 2 ≤ M ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hgx 2
      calc |2 * g x + ε * g x ^ 2| ≤ |2 * g x| + |ε * g x ^ 2| := abs_add_le _ _
        _ = 2 * |g x| + ε * g x ^ 2 := by
            rw [abs_mul, abs_mul, abs_two, abs_of_pos hε0, abs_of_nonneg (sq_nonneg (g x))]
        _ ≤ 2 * M + 1 * M ^ 2 := by
            have := mul_le_mul hε1 hsq (sq_nonneg (g x)) zero_le_one
            linarith
        _ = A := by ring
    have hL := entropyFunctional_one_add_mul_ge hπ hπ1 g hε0.le hAx hεA
    have hls := logSobolevConstant_mul_entropyFunctional_le hπ0 hπ1 hP hrow (fun x => 1 + ε * g x)
    have hEf : form π (P - 1) (fun x => 1 + ε * g x) (fun x => 1 + ε * g x) = ε ^ 2 * E := by
      simp only [E, form_sub_one π hrow]
      have e : ∀ x y, π x * P x y * (1 + ε * g x - (1 + ε * g y)) * (1 + ε * g x - (1 + ε * g y)) =
          ε ^ 2 * (π x * P x y * (g x - g y) * (g x - g y)) := by intro x y; ring
      simp only [e, ← Finset.mul_sum]; ring
    have h1 : α * (2 * ε ^ 2 * V - ε ^ 3 * C) ≤ ε ^ 2 * E :=
      (mul_le_mul_of_nonneg_left hL hα0).trans (hls.trans hEf.le)
    have hε2 : 0 < ε ^ 2 := by positivity
    have h2 : ε ^ 2 * (α * (2 * V - ε * C)) ≤ ε ^ 2 * E := by
      have : ε ^ 2 * (α * (2 * V - ε * C)) = α * (2 * ε ^ 2 * V - ε ^ 3 * C) := by ring
      rw [this]; exact h1
    exact le_of_mul_le_mul_left h2 hε2
  -- Let `ε → 0`.
  by_contra hcon
  have hδ : 0 < 2 * α * V - E := by linarith [lt_of_not_ge hcon]
  set δ := 2 * α * V - E
  set ε := min (min 1 (1 / (2 * A + 1))) (δ / (2 * (α * C + 1))) with hεdef
  have hαC : 0 ≤ α * C := mul_nonneg hα0 hC0
  have hε0 : 0 < ε := lt_min (lt_min one_pos (by positivity)) (by positivity)
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hεA : ε * A ≤ 1 / 2 := by
    have h' : ε ≤ 1 / (2 * A + 1) := (min_le_left _ _).trans (min_le_right _ _)
    have hpos : 0 < 2 * A + 1 := by positivity
    calc ε * A ≤ 1 / (2 * A + 1) * A := mul_le_mul_of_nonneg_right h' hA0
      _ ≤ 1 / 2 := by rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]; linarith
  have hεδ : ε ≤ δ / (2 * (α * C + 1)) := min_le_right _ _
  have hmain := hstep ε hε0 hε1 hεA
  have hsmall : α * C * ε < δ := by
    have hpos : 0 < 2 * (α * C + 1) := by positivity
    calc α * C * ε ≤ α * C * (δ / (2 * (α * C + 1))) := mul_le_mul_of_nonneg_left hεδ hαC
      _ < δ := by
          rw [mul_div_assoc', div_lt_iff₀ hpos]
          nlinarith
  nlinarith

end MathlibExt.Probability.DirichletForm
