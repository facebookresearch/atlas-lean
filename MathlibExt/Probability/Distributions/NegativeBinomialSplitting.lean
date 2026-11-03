/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.MeasureTheory.Measure.Real

/-!
# Splitting a sum of negative binomial counts: the beta-binomial law

For a real shape `r > 0` and success probability `p ∈ (0, 1]`, the negative binomial law
`NB(r, p)` on `ℕ` has mass `P(X = k) = r^{(k)} / k! · p^r (1 - p)^k`, where `r^{(k)}` is the rising
factorial (`ascPochhammer`); for integer `r` it counts failures before the `r`-th success. The
beta-binomial law `BB(n; α, β)` has mass
`C(n, k) α^{(k)} β^{(n - k)} / (α + β)^{(n)} = C(n, k) B(k + α, n - k + β) / B(α, β)`.

If `X ~ NB(r₁, p)` and `Y ~ NB(r₂, p)` are independent, then `X + Y ~ NB(r₁ + r₂, p)` and the
conditional law of `X` given `X + Y = n` is `BB(n; r₁, r₂)`, free of `p`. This is the negative
binomial analogue of the binomial split of a sum of independent Poisson counts. Both facts
reduce to the Chu–Vandermonde identity `(α + β)^{(n)} = ∑ₖ C(n, k) α^{(k)} β^{(n - k)}`.

## Main results

* `ProbabilityTheory.negBinomialPMF`, `ProbabilityTheory.betaBinomialPMF`.
* `ProbabilityTheory.ascPochhammer_eval_add_eq_sum`: Chu–Vandermonde for rising factorials.
* `ProbabilityTheory.sum_betaBinomialPMF`: the beta-binomial masses sum to one.
* `ProbabilityTheory.hasSum_negBinomialPMF`: the negative binomial masses sum to one.
* `ProbabilityTheory.sum_negBinomialPMF_mul`: `NB(r₁, p) * NB(r₂, p) = NB(r₁ + r₂, p)`.
* `ProbabilityTheory.negBinomialPMF_mul_div_eq_betaBinomialPMF`: the conditional mass ratio is
  beta-binomial.
* `ProbabilityTheory.measure_cond_eq_betaBinomialPMF`: the same for independent random variables.

## References

* N. L. Johnson, A. W. Kemp and S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley
  (2005), chapters 5 (negative binomial) and 6 (beta-binomial).
-/


@[expose] public section

open MeasureTheory Real Finset
open scoped Nat

namespace ProbabilityTheory

/-- Negative binomial mass `P(X = k) = r^{(k)} / k! · p ^ r · (1 - p) ^ k` with real shape `r`
(rising factorial `r^{(k)} = (ascPochhammer ℝ k).eval r`) and success probability `p`, using the
real power `p ^ r`. A probability mass function for `r > 0` and `p ∈ (0, 1]`. -/
noncomputable def negBinomialPMF (r p : ℝ) (k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval r / k ! * p ^ r * (1 - p) ^ k

/-- Beta-binomial mass `C(n, k) α^{(k)} β^{(n - k)} / (α + β)^{(n)}` (zero for `k > n`, since
`C(n, k) = 0`). A probability mass function for `α, β > 0`. -/
noncomputable def betaBinomialPMF (n : ℕ) (α β : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (ascPochhammer ℝ k).eval α * (ascPochhammer ℝ (n - k)).eval β /
    (ascPochhammer ℝ n).eval (α + β)

/-- **Chu–Vandermonde identity for rising factorials**:
`(α + β)^{(n)} = ∑_{k ≤ n} C(n, k) α^{(k)} β^{(n - k)}`, for all real `α, β`. -/
theorem ascPochhammer_eval_add_eq_sum (α β : ℝ) (n : ℕ) :
    (ascPochhammer ℝ n).eval (α + β) =
      ∑ k ∈ range (n + 1),
        (n.choose k : ℝ) * (ascPochhammer ℝ k).eval α * (ascPochhammer ℝ (n - k)).eval β := by
  have h (m : ℕ) :
      (ascPochhammer ℝ m).eval (α + β) =
        ∑ ij ∈ antidiagonal m,
          (m.choose ij.1 : ℝ) *
            ((ascPochhammer ℝ ij.1).eval α * (ascPochhammer ℝ ij.2).eval β) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [ascPochhammer_succ_eval, ih, Finset.sum_mul,
        Finset.sum_antidiagonal_choose_succ_mul
          (fun i j => (ascPochhammer ℝ i).eval α * (ascPochhammer ℝ j).eval β),
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ij hij
      have hij' : ij.1 + ij.2 = m := List.Nat.mem_antidiagonal.mp hij
      have hc : m.choose ij.2 = m.choose ij.1 :=
        Nat.choose_symm_of_eq_add (by omega)
      have hn : (ij.1 : ℝ) + (ij.2 : ℝ) = m := by exact_mod_cast hij'
      rw [hc, ascPochhammer_succ_eval, ascPochhammer_succ_eval]
      rw [← hn]
      ring
  simpa only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_assoc] using h n

/-- The beta-binomial masses sum to one for `α, β > 0`. -/
theorem sum_betaBinomialPMF (n : ℕ) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∑ k ∈ range (n + 1), betaBinomialPMF n α β k = 1 := by
  unfold betaBinomialPMF
  rw [← Finset.sum_div, ← ascPochhammer_eval_add_eq_sum]
  exact div_self (ne_of_gt (ascPochhammer_pos n (α + β) (add_pos hα hβ)))

private theorem choose_eq_ascPochhammer_div (r : ℝ) (k : ℕ) :
    Ring.choose (r + k - 1) k = (ascPochhammer ℝ k).eval r / k ! := by
  rw [← Ring.multichoose_eq]
  apply (eq_div_iff_mul_eq (by exact_mod_cast Nat.factorial_ne_zero k)).2
  simpa only [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval, mul_comm] using
    Ring.factorial_nsmul_multichoose_eq_ascPochhammer r k

/-- The negative binomial masses sum to one for `r > 0` and `p ∈ (0, 1]` (the binomial series
`∑ₖ r^{(k)} xᵏ / k! = (1 - x)^{-r}` at `x = 1 - p`). -/
theorem hasSum_negBinomialPMF {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1) :
    HasSum (negBinomialPMF r p) 1 := by
  have hx : 1 - p ∈ Metric.eball (0 : ℝ) (1 : ENNReal) := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_nonneg (sub_nonneg.mpr hp1)]
    linarith
  have hs := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero r).hasSum hx
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    choose_eq_ascPochhammer_div, zero_add, sub_sub_cancel] at hs
  convert hs.mul_right (p ^ r) using 1
  · funext k
    unfold negBinomialPMF
    ring
  · exact (div_mul_cancel₀ 1 ((Real.rpow_ne_zero hp.le (ne_of_gt hr)).2 hp.ne')).symm

private theorem negBinomialPMF_mul_eq (r₁ r₂ : ℝ) {p : ℝ} (hp : 0 < p)
    {n k : ℕ} (hk : k ≤ n) :
    negBinomialPMF r₁ p k * negBinomialPMF r₂ p (n - k) =
      ((n.choose k : ℝ) * (ascPochhammer ℝ k).eval r₁ *
        (ascPochhammer ℝ (n - k)).eval r₂) / n ! * p ^ (r₁ + r₂) * (1 - p) ^ n := by
  have hkf : (k ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnf : (n ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hnkf : ((n - k) ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - k)
  have hfac : (n.choose k : ℝ) * (k ! : ℝ) * ((n - k) ! : ℝ) = n ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hc : (n.choose k : ℝ) / n ! = 1 / ((k ! : ℝ) * ((n - k) ! : ℝ)) := by
    apply (div_eq_div_iff hnf (mul_ne_zero hkf hnkf)).2
    simpa only [one_mul, mul_assoc] using hfac
  have hcoef : (ascPochhammer ℝ k).eval r₁ / k ! *
      ((ascPochhammer ℝ (n - k)).eval r₂ / (n - k) !) =
      (n.choose k : ℝ) * (ascPochhammer ℝ k).eval r₁ *
        (ascPochhammer ℝ (n - k)).eval r₂ / n ! := by
    rw [div_mul_div_comm]
    calc
      _ = ((ascPochhammer ℝ k).eval r₁ *
          (ascPochhammer ℝ (n - k)).eval r₂) *
          (1 / ((k ! : ℝ) * ((n - k) ! : ℝ))) := by ring
      _ = _ := by rw [← hc]; ring
  have hpow : (1 - p) ^ k * (1 - p) ^ (n - k) = (1 - p) ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  unfold negBinomialPMF
  calc
    _ = ((ascPochhammer ℝ k).eval r₁ / k ! *
        ((ascPochhammer ℝ (n - k)).eval r₂ / (n - k) !)) *
        (p ^ r₁ * p ^ r₂) * ((1 - p) ^ k * (1 - p) ^ (n - k)) := by ring
    _ = _ := by rw [hcoef, ← Real.rpow_add hp, hpow]

/-- **Convolution of negative binomial laws with a common `p`**:
`∑_{k ≤ n} NB(r₁, p)(k) NB(r₂, p)(n - k) = NB(r₁ + r₂, p)(n)` for `p > 0` and all real
shapes. -/
theorem sum_negBinomialPMF_mul (r₁ r₂ : ℝ) {p : ℝ} (hp : 0 < p) (n : ℕ) :
    ∑ k ∈ range (n + 1), negBinomialPMF r₁ p k * negBinomialPMF r₂ p (n - k) =
      negBinomialPMF (r₁ + r₂) p n := by
  calc
    _ = ∑ k ∈ range (n + 1),
        ((n.choose k : ℝ) * (ascPochhammer ℝ k).eval r₁ *
          (ascPochhammer ℝ (n - k)).eval r₂) / n ! * p ^ (r₁ + r₂) * (1 - p) ^ n := by
      apply Finset.sum_congr rfl
      intro k hk
      exact negBinomialPMF_mul_eq r₁ r₂ hp (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_div,
        ← ascPochhammer_eval_add_eq_sum]
      rfl

/-- **Negative binomial splitting**: for `r₁, r₂ > 0`, `0 < p < 1` and `k ≤ n`,
`NB(r₁, p)(k) NB(r₂, p)(n - k) / NB(r₁ + r₂, p)(n) = BB(n; r₁, r₂)(k)`; the conditional law of
one component given the total is beta-binomial and does not depend on `p`. -/
theorem negBinomialPMF_mul_div_eq_betaBinomialPMF {r₁ r₂ p : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hp : 0 < p) (hp1 : p < 1) {n k : ℕ} (hk : k ≤ n) :
    negBinomialPMF r₁ p k * negBinomialPMF r₂ p (n - k) / negBinomialPMF (r₁ + r₂) p n =
      betaBinomialPMF n r₁ r₂ k := by
  rw [negBinomialPMF_mul_eq r₁ r₂ hp hk]
  have ha : (ascPochhammer ℝ n).eval (r₁ + r₂) ≠ 0 :=
    ne_of_gt (ascPochhammer_pos n (r₁ + r₂) (add_pos hr₁ hr₂))
  have hf : (n ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hp' : p ^ (r₁ + r₂) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hp _)
  have hq : (1 - p) ^ n ≠ 0 := ne_of_gt (pow_pos (sub_pos.mpr hp1) n)
  unfold negBinomialPMF betaBinomialPMF
  field_simp [ha, hf, hp', hq]

/-- **Negative binomial splitting for random variables**: if `X` and `Y` are independent with
`P(X = j) = NB(r₁, p)(j)` and `P(Y = j) = NB(r₂, p)(j)` for all `j`, where `r₁, r₂ > 0` and
`0 < p < 1`, then `P(X = k ∣ X + Y = n) = BB(n; r₁, r₂)(k)` for `k ≤ n`. -/
theorem measure_cond_eq_betaBinomialPMF {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℕ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ) {r₁ r₂ p : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hp : 0 < p)
    (hp1 : p < 1) (hlawX : ∀ j, μ.real (X ⁻¹' {j}) = negBinomialPMF r₁ p j)
    (hlawY : ∀ j, μ.real (Y ⁻¹' {j}) = negBinomialPMF r₂ p j) {n k : ℕ} (hk : k ≤ n) :
    μ.real ({ω | X ω = k} ∩ {ω | X ω + Y ω = n}) / μ.real {ω | X ω + Y ω = n} =
      betaBinomialPMF n r₁ r₂ k := by
  have hinter (i j : ℕ) :
      μ.real (X ⁻¹' {i} ∩ Y ⁻¹' {j}) =
        negBinomialPMF r₁ p i * negBinomialPMF r₂ p j := by
    rw [← hlawX i, ← hlawY j]
    simpa only [measureReal_def, ENNReal.toReal_mul] using
      congrArg ENNReal.toReal
        (hXY.measure_inter_preimage_eq_mul {i} {j}
          (measurableSet_singleton i) (measurableSet_singleton j))
  have hpart : {ω | X ω + Y ω = n} =
      ⋃ i ∈ range (n + 1), (X ⁻¹' {i} ∩ Y ⁻¹' {n - i}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      refine ⟨X ω, by omega, rfl, ?_⟩
      omega
    · rintro ⟨i, hi, hxi, hyi⟩
      omega
  have hd : Set.PairwiseDisjoint (↑(range (n + 1)))
      (fun i => X ⁻¹' {i} ∩ Y ⁻¹' {n - i}) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro ω hwi hwj
    exact hij (hwi.1.symm.trans hwj.1)
  have hm (i : ℕ) (_hi : i ∈ range (n + 1)) :
      MeasurableSet (X ⁻¹' {i} ∩ Y ⁻¹' {n - i}) :=
    ((measurableSet_singleton i).preimage hX).inter
      ((measurableSet_singleton (n - i)).preimage hY)
  have hden : μ.real {ω | X ω + Y ω = n} = negBinomialPMF (r₁ + r₂) p n := by
    rw [hpart, measureReal_biUnion_finset hd hm]
    simp_rw [hinter]
    exact sum_negBinomialPMF_mul r₁ r₂ hp n
  have hnum : {ω | X ω = k} ∩ {ω | X ω + Y ω = n} =
      X ⁻¹' {k} ∩ Y ⁻¹' {n - k} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff]
    omega
  rw [hnum, hinter, hden]
  exact negBinomialPMF_mul_div_eq_betaBinomialPMF hr₁ hr₂ hp hp1 hk

end ProbabilityTheory
