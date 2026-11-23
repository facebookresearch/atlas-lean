/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

arnovich/asgard-lean, commit
e5e098d5bce80c3907a6acd4e2beb904309a1709,
`Gimle/Asgard/Streams/ColeHopf.lean`. Authors: arnovich.

MIT License

Copyright (c) 2025 Gimle Labs

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import MathlibExt.Analysis.PDE.ExponentialColeHopf
public import MathlibExt.RingTheory.MvPowerSeries.ExponentialDerivative
public import MathlibExt.RingTheory.MvPowerSeries.ColeHopfSolution
public import MathlibExt.RingTheory.MvPowerSeries.GeometricEvaluation
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational series for classical exponential-sum Cole–Hopf solutions

The bivariate exponential Taylor coefficients evaluate to the exponential heat
profiles in `ColeHopf.heatMoment`. Absolutely convergent product and reciprocal
evaluation identifies the formal Cole–Hopf quotient with its classical solution.
The existing geometric-tail estimate therefore bounds the error of a finite
rectangular polynomial approximation to that real solution.

References: Zarmi, equations (3)–(5), https://arxiv.org/abs/1908.01315;
Gesztesy–Holden, Lemma 3.1, https://arxiv.org/abs/solv-int/9812025.
The evaluation argument uses the ordinary exponential Taylor series and
absolutely convergent Cauchy products. Rational geometric estimates are
elementary consequences of coefficient bounds, as in `GeometricMajorant`
and `GeometricTail`; they are not quoted constants from those papers.
-/

@[expose] public section

namespace MvPowerSeries.ColeHopf

/-- Bivariate exponential Taylor series with rational rates, in time-space order. -/
noncomputable def exponentialSeries₂ (a b : ℚ) : MvPowerSeries (Fin 2) ℚ :=
  fun α => a ^ α 0 * b ^ α 1 / ((α 0).factorial * (α 1).factorial)

theorem coeff_exponentialSeries₂ (a b : ℚ) (α : Fin 2 →₀ ℕ) :
    coeff α (exponentialSeries₂ a b) =
      a ^ α 0 * b ^ α 1 / ((α 0).factorial * (α 1).factorial) := rfl

@[simp] theorem constantCoeff_exponentialSeries₂ (a b : ℚ) :
    constantCoeff (exponentialSeries₂ a b) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_exponentialSeries₂]
  simp

/-- Time differentiation multiplies the exponential series by its time rate. -/
theorem pderiv_zero_exponentialSeries₂ (a b : ℚ) :
    pderiv 0 (exponentialSeries₂ a b) = C a * exponentialSeries₂ a b := by
  ext α
  rw [coeff_pderiv, coeff_C_mul, coeff_exponentialSeries₂, coeff_exponentialSeries₂]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne
    (by decide : (1 : Fin 2) ≠ 0), add_zero, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  have h0 : ((α 0).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h1 : ((α 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hs : (α 0 : ℚ) + 1 ≠ 0 := by positivity
  field_simp

/-- Spatial differentiation multiplies the exponential series by its spatial rate. -/
theorem pderiv_one_exponentialSeries₂ (a b : ℚ) :
    pderiv 1 (exponentialSeries₂ a b) = C b * exponentialSeries₂ a b := by
  ext α
  rw [coeff_pderiv, coeff_C_mul, coeff_exponentialSeries₂, coeff_exponentialSeries₂]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne
    (by decide : (0 : Fin 2) ≠ 1), add_zero, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  have h0 : ((α 0).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h1 : ((α 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hs : (α 1 : ℚ) + 1 ≠ 0 := by positivity
  field_simp

/-- The coefficient formula is the canonical formal exponential of a linear form. -/
theorem exponentialSeries₂_eq_expOfConstantCoeffZero (a b : ℚ) :
    exponentialSeries₂ a b =
      expOfConstantCoeffZero (C a * X 0 + C b * X 1) (by simp) := by
  let E := expOfConstantCoeffZero (C a * X (0 : Fin 2) + C b * X 1) (by simp)
  have step (α : Fin 2 →₀ ℕ) (i : Fin 2)
      (ih : coeff α (exponentialSeries₂ a b) = coeff α E) :
      coeff (α + Finsupp.single i 1) (exponentialSeries₂ a b) =
        coeff (α + Finsupp.single i 1) E := by
    apply mul_right_cancel₀ (show (α i : ℚ) + 1 ≠ 0 by positivity)
    rw [← coeff_pderiv, ← coeff_pderiv]
    fin_cases i
    · change coeff α (pderiv 0 (exponentialSeries₂ a b)) = coeff α (pderiv 0 E)
      rw [pderiv_zero_exponentialSeries₂]
      simp [E, pderiv_expOfConstantCoeffZero, coeff_C_mul, ih]
    · change coeff α (pderiv 1 (exponentialSeries₂ a b)) = coeff α (pderiv 1 E)
      rw [pderiv_one_exponentialSeries₂]
      simp [E, pderiv_expOfConstantCoeffZero, coeff_C_mul, ih]
  ext α
  change coeff α (exponentialSeries₂ a b) = coeff α E
  induction α using Finsupp.induction₂ with
  | zero => simp [coeff_zero_eq_constantCoeff, E]
  | add_single i n α hi hn ih =>
    clear hi hn
    induction n with
    | zero => simpa using ih
    | succ n hn =>
      simpa [Finsupp.single_add, ← add_assoc] using step (α + Finsupp.single i n) i hn

private theorem hasSum_exp (r : ℝ) :
    HasSum (fun n : ℕ => r ^ n / n.factorial) (Real.exp r) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp r

/-- The rational bivariate exponential series converges at every real point. -/
theorem hasSum_exponentialSeries₂ (a b : ℚ) (x : Fin 2 → ℝ) :
    HasSum (seriesTerm (exponentialSeries₂ a b) x)
      (Real.exp ((a : ℝ) * x 0 + b * x 1)) := by
  let e : (Fin 2 →₀ ℕ) ≃ ℕ × ℕ :=
    (Finsupp.equivFunOnFinite (α := Fin 2) (M := ℕ)).trans (finTwoArrowEquiv ℕ)
  have norms (r : ℝ) : Summable fun n : ℕ => ‖r ^ n / (n.factorial : ℝ)‖ := by
    simpa [norm_div, norm_pow, Real.norm_eq_abs] using Real.summable_pow_div_factorial |r|
  have h := (hasSum_exp ((a : ℝ) * x 0)).mul (hasSum_exp ((b : ℝ) * x 1))
    (summable_mul_of_summable_norm (norms _) (norms _))
  rw [← Real.exp_add] at h
  have he := e.hasSum_iff.mpr h
  refine he.congr_fun fun α => ?_
  change seriesTerm (exponentialSeries₂ a b) x α =
    (((a : ℝ) * x 0) ^ α 0 / (α 0).factorial) *
      (((b : ℝ) * x 1) ^ α 1 / (α 1).factorial)
  simp only [seriesTerm, coeff_exponentialSeries₂, Fin.prod_univ_two]
  push_cast
  simp only [mul_pow]
  ring

variable {ι : Type*} (s : Finset ι) (c k : ι → ℚ) (ν : ℚ)

/-- Rational coefficient series of a finite exponential heat moment. -/
noncomputable def exponentialHeatMoment (n : ℕ) : MvPowerSeries (Fin 2) ℚ :=
  ∑ i ∈ s, C (c i * k i ^ n) * exponentialSeries₂ (ν * k i ^ 2) (k i)

/-- The constant coefficient is the finite frequency moment. -/
@[simp] theorem constantCoeff_exponentialHeatMoment (n : ℕ) :
    constantCoeff (exponentialHeatMoment s c k ν n) = ∑ i ∈ s, c i * k i ^ n := by
  simp [exponentialHeatMoment]

/-- Coefficient evaluation identifies every finite heat moment with its real function. -/
theorem hasSum_exponentialHeatMoment (n : ℕ) (x : Fin 2 → ℝ) :
    HasSum (seriesTerm (exponentialHeatMoment s c k ν n) x)
      (_root_.ColeHopf.heatMoment s (fun i => (c i : ℝ)) (fun i => (k i : ℝ)) ν n (x 0) (x 1)) := by
  have h := hasSum_sum (s := s) fun i _ =>
    (hasSum_exponentialSeries₂ (ν * k i ^ 2) (k i) x).mul_left ((c i * k i ^ n : ℚ) : ℝ)
  simp only [Rat.cast_mul, Rat.cast_pow] at h
  refine h.congr_fun fun α => ?_
  simp only [seriesTerm, exponentialHeatMoment, map_sum, coeff_C_mul,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Finset.sum_mul, mul_assoc]

/-- The sum of the rational coefficient series is the classical heat moment. -/
theorem geometricSum_exponentialHeatMoment (n : ℕ) (x : Fin 2 → ℝ) :
    geometricSum (exponentialHeatMoment s c k ν n) x =
      _root_.ColeHopf.heatMoment s (fun i => (c i : ℝ)) (fun i => (k i : ℝ)) ν n (x 0) (x 1) :=
  (hasSum_exponentialHeatMoment s c k ν n x).tsum_eq

private theorem pderiv_C_mul (j : Fin 2) (q : ℚ) (a : MvPowerSeries (Fin 2) ℚ) :
    pderiv j (C q * a) = C q * pderiv j a := by
  simpa only [pderiv_C, smul_eq_mul, mul_zero, add_zero] using (pderiv j).leibniz (C q) a

/-- Formal spatial differentiation agrees with the classical moment shift. -/
theorem pderiv_one_exponentialHeatMoment (n : ℕ) :
    pderiv 1 (exponentialHeatMoment s c k ν n) = exponentialHeatMoment s c k ν (n + 1) := by
  simp only [exponentialHeatMoment, map_sum, pderiv_C_mul, pderiv_one_exponentialSeries₂]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, ← map_mul]
  congr 2
  ring

/-- Formal time differentiation raises the moment order by two. -/
theorem pderiv_zero_exponentialHeatMoment (n : ℕ) :
    pderiv 0 (exponentialHeatMoment s c k ν n) = C ν * exponentialHeatMoment s c k ν (n + 2) := by
  simp only [exponentialHeatMoment, map_sum, pderiv_C_mul, pderiv_zero_exponentialSeries₂,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
  congr 2
  ring

/-- The explicit rational series solves the formal heat equation. -/
theorem exponentialHeatMoment_heat :
    pderiv 0 (exponentialHeatMoment s c k ν 0) =
      C ν * pderiv 1 (pderiv 1 (exponentialHeatMoment s c k ν 0)) := by
  rw [pderiv_zero_exponentialHeatMoment, pderiv_one_exponentialHeatMoment,
    pderiv_one_exponentialHeatMoment]

/-- The explicit series is the canonical formal heat solution of its initial profile. -/
theorem exponentialHeatMoment_eq_heatSolution :
    exponentialHeatMoment s c k ν 0 = heatSolution ν 0 1 (exponentialHeatMoment s c k 0 0) := by
  apply heatSolution_unique (by decide : (1 : Fin 2) ≠ 0)
  · exact exponentialHeatMoment_heat s c k ν
  · intro α hα
    simp [exponentialHeatMoment, coeff_C_mul, coeff_exponentialSeries₂, hα]

/-- The rational formal Cole–Hopf series of the exponential heat profile. -/
noncomputable def exponentialBurgersSeries : MvPowerSeries (Fin 2) ℚ :=
  coleHopf ν 1 (exponentialHeatMoment s c k ν 0)

/-- The explicit quotient is the canonical formal Burgers solution with the
Cole–Hopf transform of the exponential initial profile. -/
theorem exponentialBurgersSeries_eq_solution (hc : (∑ i ∈ s, c i) ≠ 0) :
    exponentialBurgersSeries s c k ν =
      Causal.solution 0 (burgersRhs ν 1)
        (coleHopf ν 1 (exponentialHeatMoment s c k 0 0)) := by
  rw [exponentialBurgersSeries, exponentialHeatMoment_eq_heatSolution]
  exact coleHopf_heatSolution_eq_solution (by decide : (1 : Fin 2) ≠ 0) (by simpa using hc)

/-- The formal quotient solves Burgers when its constant heat coefficient is nonzero. -/
theorem exponentialBurgersSeries_formal (hc : (∑ i ∈ s, c i) ≠ 0) :
    pderiv 0 (exponentialBurgersSeries s c k ν) +
      exponentialBurgersSeries s c k ν * pderiv 1 (exponentialBurgersSeries s c k ν) =
        C ν * pderiv 1 (pderiv 1 (exponentialBurgersSeries s c k ν)) := by
  exact eq_sub_iff_add_eq.mp (pderiv_coleHopf_of_heat ν 0 1 (exponentialHeatMoment s c k ν 0)
    (by simpa using hc) (exponentialHeatMoment_heat s c k ν))

/-- The formal quotient evaluates to the classical solution, with nonvanishing
deduced from convergent reciprocal evaluation. -/
theorem geometricSum_exponentialBurgersSeries
    (hc : (∑ i ∈ s, c i) ≠ 0)
    {m0 m1 mi : GeometricMajorant (Fin 2)} {r : Fin 2 → ℚ≥0}
    (h0 : IsMajorized (exponentialHeatMoment s c k ν 0) m0)
    (h1 : IsMajorized (exponentialHeatMoment s c k ν 1) m1)
    (hi : IsMajorized (exponentialHeatMoment s c k ν 0)⁻¹ mi)
    (i0 : ∀ i, (r i : ℚ) < m0.radius i) (i1 : ∀ i, (r i : ℚ) < m1.radius i)
    (ii : ∀ i, (r i : ℚ) < mi.radius i)
    {x : Fin 2 → ℝ} (hx : ∀ i, |x i| ≤ ((r i : ℚ) : ℝ)) :
    geometricSum (exponentialBurgersSeries s c k ν) x =
      _root_.ColeHopf.exponentialSolution s (fun i => (c i : ℝ)) (fun i => (k i : ℝ))
        ν (x 0) (x 1) ∧
    _root_.ColeHopf.heatMoment s (fun i => (c i : ℝ)) (fun i => (k i : ℝ))
        ν 0 (x 0) (x 1) ≠ 0 := by
  have hinv := geometricSum_inv (by simpa using hc) h0 hi i0 ii hx
  constructor
  · simp only [exponentialBurgersSeries, coleHopf, pderiv_one_exponentialHeatMoment]
    rw [geometricSum_C_mul, geometricSum_mul h1 hi i1 ii hx, hinv.1,
      geometricSum_exponentialHeatMoment, geometricSum_exponentialHeatMoment]
    simp only [Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat,
      _root_.ColeHopf.exponentialSolution, div_eq_mul_inv]
  · simpa only [geometricSum_exponentialHeatMoment] using hinv.2

/-- A coefficient bound for the bivariate exponential from bounds on its rates. -/
theorem coeff_exponentialSeries₂_le (a b : ℚ) {R : Fin 2 → ℚ}
    (hR : ∀ i, 0 < R i) (ha : |a| ≤ (R 0)⁻¹) (hb : |b| ≤ (R 1)⁻¹)
    (α : Fin 2 →₀ ℕ) : |coeff α (exponentialSeries₂ a b)| ≤ radiiWeight R α := by
  have hf : (1 : ℚ) ≤ (α 0).factorial * (α 1).factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
  rw [coeff_exponentialSeries₂, abs_div, abs_mul, abs_pow, abs_pow,
    abs_of_pos (by positivity : (0 : ℚ) < (α 0).factorial * (α 1).factorial)]
  calc |a| ^ α 0 * |b| ^ α 1 / ((α 0).factorial * (α 1).factorial)
      ≤ |a| ^ α 0 * |b| ^ α 1 := div_le_self (by positivity) hf
    _ ≤ ((R 0)⁻¹) ^ α 0 * ((R 1)⁻¹) ^ α 1 :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg a) ha _) (pow_le_pow_left₀ (abs_nonneg b) hb _)
        (by positivity) (pow_nonneg (inv_nonneg.mpr (hR 0).le) _)
    _ = radiiWeight R α := by simp [radiiWeight, Fin.prod_univ_two, inv_pow, mul_comm]

/-- A rational majorant for any finite heat moment, obtained by dropping factorials. -/
theorem isMajorized_exponentialHeatMoment (n : ℕ) {R : Fin 2 → ℚ}
    (hR : ∀ i, 0 < R i)
    (ht : ∀ i ∈ s, |ν * k i ^ 2| ≤ (R 0)⁻¹)
    (hx : ∀ i ∈ s, |k i| ≤ (R 1)⁻¹) :
    IsMajorized (exponentialHeatMoment s c k ν n)
      ⟨∑ i ∈ s, |c i * k i ^ n|, R, Finset.sum_nonneg (fun _ _ => abs_nonneg _), hR⟩ := by
  intro α
  simp only [exponentialHeatMoment, map_sum, coeff_C_mul]
  calc |∑ i ∈ s, c i * k i ^ n * coeff α (exponentialSeries₂ (ν * k i ^ 2) (k i))|
      ≤ ∑ i ∈ s, |c i * k i ^ n * coeff α (exponentialSeries₂ (ν * k i ^ 2) (k i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, |c i * k i ^ n| * radiiWeight R α := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (coeff_exponentialSeries₂_le _ _ hR (ht i hi) (hx i hi) α)
        (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- A majorant of the quotient from numerator and reciprocal bounds at common radii. -/
theorem isMajorized_exponentialBurgersSeries
    {m1 mi : GeometricMajorant (Fin 2)} (R : Fin 2 → ℚ)
    (h1 : IsMajorized (exponentialHeatMoment s c k ν 1) m1)
    (hi : IsMajorized (exponentialHeatMoment s c k ν 0)⁻¹ mi)
    (r1 : ∀ i, m1.radius i = R i) (ri : ∀ i, mi.radius i = R i) :
    IsMajorized (exponentialBurgersSeries s c k ν)
      ⟨|-2 * ν| * (m1.bound * mi.bound), fun i => R i / 2,
        mul_nonneg (abs_nonneg _) (mul_nonneg m1.bound_nonneg mi.bound_nonneg),
        fun i => by rw [← r1 i]; exact half_pos (m1.radius_pos i)⟩ := by
  unfold exponentialBurgersSeries coleHopf
  rw [pderiv_one_exponentialHeatMoment]
  exact (h1.mul R hi r1 ri).C_mul (-2 * ν)

/-- A uniform rational bound on rectangular truncation of the classical Burgers solution. -/
theorem exponentialSolution_truncation
    (hc : (∑ i ∈ s, c i) ≠ 0)
    {m0 m1 mi mu : GeometricMajorant (Fin 2)} {r : Fin 2 → ℚ≥0}
    (h0 : IsMajorized (exponentialHeatMoment s c k ν 0) m0)
    (h1 : IsMajorized (exponentialHeatMoment s c k ν 1) m1)
    (hi : IsMajorized (exponentialHeatMoment s c k ν 0)⁻¹ mi)
    (hu : IsMajorized (exponentialBurgersSeries s c k ν) mu)
    (i0 : ∀ i, (r i : ℚ) < m0.radius i) (i1 : ∀ i, (r i : ℚ) < m1.radius i)
    (ii : ∀ i, (r i : ℚ) < mi.radius i) (iu : ∀ i, (r i : ℚ) < mu.radius i)
    (N : Fin 2 → ℕ) {x : Fin 2 → ℝ} (hx : ∀ i, |x i| ≤ ((r i : ℚ) : ℝ)) :
    |(_root_.ColeHopf.exponentialSolution s (fun i => (c i : ℝ)) (fun i => (k i : ℝ))
      ν (x 0) (x 1)) - rectangularSum N (exponentialBurgersSeries s c k ν) x| ≤
        geometricTailBound mu r N := by
  rw [← (geometricSum_exponentialBurgersSeries s c k ν hc h0 h1 hi i0 i1 ii hx).1]
  exact abs_geometricSum_sub_rectangularSum_le hu iu N hx

end MvPowerSeries.ColeHopf
