/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

/-! # Bernstein's inequality

For independent centered random variables bounded almost surely by `M` with total
variance at most `V`, the sum has sub-exponential tails:
`P(t ≤ |∑ Xᵢ|) ≤ 2 exp (-t² / (2 (V + M t / 3)))`. This file covers
roadmap package ML-10 of the Atlas TCS canon roadmap.

Source: S. Bernstein (1924); see Boucheron, Lugosi and Massart,
Concentration Inequalities (2013), Section 2.7.
-/

open MeasureTheory ProbabilityTheory Finset

private lemma exp_eq_tsum (y : ℝ) :
    Real.exp y = ∑' n : ℕ, y ^ n / (n.factorial : ℝ) := by
  simp only [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

private lemma summable_shift_two {f : ℕ → ℝ} (hf : Summable f) :
    Summable (fun k : ℕ => f (k + 2)) :=
  (summable_nat_add_iff 2).mpr hf

private lemma tsum_eq_add_tsum_shift_two {f : ℕ → ℝ} (hf : Summable f) :
    ∑' b, f b = f 0 + f 1 + ∑' b, f (b + 2) := by
  have h1 : Summable (fun b => f (b + 1)) := (summable_nat_add_iff 1).mpr hf
  rw [hf.tsum_eq_zero_add, h1.tsum_eq_zero_add]
  show f 0 + (f 1 + ∑' b, f (b + 2)) = f 0 + f 1 + ∑' b, f (b + 2)
  ring

private lemma exp_sub_one_sub (y : ℝ) :
    Real.exp y - 1 - y = ∑' k : ℕ, y ^ (k + 2) / ((k + 2).factorial : ℝ) := by
  have hS := Real.summable_pow_div_factorial y
  have hE := exp_eq_tsum y
  rw [tsum_eq_add_tsum_shift_two hS] at hE
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
    Nat.factorial_one] at hE
  linarith

private lemma two_mul_three_pow_le_factorial (k : ℕ) :
    (2 : ℝ) * 3 ^ k ≤ ((k + 2).factorial : ℝ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h3 : (3 : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := by
      have h : 3 ≤ k + 3 := Nat.le_add_left 3 k
      exact_mod_cast h
    have hfact : (0 : ℝ) ≤ ((k + 2).factorial : ℝ) := Nat.cast_nonneg _
    have hstep : (k + 1 + 2) = (k + 2 + 1) := by omega
    calc (2 : ℝ) * 3 ^ (k + 1) = 3 * (2 * 3 ^ k) := by ring
      _ ≤ 3 * ((k + 2).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
      _ ≤ ((k + 3 : ℕ) : ℝ) * ((k + 2).factorial : ℝ) :=
          mul_le_mul_of_nonneg_right h3 hfact
      _ = ((((k + 1) + 2).factorial : ℕ) : ℝ) := by
          rw [hstep, Nat.factorial_succ (k + 2)]
          push_cast
          ring

private lemma exp_sub_one_sub_le {u : ℝ} (hu0 : 0 ≤ u) (hu3 : u < 3) :
    Real.exp u - 1 - u ≤ u ^ 2 / 2 / (1 - u / 3) := by
  have hS := Real.summable_pow_div_factorial u
  have hS2 : Summable (fun k : ℕ => u ^ (k + 2) / ((k + 2).factorial : ℝ)) :=
    summable_shift_two hS
  have hnorm : ‖u / 3‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hG : Summable (fun k : ℕ => (u ^ 2 / 2) * (u / 3) ^ k) :=
    Summable.mul_left _ (summable_geometric_of_norm_lt_one hnorm)
  have hle : (∑' k : ℕ, u ^ (k + 2) / ((k + 2).factorial : ℝ))
      ≤ ∑' k : ℕ, (u ^ 2 / 2) * (u / 3) ^ k := by
    apply Summable.tsum_le_tsum _ hS2 hG
    intro k
    have hF : (0 : ℝ) < ((k + 2).factorial : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hG0 : (0 : ℝ) < 2 * 3 ^ k := by positivity
    have hF2 : (2 : ℝ) * 3 ^ k ≤ ((k + 2).factorial : ℝ) :=
      two_mul_three_pow_le_factorial k
    have hpow : (0 : ℝ) ≤ u ^ (k + 2) := pow_nonneg hu0 _
    have h3k : (3 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    calc u ^ (k + 2) / ((k + 2).factorial : ℝ)
        ≤ u ^ (k + 2) / (2 * 3 ^ k) := by
          rw [div_le_div_iff₀ hF hG0]
          exact mul_le_mul_of_nonneg_left hF2 hpow
      _ = (u ^ 2 / 2) * (u / 3) ^ k := by
          rw [div_pow, pow_add]
          field_simp
  have hT2 : (∑' k : ℕ, (u ^ 2 / 2) * (u / 3) ^ k) = u ^ 2 / 2 / (1 - u / 3) := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm,
      div_eq_mul_inv (u ^ 2 / 2) (1 - u / 3)]
  rw [exp_sub_one_sub u]
  rw [hT2] at hle
  exact hle

private lemma bennett_scalar {lam M x : ℝ} (hlam : 0 ≤ lam) (hM : 0 < M) (hx : |x| ≤ M) :
    Real.exp (lam * x) ≤ 1 + lam * x
      + ((Real.exp (lam * M) - 1 - lam * M) / M ^ 2) * x ^ 2 := by
  have hT1 : Summable (fun k : ℕ => (lam * x) ^ (k + 2) / ((k + 2).factorial : ℝ)) :=
    summable_shift_two (Real.summable_pow_div_factorial (lam * x))
  have hT2 : Summable (fun k : ℕ => (lam * M) ^ (k + 2) / ((k + 2).factorial : ℝ)) :=
    summable_shift_two (Real.summable_pow_div_factorial (lam * M))
  have hM2 : (0 : ℝ) < M ^ 2 := pow_pos hM 2
  have hG : Summable (fun k : ℕ =>
      (x ^ 2 / M ^ 2) * ((lam * M) ^ (k + 2) / ((k + 2).factorial : ℝ))) :=
    Summable.mul_left _ hT2
  have hle : (∑' k : ℕ, (lam * x) ^ (k + 2) / ((k + 2).factorial : ℝ))
      ≤ ∑' k : ℕ, (x ^ 2 / M ^ 2) * ((lam * M) ^ (k + 2) / ((k + 2).factorial : ℝ)) := by
    apply Summable.tsum_le_tsum _ hT1 hG
    intro k
    have hF : (0 : ℝ) < ((k + 2).factorial : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hx2 : x ^ (k + 2) ≤ x ^ 2 * M ^ k := by
      calc x ^ (k + 2) ≤ |x| ^ (k + 2) := by rw [← abs_pow]; exact le_abs_self _
        _ = x ^ 2 * |x| ^ k := by rw [pow_add, sq_abs]; ring
        _ ≤ x ^ 2 * M ^ k := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg x)
            exact pow_le_pow_left₀ (abs_nonneg _) hx k
    have hlamk : (0 : ℝ) ≤ lam ^ (k + 2) := pow_nonneg hlam _
    have h1 : (lam * x) ^ (k + 2) ≤ (x ^ 2 / M ^ 2) * (lam * M) ^ (k + 2) := by
      rw [mul_pow, mul_pow]
      have h2 : lam ^ (k + 2) * x ^ (k + 2) ≤ lam ^ (k + 2) * (x ^ 2 * M ^ k) :=
        mul_le_mul_of_nonneg_left hx2 hlamk
      refine h2.trans_eq ?_
      have hMne : M ^ 2 ≠ 0 := ne_of_gt hM2
      field_simp
      ring
    calc (lam * x) ^ (k + 2) / ((k + 2).factorial : ℝ)
        ≤ ((x ^ 2 / M ^ 2) * (lam * M) ^ (k + 2)) / ((k + 2).factorial : ℝ) := by
          exact (div_le_div_iff_of_pos_right hF).mpr h1
      _ = (x ^ 2 / M ^ 2) * ((lam * M) ^ (k + 2) / ((k + 2).factorial : ℝ)) := by ring
  have hE1 := exp_sub_one_sub (lam * x)
  have hT2' : (∑' k : ℕ, (x ^ 2 / M ^ 2) * ((lam * M) ^ (k + 2) / ((k + 2).factorial : ℝ)))
      = (x ^ 2 / M ^ 2) * (Real.exp (lam * M) - 1 - lam * M) := by
    rw [tsum_mul_left, ← exp_sub_one_sub (lam * M)]
  rw [← hE1, hT2'] at hle
  have hring : (x ^ 2 / M ^ 2) * (Real.exp (lam * M) - 1 - lam * M)
      = ((Real.exp (lam * M) - 1 - lam * M) / M ^ 2) * x ^ 2 := by ring
  rw [hring] at hle
  linarith

private lemma integrable_exp_mul_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {lam M : ℝ} (hlam0 : 0 ≤ lam)
    (hXm : Measurable X) (hbdd : ∀ᵐ ω ∂P, |X ω| ≤ M) :
    Integrable (fun ω => Real.exp (lam * X ω)) P := by
  refine Integrable.of_bound
    (Real.measurable_exp.comp (hXm.const_mul lam)).aestronglyMeasurable
    (Real.exp (lam * M)) ?_
  filter_upwards [hbdd] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc lam * X ω ≤ lam * |X ω| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hlam0
    _ ≤ lam * M := mul_le_mul_of_nonneg_left hω hlam0

private lemma mgf_le_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {M : ℝ} {X : Ω → ℝ} {lam : ℝ}
    (hM : 0 < M) (hlam0 : 0 ≤ lam) (hlam3 : lam * M < 3)
    (hXm : Measurable X) (hmean : ∫ ω, X ω ∂P = 0) (hbdd : ∀ᵐ ω ∂P, |X ω| ≤ M) :
    mgf X P lam ≤ Real.exp (lam ^ 2 * (∫ ω, (X ω) ^ 2 ∂P) / 2 / (1 - lam * M / 3)) := by
  set A : ℝ := Real.exp (lam * M) - 1 - lam * M with hA
  set K : ℝ := A / M ^ 2 with hK
  have hM2 : (0 : ℝ) < M ^ 2 := pow_pos hM 2
  have hA0 : 0 ≤ A := by
    rw [hA]
    have h := Real.add_one_le_exp (lam * M)
    linarith
  have hσ0 : 0 ≤ ∫ ω, (X ω) ^ 2 ∂P :=
    integral_nonneg_of_ae (ae_of_all _ fun ω => sq_nonneg _)
  have hXe : Integrable (fun ω => Real.exp (lam * X ω)) P :=
    integrable_exp_mul_of_bounded hlam0 hXm hbdd
  have hX1 : Integrable X P := by
    refine Integrable.of_bound hXm.aestronglyMeasurable M ?_
    filter_upwards [hbdd] with ω hω
    rw [Real.norm_eq_abs]
    exact hω
  have hX2 : Integrable (fun ω => (X ω) ^ 2) P := by
    refine Integrable.of_bound (hXm.pow_const 2).aestronglyMeasurable (M ^ 2) ?_
    filter_upwards [hbdd] with ω hω
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  have hIntg : Integrable (fun ω => 1 + lam * X ω + K * (X ω) ^ 2) P :=
    ((integrable_const 1).add (hX1.const_mul lam)).add (hX2.const_mul K)
  have hmono : ∫ ω, Real.exp (lam * X ω) ∂P
      ≤ ∫ ω, (1 + lam * X ω + K * (X ω) ^ 2) ∂P := by
    apply integral_mono_ae hXe hIntg
    filter_upwards [hbdd] with ω hω
    exact bennett_scalar hlam0 hM hω
  have hreal : P.real Set.univ = 1 := by
    show (P Set.univ).toReal = 1
    rw [measure_univ, ENNReal.toReal_one]
  have hInt1 : ∫ ω, (1 : ℝ) ∂P = 1 := by
    rw [integral_const, hreal, one_smul]
  have hIntg_eq : ∫ ω, (1 + lam * X ω + K * (X ω) ^ 2) ∂P
      = 1 + K * (∫ ω, (X ω) ^ 2 ∂P) := by
    have e1 : ∫ ω, (1 + lam * X ω + K * (X ω) ^ 2) ∂P
        = ∫ ω, (1 + lam * X ω) ∂P + ∫ ω, K * (X ω) ^ 2 ∂P :=
      integral_add ((integrable_const 1).add (hX1.const_mul lam)) (hX2.const_mul K)
    have e2 : ∫ ω, (1 + lam * X ω) ∂P = ∫ ω, (1 : ℝ) ∂P + ∫ ω, lam * X ω ∂P :=
      integral_add (integrable_const 1) (hX1.const_mul lam)
    have e3 : ∫ ω, lam * X ω ∂P = lam * ∫ ω, X ω ∂P := integral_const_mul lam X
    have e4 : ∫ ω, K * (X ω) ^ 2 ∂P = K * ∫ ω, (X ω) ^ 2 ∂P :=
      integral_const_mul K _
    rw [e1, e2, e3, e4, hmean, hInt1]
    ring
  have hmgf : mgf X P lam ≤ 1 + K * (∫ ω, (X ω) ^ 2 ∂P) := by
    show (∫ ω, Real.exp (lam * X ω) ∂P) ≤ _
    rw [← hIntg_eq]
    exact hmono
  have hexp : (1 : ℝ) + K * (∫ ω, (X ω) ^ 2 ∂P)
      ≤ Real.exp (K * (∫ ω, (X ω) ^ 2 ∂P)) := by
    have h := Real.add_one_le_exp (K * (∫ ω, (X ω) ^ 2 ∂P))
    linarith
  have hden : (0 : ℝ) < 1 - lam * M / 3 := by linarith [hlam3]
  have hu : Real.exp (lam * M) - 1 - lam * M ≤ (lam * M) ^ 2 / 2 / (1 - lam * M / 3) :=
    exp_sub_one_sub_le (mul_nonneg hlam0 (le_of_lt hM)) hlam3
  have hKbound : K * (∫ ω, (X ω) ^ 2 ∂P)
      ≤ lam ^ 2 * (∫ ω, (X ω) ^ 2 ∂P) / 2 / (1 - lam * M / 3) := by
    rw [hK, hA]
    have h1 : ((Real.exp (lam * M) - 1 - lam * M) / M ^ 2) * (∫ ω, (X ω) ^ 2 ∂P)
        ≤ (((lam * M) ^ 2 / 2 / (1 - lam * M / 3)) / M ^ 2) * (∫ ω, (X ω) ^ 2 ∂P) := by
      apply mul_le_mul_of_nonneg_right _ hσ0
      exact (div_le_div_iff_of_pos_right hM2).mpr hu
    refine h1.trans_eq ?_
    have hMne : M ^ 2 ≠ 0 := ne_of_gt hM2
    have hdenne : (1 : ℝ) - lam * M / 3 ≠ 0 := ne_of_gt hden
    field_simp
  exact hmgf.trans (hexp.trans (Real.exp_le_exp.mpr hKbound))

private lemma prod_le_prod_of_nonneg {ι : Type*} {f g : ι → ℝ} :
    ∀ {s : Finset ι}, (∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, 0 ≤ g i) →
      (∀ i ∈ s, f i ≤ g i) → ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  intro s
  classical
  induction s using Finset.induction with
  | empty => intro _ _ _; simp
  | insert i s hi ih =>
      intro hf hg h
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact mul_le_mul (h i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hg j (Finset.mem_insert_of_mem hj))
          (fun j hj => h j (Finset.mem_insert_of_mem hj)))
        (Finset.prod_nonneg (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
        (hg i (Finset.mem_insert_self i s))

private lemma chernoff_exponent_eq {t M V D lam : ℝ} (hV : 0 < V) (hD0 : 0 < D)
    (hD : D = V + M * t / 3) (hlam : lam = t / D) :
    -lam * t + lam ^ 2 * V / 2 / (1 - lam * M / 3) = -(t ^ 2 / (2 * D)) := by
  have hDne : D ≠ 0 := ne_of_gt hD0
  have hVne : V ≠ 0 := ne_of_gt hV
  have hden_eq : 1 - lam * M / 3 = V / D := by
    rw [hlam, eq_div_iff hDne]
    have hDM : D - t * M / 3 = V := by rw [hD]; ring
    have htom : (1 - t / D * M / 3) * D = D - t * M / 3 := by
      field_simp
    rw [htom]
    exact hDM
  rw [hden_eq, hlam]
  have hVD : V / D ≠ 0 := div_ne_zero hVne hDne
  field_simp
  ring

private lemma bernstein_one_sided {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {M V t : ℝ} (hM : 0 < M) (hV : 0 < V) (ht : 0 < t)
    {X : Fin n → Ω → ℝ} (hX : iIndepFun X P) (hXm : ∀ i, Measurable (X i))
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hbdd : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ M)
    (hvar : ∑ i, ∫ ω, (X i ω) ^ 2 ∂P ≤ V) :
    P.real {ω | t ≤ ∑ i, X i ω} ≤ Real.exp (-(t ^ 2 / (2 * (V + M * t / 3)))) := by
  have hD0 : (0 : ℝ) < V + M * t / 3 := by
    have hMt : (0 : ℝ) ≤ M * t / 3 :=
      div_nonneg (mul_nonneg hM.le ht.le) (by norm_num)
    linarith
  have hlam0 : (0 : ℝ) ≤ t / (V + M * t / 3) := div_nonneg ht.le hD0.le
  have hlam3 : t / (V + M * t / 3) * M < 3 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hD0]
    linarith [hV]
  have hterm : ∀ i, mgf (X i) P (t / (V + M * t / 3))
      ≤ Real.exp ((t / (V + M * t / 3)) ^ 2 * (∫ ω, (X i ω) ^ 2 ∂P) / 2
        / (1 - t / (V + M * t / 3) * M / 3)) :=
    fun i => mgf_le_of_bounded hM hlam0 hlam3 (hXm i) (hmean i) (hbdd i)
  have hInt : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun ω => Real.exp (t / (V + M * t / 3) * X i ω)) P :=
    fun i _ => integrable_exp_mul_of_bounded hlam0 (hXm i) (hbdd i)
  have hIntSum : Integrable
      (fun ω => Real.exp (t / (V + M * t / 3) * (∑ i ∈ Finset.univ, X i) ω)) P :=
    iIndepFun.integrable_exp_mul_sum hX hXm hInt
  have hchern : P.real {ω | t ≤ (∑ i ∈ Finset.univ, X i) ω}
      ≤ Real.exp (-(t / (V + M * t / 3)) * t)
        * mgf (∑ i ∈ Finset.univ, X i) P (t / (V + M * t / 3)) :=
    measure_ge_le_exp_mul_mgf t hlam0 hIntSum
  have hset : {ω | t ≤ ∑ i, X i ω} = {ω | t ≤ (∑ i ∈ Finset.univ, X i) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [Finset.sum_apply]
  rw [hset]
  refine hchern.trans ?_
  rw [hX.mgf_sum hXm Finset.univ]
  have hprod : ∏ i ∈ (Finset.univ : Finset (Fin n)), mgf (X i) P (t / (V + M * t / 3))
      ≤ ∏ i ∈ Finset.univ, Real.exp ((t / (V + M * t / 3)) ^ 2 * (∫ ω, (X i ω) ^ 2 ∂P) / 2
        / (1 - t / (V + M * t / 3) * M / 3)) :=
    prod_le_prod_of_nonneg (fun i _ => mgf_nonneg) (fun i _ => (Real.exp_pos _).le)
      (fun i _ => hterm i)
  have hexp_sum : (∏ i ∈ (Finset.univ : Finset (Fin n)),
        Real.exp ((t / (V + M * t / 3)) ^ 2 * (∫ ω, (X i ω) ^ 2 ∂P) / 2
          / (1 - t / (V + M * t / 3) * M / 3)))
      = Real.exp (∑ i ∈ Finset.univ, (t / (V + M * t / 3)) ^ 2 * (∫ ω, (X i ω) ^ 2 ∂P) / 2
        / (1 - t / (V + M * t / 3) * M / 3)) :=
    (Real.exp_sum _ _).symm
  have hden : (0 : ℝ) < 1 - t / (V + M * t / 3) * M / 3 := by
    have h1 : t / (V + M * t / 3) * M / 3 < 1 := by linarith [hlam3]
    linarith
  have hcoef : (0 : ℝ) ≤ (t / (V + M * t / 3)) ^ 2 / 2 / (1 - t / (V + M * t / 3) * M / 3) :=
    div_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) hden.le
  have hsum : (∑ i ∈ (Finset.univ : Finset (Fin n)),
        (t / (V + M * t / 3)) ^ 2 * (∫ ω, (X i ω) ^ 2 ∂P) / 2
          / (1 - t / (V + M * t / 3) * M / 3))
      ≤ (t / (V + M * t / 3)) ^ 2 * V / 2 / (1 - t / (V + M * t / 3) * M / 3) := by
    have heq : (∑ i ∈ (Finset.univ : Finset (Fin n)),
          (t / (V + M * t / 3)) ^ 2 * (∫ ω, (X i ω) ^ 2 ∂P) / 2
            / (1 - t / (V + M * t / 3) * M / 3))
        = ((t / (V + M * t / 3)) ^ 2 / 2 / (1 - t / (V + M * t / 3) * M / 3))
          * ∑ i, ∫ ω, (X i ω) ^ 2 ∂P := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have heq2 : ((t / (V + M * t / 3)) ^ 2 / 2 / (1 - t / (V + M * t / 3) * M / 3)) * V
        = (t / (V + M * t / 3)) ^ 2 * V / 2 / (1 - t / (V + M * t / 3) * M / 3) := by
      ring
    rw [heq, ← heq2]
    exact mul_le_mul_of_nonneg_left hvar hcoef
  have hmgf_sum : ∏ i ∈ (Finset.univ : Finset (Fin n)), mgf (X i) P (t / (V + M * t / 3))
      ≤ Real.exp ((t / (V + M * t / 3)) ^ 2 * V / 2
        / (1 - t / (V + M * t / 3) * M / 3)) := by
    refine hprod.trans ?_
    rw [hexp_sum]
    exact Real.exp_le_exp.mpr hsum
  have hnonneg : (0 : ℝ) ≤ Real.exp (-(t / (V + M * t / 3)) * t) := (Real.exp_pos _).le
  refine (mul_le_mul_of_nonneg_left hmgf_sum hnonneg).trans_eq ?_
  rw [← Real.exp_add]
  congr 1
  exact chernoff_exponent_eq hV hD0 rfl rfl

/-- Bernstein's inequality: for independent centered random variables
bounded almost surely by `M`, with total variance at most `V`, the sum has
sub-exponential tails. -/
theorem bernstein_inequality {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} {M V t : ℝ}
    (hM : 0 ≤ M) (ht : 0 ≤ t)
    {X : Fin n → Ω → ℝ} (hX : iIndepFun X P) (hXm : ∀ i, Measurable (X i))
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hbdd : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ M)
    (hvar : ∑ i, ∫ ω, (X i ω) ^ 2 ∂P ≤ V) :
    P {ω | t ≤ |∑ i, X i ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / (2 * (V + M * t / 3))))) := by
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · rw [← ht0]
    have hexp : (-((0 : ℝ) ^ 2 / (2 * (V + M * 0 / 3)))) = 0 := by simp
    rw [hexp, Real.exp_zero, mul_one]
    calc P {ω | (0 : ℝ) ≤ |∑ i, X i ω|} ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (by norm_num)
  · by_cases hM0 : M = 0
    · have h0 : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 := by
        intro i
        filter_upwards [hbdd i] with ω hω
        apply abs_eq_zero.mp
        rw [hM0] at hω
        exact le_antisymm hω (abs_nonneg _)
      have hS : ∀ᵐ ω ∂P, ∑ i, X i ω = 0 := by
        filter_upwards [ae_all_iff.mpr h0] with ω hω
        exact Finset.sum_eq_zero (fun i _ => hω i)
      have hnull : P {ω | t ≤ |∑ i, X i ω|} = 0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [hS] with ω hω
        simpa only [Set.mem_ofPred_eq, hω, abs_zero] using not_le_of_gt htpos
      rw [hnull]
      exact zero_le
    · by_cases hV0 : V ≤ 0
      · have hσ0 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
            (0 : ℝ) ≤ ∫ ω, (X i ω) ^ 2 ∂P :=
          fun i _ => integral_nonneg_of_ae (ae_of_all _ fun ω => sq_nonneg _)
        have hsum0 : ∑ i, ∫ ω, (X i ω) ^ 2 ∂P = 0 :=
          le_antisymm (hvar.trans hV0) (Finset.sum_nonneg hσ0)
        have heach : ∀ i ∈ (Finset.univ : Finset (Fin n)),
            ∫ ω, (X i ω) ^ 2 ∂P = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg hσ0).mp hsum0
        have hX2i : ∀ i, Integrable (fun ω => (X i ω) ^ 2) P := by
          intro i
          refine Integrable.of_bound ((hXm i).pow_const 2).aestronglyMeasurable
            (M ^ 2) ?_
          filter_upwards [hbdd i] with ω hω
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) hω 2
        have hae : ∀ i, (fun ω => (X i ω) ^ 2) =ᵐ[P] 0 := fun i =>
          (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun ω => sq_nonneg _)
            (hX2i i)).mp (heach i (Finset.mem_univ i))
        have hXae : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 := by
          intro i
          filter_upwards [hae i] with ω hω
          simp only [Pi.zero_apply] at hω
          exact (pow_eq_zero_iff two_ne_zero).mp hω
        have hSae : ∀ᵐ ω ∂P, ∑ i, X i ω = 0 := by
          have hall : ∀ᵐ ω ∂P, ∀ i, X i ω = 0 := ae_all_iff.mpr hXae
          filter_upwards [hall] with ω hω
          exact Finset.sum_eq_zero (fun i _ => hω i)
        have hnull : P {ω | t ≤ |∑ i, X i ω|} = 0 := by
          have hmem : {ω | ∑ i, X i ω = 0} ∈ ae P := hSae
          have hnull0 : P {ω | ∑ i, X i ω = 0}ᶜ = 0 := mem_ae_iff.mp hmem
          have hsub : {ω | t ≤ |∑ i, X i ω|} ⊆ {ω | ∑ i, X i ω = 0}ᶜ := by
            intro ω hω
            show ω ∉ {ω | ∑ i, X i ω = 0}
            show ¬ ∑ i, X i ω = 0
            intro hcon
            have hω' : t ≤ |∑ i, X i ω| := hω
            rw [hcon, abs_zero] at hω'
            exact not_le_of_gt htpos hω'
          exact measure_mono_null hsub hnull0
        rw [hnull]
        exact zero_le
      · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
        have hVpos : 0 < V := not_le.mp hV0
        have h1 : P.real {ω | t ≤ ∑ i, X i ω}
            ≤ Real.exp (-(t ^ 2 / (2 * (V + M * t / 3)))) :=
          bernstein_one_sided hMpos hVpos htpos hX hXm hmean hbdd hvar
        have hYindep : iIndepFun (fun i => -(X i)) P :=
          hX.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
        have hYmeas : ∀ i, Measurable (-(X i)) := fun i => (hXm i).neg
        have hmean' : ∀ i, ∫ ω, (-(X i)) ω ∂P = 0 := by
          intro i
          simp only [Pi.neg_apply, integral_neg, hmean i, neg_zero]
        have hbdd' : ∀ i, ∀ᵐ ω ∂P, |(-(X i)) ω| ≤ M := by
          intro i
          simpa only [Pi.neg_apply, abs_neg] using hbdd i
        have hvar' : ∑ i, ∫ ω, ((-(X i)) ω) ^ 2 ∂P ≤ V := by
          simp only [Pi.neg_apply, neg_sq]
          exact hvar
        have h2 : P.real {ω | t ≤ ∑ i, (-(X i)) ω}
            ≤ Real.exp (-(t ^ 2 / (2 * (V + M * t / 3)))) :=
          bernstein_one_sided hMpos hVpos htpos hYindep hYmeas hmean' hbdd' hvar'
        have hYset : {ω | t ≤ ∑ i, (-(X i)) ω} = {ω | t ≤ -(∑ i, X i ω)} := by
          ext ω
          show (t ≤ ∑ i, (-(X i)) ω) ↔ (t ≤ -(∑ i, X i ω))
          have heq : (∑ i, (-(X i)) ω) = -(∑ i, X i ω) := by
            simp only [Pi.neg_apply]
            exact Finset.sum_neg_distrib _
          rw [heq]
        have hsub : {ω | t ≤ |∑ i, X i ω|}
            ⊆ {ω | t ≤ ∑ i, X i ω} ∪ {ω | t ≤ -(∑ i, X i ω)} := by
          intro ω hω
          show t ≤ ∑ i, X i ω ∨ t ≤ -(∑ i, X i ω)
          have hω' : t ≤ |∑ i, X i ω| := hω
          rcases le_total 0 (∑ i, X i ω) with hnn | hnp
          · left
            rwa [abs_of_nonneg hnn] at hω'
          · right
            rwa [abs_of_nonpos hnp] at hω'
        have hexp_nonneg : (0 : ℝ)
            ≤ Real.exp (-(t ^ 2 / (2 * (V + M * t / 3)))) :=
          (Real.exp_pos _).le
        have hA : P {ω | t ≤ ∑ i, X i ω}
            ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * (V + M * t / 3))))) := by
          have e : P {ω | t ≤ ∑ i, X i ω}
              = ENNReal.ofReal (P.real {ω | t ≤ ∑ i, X i ω}) :=
            (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
          rw [e]
          exact ENNReal.ofReal_le_ofReal h1
        have hB : P {ω | t ≤ -(∑ i, X i ω)}
            ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * (V + M * t / 3))))) := by
          have e : P {ω | t ≤ -(∑ i, X i ω)}
              = ENNReal.ofReal (P.real {ω | t ≤ -(∑ i, X i ω)}) :=
            (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
          rw [e]
          have h2' : P.real {ω | t ≤ -(∑ i, X i ω)}
              ≤ Real.exp (-(t ^ 2 / (2 * (V + M * t / 3)))) := by
            rw [← hYset]
            exact h2
          exact ENNReal.ofReal_le_ofReal h2'
        calc P {ω | t ≤ |∑ i, X i ω|}
            ≤ P ({ω | t ≤ ∑ i, X i ω} ∪ {ω | t ≤ -(∑ i, X i ω)}) :=
              measure_mono hsub
          _ ≤ P {ω | t ≤ ∑ i, X i ω} + P {ω | t ≤ -(∑ i, X i ω)} :=
              measure_union_le _ _
          _ ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * (V + M * t / 3)))))
              + ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * (V + M * t / 3))))) :=
              add_le_add hA hB
          _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / (2 * (V + M * t / 3))))) := by
              rw [← ENNReal.ofReal_add hexp_nonneg hexp_nonneg]
              congr 1
              ring
