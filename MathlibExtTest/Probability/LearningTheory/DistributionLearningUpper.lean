/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.DistributionLearningUpper
public import Mathlib.Data.Fintype.Card
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Monad

import Mathlib.Tactic.NormNum

/-- Computation: the two-point alphabet has card `2`. -/
example : Fintype.card (Fin 2) = 2 := rfl

/-- Computation: deviation bound on `Fin 2` with five samples. -/
example :
    (∑ x ∈ Finset.univ.filter (fun x : Fin 5 → Fin 2 =>
      decide ((1 : ℝ) ≤ (∑ a, |empFreq x a -
        ((PMF.pure 0 : PMF (Fin 2)) a).toReal|) -
        Real.sqrt (Fintype.card (Fin 2) / 5))),
      ∏ i, (((PMF.pure 0 : PMF (Fin 2)) (x i)).toReal)) ≤
    Real.exp (-(5 : ℝ) * 1 ^ 2 / 2) :=
  empFreq_l1_deviation (PMF.pure (0 : Fin 2))
    (show (0 : ℕ) < 5 from by norm_num) 1
    (show (0 : ℝ) < 1 from by norm_num)

/-- Computation: confidence form on `Fin 2` with five samples. -/
example :
    (∑ x ∈ Finset.univ.filter (fun x : Fin 5 → Fin 2 =>
      decide (Real.sqrt ((Fintype.card (Fin 2) : ℝ) / 5) +
        Real.sqrt (2 * Real.log (1 / (1 / 2)) / 5) ≤
          ∑ a, |empFreq x a - ((PMF.pure 0 : PMF (Fin 2)) a).toReal|)),
      ∏ i, (((PMF.pure 0 : PMF (Fin 2)) (x i)).toReal)) ≤
    (1 / 2 : ℝ) :=
  empFreq_l1_high_probability (PMF.pure (0 : Fin 2))
    (show (0 : ℕ) < 5 from by norm_num) (1 / 2 : ℝ)
    (show (0 : ℝ) < 1 / 2 from by norm_num)
    (show (1 / 2 : ℝ) < 1 from by norm_num)

/-- Computation: total-variation form on `Fin 2` with five samples. -/
example :
    (∑ x ∈ Finset.univ.filter (fun x : Fin 5 → Fin 2 =>
      decide ((Real.sqrt ((Fintype.card (Fin 2) : ℝ) / 5) +
        Real.sqrt (2 * Real.log (1 / (1 / 2)) / 5)) / 2 ≤
          (∑ a, |empFreq x a - ((PMF.pure 0 : PMF (Fin 2)) a).toReal|) / 2)),
      ∏ i, (((PMF.pure 0 : PMF (Fin 2)) (x i)).toReal)) ≤
    (1 / 2 : ℝ) :=
  empFreq_tv_high_probability (PMF.pure (0 : Fin 2))
    (show (0 : ℕ) < 5 from by norm_num) (1 / 2 : ℝ)
    (show (0 : ℝ) < 1 / 2 from by norm_num)
    (show (1 / 2 : ℝ) < 1 from by norm_num)

/-- Sanity: the deviation bound at `n = 5`, `t = 1` is below one. -/
example : Real.exp (-(5 : ℝ) * 1 ^ 2 / 2) < 1 := by
  rw [Real.exp_lt_one_iff]
  norm_num

/-- Test law on `Fin 2`: mass `9 / 10` at `0`, `1 / 10` at `1`. -/
private noncomputable def testLaw : PMF (Fin 2) :=
  PMF.ofFintype (fun a => if a = 0 then ENNReal.ofReal (9 / 10) else ENNReal.ofReal (1 / 10)) (by
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    rw [Fin.sum_univ_two]
    simp only [ite_true, h10, ite_false]
    have h : (9 / 10 : ℝ) + 1 / 10 = 1 := by norm_num
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), h, ENNReal.ofReal_one])

/-- Computation: deviation bound on `Fin 2` with one sample, biased law. -/
example :
    (∑ x ∈ Finset.univ.filter (fun x : Fin 1 → Fin 2 =>
      decide ((3 / 10 : ℝ) ≤ (∑ a, |empFreq x a -
        (testLaw a).toReal|) -
        Real.sqrt (Fintype.card (Fin 2) / ((1 : ℕ) : ℝ)))),
      ∏ i, ((testLaw (x i)).toReal)) ≤
    Real.exp (-((1 : ℕ) : ℝ) * (3 / 10) ^ 2 / 2) :=
  empFreq_l1_deviation testLaw
    (show (0 : ℕ) < 1 from by norm_num) (3 / 10 : ℝ)
    (show (0 : ℝ) < 3 / 10 from by norm_num)

/-- Computation: confidence form on `Fin 2` with one sample, biased law. -/
example :
    (∑ x ∈ Finset.univ.filter (fun x : Fin 1 → Fin 2 =>
      decide (Real.sqrt ((Fintype.card (Fin 2) : ℝ) / ((1 : ℕ) : ℝ)) +
        Real.sqrt (2 * Real.log (1 / (19 / 20)) / ((1 : ℕ) : ℝ)) ≤
          ∑ a, |empFreq x a - (testLaw a).toReal|)),
      ∏ i, ((testLaw (x i)).toReal)) ≤
    (19 / 20 : ℝ) :=
  empFreq_l1_high_probability testLaw
    (show (0 : ℕ) < 1 from by norm_num) (19 / 20 : ℝ)
    (show (0 : ℝ) < 19 / 20 from by norm_num)
    (show (19 / 20 : ℝ) < 1 from by norm_num)

/-- Computation: total-variation form on `Fin 2` with one sample, biased law. -/
example :
    (∑ x ∈ Finset.univ.filter (fun x : Fin 1 → Fin 2 =>
      decide ((Real.sqrt ((Fintype.card (Fin 2) : ℝ) / ((1 : ℕ) : ℝ)) +
        Real.sqrt (2 * Real.log (1 / (19 / 20)) / ((1 : ℕ) : ℝ))) / 2 ≤
          (∑ a, |empFreq x a - (testLaw a).toReal|) / 2)),
      ∏ i, ((testLaw (x i)).toReal)) ≤
    (19 / 20 : ℝ) :=
  empFreq_tv_high_probability testLaw
    (show (0 : ℕ) < 1 from by norm_num) (19 / 20 : ℝ)
    (show (0 : ℝ) < 19 / 20 from by norm_num)
    (show (19 / 20 : ℝ) < 1 from by norm_num)

/-- Positivity: the one-sample deviation event has positive weight. -/
example : 0 < (∑ x ∈ Finset.univ.filter (fun x : Fin 1 → Fin 2 =>
    decide ((3 / 10 : ℝ) ≤ (∑ a, |empFreq x a - (testLaw a).toReal|) -
      Real.sqrt (Fintype.card (Fin 2) / ((1 : ℕ) : ℝ)))),
    ∏ i, ((testLaw (x i)).toReal)) := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have he0 : empFreq (fun _ : Fin 1 => (1 : Fin 2)) 0 = 0 := by
    simp [empFreq, h10]
  have he1 : empFreq (fun _ : Fin 1 => (1 : Fin 2)) 1 = 1 := by
    simp [empFreq]
  have hp0 : (testLaw 0).toReal = 9 / 10 := by
    unfold testLaw
    simp only [PMF.ofFintype_apply, ite_true]
    exact ENNReal.toReal_ofReal (by norm_num)
  have hp1 : (testLaw 1).toReal = 1 / 10 := by
    unfold testLaw
    simp only [PMF.ofFintype_apply, h10, ite_false]
    exact ENNReal.toReal_ofReal (by norm_num)
  have hL1 : (∑ a, |empFreq (fun _ : Fin 1 => (1 : Fin 2)) a -
      (testLaw a).toReal|) = 9 / 5 := by
    rw [Fin.sum_univ_two, he0, he1, hp0, hp1]
    norm_num
  have hsqrt : Real.sqrt (Fintype.card (Fin 2) / ((1 : ℕ) : ℝ)) =
      Real.sqrt 2 := by
    simp [Fintype.card_fin]
  have hmem : (fun _ : Fin 1 => (1 : Fin 2)) ∈ Finset.univ.filter
      (fun x : Fin 1 → Fin 2 =>
        decide ((3 / 10 : ℝ) ≤ (∑ a, |empFreq x a - (testLaw a).toReal|) -
          Real.sqrt (Fintype.card (Fin 2) / ((1 : ℕ) : ℝ)))) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    rw [hL1, hsqrt]
    have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_iff]
      norm_num
    linarith
  have hnn : ∀ x ∈ Finset.univ.filter (fun x : Fin 1 → Fin 2 =>
      decide ((3 / 10 : ℝ) ≤ (∑ a, |empFreq x a - (testLaw a).toReal|) -
        Real.sqrt (Fintype.card (Fin 2) / ((1 : ℕ) : ℝ)))),
      0 ≤ ∏ i, ((testLaw (x i)).toReal) := by
    intro x _
    exact Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg
  have hw : (∏ i, (testLaw ((fun _ : Fin 1 => (1 : Fin 2)) i)).toReal) =
      1 / 10 := by
    rw [Fin.prod_univ_one]
    show (testLaw 1).toReal = 1 / 10
    exact hp1
  have hle := Finset.single_le_sum hnn hmem
  simp only [hw] at hle
  calc (0 : ℝ) < 1 / 10 := by norm_num
    _ ≤ _ := hle

/-- Sharpness: the one-sample deviation event has weight exactly `1 / 10`. -/
example : (∑ x ∈ Finset.univ.filter (fun x : Fin 1 → Fin 2 =>
    decide ((3 / 10 : ℝ) ≤ (∑ a, |empFreq x a - (testLaw a).toReal|) -
      Real.sqrt (Fintype.card (Fin 2) / ((1 : ℕ) : ℝ)))),
    ∏ i, ((testLaw (x i)).toReal)) = 1 / 10 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have he0 : empFreq (fun _ : Fin 1 => (1 : Fin 2)) 0 = 0 := by
    simp [empFreq, h10]
  have he1 : empFreq (fun _ : Fin 1 => (1 : Fin 2)) 1 = 1 := by
    simp [empFreq]
  have he0' : empFreq (fun _ : Fin 1 => (0 : Fin 2)) 0 = 1 := by
    simp [empFreq]
  have he1' : empFreq (fun _ : Fin 1 => (0 : Fin 2)) 1 = 0 := by
    simp [empFreq, h01]
  have hp0 : (testLaw 0).toReal = 9 / 10 := by
    unfold testLaw
    simp only [PMF.ofFintype_apply, ite_true]
    exact ENNReal.toReal_ofReal (by norm_num)
  have hp1 : (testLaw 1).toReal = 1 / 10 := by
    unfold testLaw
    simp only [PMF.ofFintype_apply, h10, ite_false]
    exact ENNReal.toReal_ofReal (by norm_num)
  have hL1 : (∑ a, |empFreq (fun _ : Fin 1 => (1 : Fin 2)) a -
      (testLaw a).toReal|) = 9 / 5 := by
    rw [Fin.sum_univ_two, he0, he1, hp0, hp1]
    norm_num
  have hL1' : (∑ a, |empFreq (fun _ : Fin 1 => (0 : Fin 2)) a -
      (testLaw a).toReal|) = 1 / 5 := by
    rw [Fin.sum_univ_two, he0', he1', hp0, hp1]
    norm_num
  have hsqrt : Real.sqrt (Fintype.card (Fin 2) / ((1 : ℕ) : ℝ)) =
      Real.sqrt 2 := by
    simp [Fintype.card_fin]
  have hP1 : (3 / 10 : ℝ) ≤ (∑ a, |empFreq (fun _ : Fin 1 => (1 : Fin 2)) a -
      (testLaw a).toReal|) - Real.sqrt (Fintype.card (Fin 2) / ((1 : ℕ) : ℝ)) := by
    rw [hL1, hsqrt]
    have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_iff]
      norm_num
    linarith
  have hP0 : ¬ ((3 / 10 : ℝ) ≤ (∑ a, |empFreq (fun _ : Fin 1 => (0 : Fin 2)) a -
      (testLaw a).toReal|) - Real.sqrt (Fintype.card (Fin 2) / ((1 : ℕ) : ℝ))) := by
    rw [hL1', hsqrt]
    intro h
    have hsq := Real.sqrt_nonneg 2
    linarith
  have hconst : ∀ x : Fin 1 → Fin 2, x = fun _ => x 0 := by
    intro x
    funext i
    show x i = x 0
    rw [show i = 0 from by omega]
  have hdich : ∀ a : Fin 2, a = 0 ∨ a = 1 :=
    fun a => Fin.exists_fin_two.mp ⟨a, rfl⟩
  have hfilter : Finset.univ.filter (fun x : Fin 1 → Fin 2 =>
      decide ((3 / 10 : ℝ) ≤ (∑ a, |empFreq x a - (testLaw a).toReal|) -
        Real.sqrt (Fintype.card (Fin 2) / ((1 : ℕ) : ℝ)))) =
      {(fun _ => (1 : Fin 2))} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      decide_eq_true_eq]
    have hx := hconst x
    rcases hdich (x 0) with h0 | h1
    · have hx0 : x = fun _ => (0 : Fin 2) := by rw [hx, h0]
      constructor
      · intro hPx
        rw [hx0] at hPx
        exact absurd hPx hP0
      · intro hcontra
        rw [hx0] at hcontra
        have h02 : (0 : Fin 2) = 1 := congrFun hcontra 0
        exact absurd h02 h01
    · have hx1 : x = fun _ => (1 : Fin 2) := by rw [hx, h1]
      constructor
      · intro _
        exact hx1
      · intro _
        rw [hx1]
        exact hP1
  have hw : (∏ i, (testLaw ((fun _ : Fin 1 => (1 : Fin 2)) i)).toReal) =
      1 / 10 := by
    rw [Fin.prod_univ_one]
    show (testLaw 1).toReal = 1 / 10
    exact hp1
  rw [hfilter, Finset.sum_singleton]
  exact hw

#print axioms empFreq_l1_deviation
#print axioms empFreq_l1_high_probability
#print axioms empFreq_tv_high_probability
