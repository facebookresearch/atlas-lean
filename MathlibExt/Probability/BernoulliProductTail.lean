/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Notation
public import Mathlib.MeasureTheory.Constructions.Pi
public import MathlibExt.Probability.Combinatorics.RandomSubset
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Real
import MathlibExt.Probability.HoeffdingBounded

/-!
# Tail bounds for heterogeneous Bernoulli products

Independent heterogeneous Bernoulli coordinates under `randomSubsetLaw`: each coordinate `i`
is `1` with probability `p i` and `0` otherwise. The probability that the coordinate sum
reaches a threshold admits an exact finite expansion over outcome strings, and Hoeffding's
inequality gives exponential upper and lower tail bounds.

## Main results

* `integral_coordVar`: the mean of coordinate `i` is `p i`.
* `iIndepFun_coordVar`: the coordinates are independent.
* `measureReal_sum_ge_eq_sum`: exact finite threshold expansion.
* `measureReal_sum_ge_le_exp`: Hoeffding upper tail bound.
* `measureReal_sum_le_le_exp`: Hoeffding lower tail bound.

References: W. Hoeffding, Probability inequalities for sums of bounded random variables,
Journal of the American Statistical Association 58 (1963), 13-30.
-/

@[expose] public section

namespace MathlibExt.Probability.BernoulliProductTail

open MeasureTheory ProbabilityTheory Real
open MathlibExt.Probability.Combinatorics.RandomSubset
open scoped BigOperators NNReal ProbabilityTheory unitInterval

/-- **Coordinate variable.** The indicator that coordinate `i` of the outcome `ω` is `true`:
`1` if `ω i` is `true` and `0` otherwise. -/
noncomputable def coordVar {α : Type*} [Fintype α] (i : α) (ω : α → Bool) : ℝ :=
  if ω i then 1 else 0

/-- **Mean of a coordinate variable.** The expectation of `coordVar i` under
`randomSubsetLaw p` equals the success probability `p i`. -/
theorem integral_coordVar {α : Type*} [Fintype α] (p : α → I) (i : α) :
    (randomSubsetLaw p)[coordVar i] = (p i : ℝ) := by
  have hf : AEStronglyMeasurable (fun b : Bool => if b then (1 : ℝ) else 0)
      (bernoulliMeasure true false (p i)) :=
    Measurable.aestronglyMeasurable Measurable.of_discrete
  have hcomp := integral_comp_eval
    (μ := fun j => bernoulliMeasure true false (p j))
    (f := fun b : Bool => if b then (1 : ℝ) else 0) (i := i) hf
  have hbern := integral_bernoulliMeasure (x := true) (y := false)
    (p := p i) (fun b : Bool => if b then (1 : ℝ) else 0)
  change ∫ ω, coordVar i ω ∂(randomSubsetLaw p) = (p i : ℝ)
  unfold randomSubsetLaw coordVar
  rw [hcomp]
  rw [hbern]
  simp

/-- **Independence of the coordinate variables.** The family `coordVar` of coordinate
indicators is independent under `randomSubsetLaw p`. -/
theorem iIndepFun_coordVar {α : Type*} [Fintype α] (p : α → I) :
    iIndepFun coordVar (randomSubsetLaw p) := by
  unfold randomSubsetLaw
  have hX : ∀ i : α, AEMeasurable
      (fun b : Bool => if b then (1 : ℝ) else 0)
      (bernoulliMeasure true false (p i)) := by
    intro i
    exact Measurable.aemeasurable Measurable.of_discrete
  have h := iIndepFun_pi
    (μ := fun i => bernoulliMeasure true false (p i))
    (X := fun _ b => if b then (1 : ℝ) else 0) hX
  have heq : coordVar (α := α) = fun i ω => (if ω i then (1 : ℝ) else 0) := rfl
  rw [heq]
  exact h

/-- **Exact finite threshold expansion.** The probability under `randomSubsetLaw p` that the
coordinate sum reaches `T` equals the sum, over all outcome strings `b` meeting the threshold,
of the product of the coordinate masses. -/
theorem measureReal_sum_ge_eq_sum {k : ℕ} (p : Fin k → I) (T : ℝ) :
    (randomSubsetLaw p).real {ω | T ≤ ∑ i, coordVar i ω} =
      ∑ b ∈ Finset.univ.filter (fun b => T ≤ ∑ i, coordVar i b),
        ∏ i, if b i then (p i : ℝ) else 1 - (p i : ℝ) := by
  have hset : ({ω : Fin k → Bool | T ≤ ∑ i, coordVar i ω} : Set (Fin k → Bool)) =
      ↑(Finset.univ.filter (fun b : Fin k → Bool => T ≤ ∑ i, coordVar i b)) := by
    ext ω
    simp
  rw [hset, ← sum_measureReal_singleton]
  apply Finset.sum_congr rfl
  intro b _
  rw [randomSubsetLaw_real_singleton]

/-- **Hoeffding upper tail bound.** If every success probability `p i` is at most `s` and
`(k : ℝ) * s ≤ T`, the probability that the coordinate sum reaches `T` is at most
`Real.exp (-2 * (T - k * s) ^ 2 / k)`. At `k = 0` the exponent divides by the real cast of
`k`, so the bound is `Real.exp 0 = 1` by real division, and the inequality is the trivial
probability bound. -/
theorem measureReal_sum_ge_le_exp {k : ℕ} (p : Fin k → I) (s T : ℝ)
    (hs : ∀ i, (p i : ℝ) ≤ s) (hT : (k : ℝ) * s ≤ T) :
    (randomSubsetLaw p).real {ω | T ≤ ∑ i, coordVar i ω} ≤
      Real.exp (-2 * (T - k * s) ^ 2 / k) := by
  by_cases hk : k = 0
  · subst hk
    simp only [Nat.cast_zero, zero_mul] at hT ⊢
    have hle1 : (randomSubsetLaw p).real
        {ω | T ≤ ∑ i, coordVar i ω} ≤ 1 := measureReal_le_one
    have hexp : Real.exp (-2 * (T - (0 : ℝ) * s) ^ 2 / (0 : ℝ)) = 1 := by simp
    simp
  · have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
    have h_indep : iIndepFun coordVar (randomSubsetLaw p) :=
      iIndepFun_coordVar p
    have hmeas : ∀ i, AEMeasurable (coordVar i)
        (randomSubsetLaw p) := by
      intro i
      apply Measurable.aemeasurable
      have hf : Measurable (fun b : Bool => if b then (1 : ℝ) else 0) :=
        Measurable.of_discrete
      have heval : Measurable (fun ω : Fin k → Bool => ω i) :=
        measurable_pi_apply i
      exact hf.comp heval
    have hZ : ∀ i, ∀ᵐ ω ∂(randomSubsetLaw p),
        coordVar i ω ∈ Set.Icc (0 : ℝ) 1 := by
      intro i
      apply Filter.Eventually.of_forall
      intro ω
      show coordVar i ω ∈ Set.Icc (0 : ℝ) 1
      unfold coordVar
      cases h : ω i <;> simp
    set t : ℝ := T / (k : ℝ) - s with htdef
    have hs_le : s ≤ T / (k : ℝ) := by
      rw [le_div_iff₀ hkpos]
      have := hT
      linarith [mul_comm ((k : ℝ)) s]
    have ht : 0 ≤ t := by
      rw [htdef]
      linarith
    have hL2 : ∀ i, (randomSubsetLaw p)[coordVar i] = (p i : ℝ) :=
      fun i => integral_coordVar p i
    have hsum_eq : ∑ i, (randomSubsetLaw p)[coordVar i] = ∑ i, (p i : ℝ) :=
      Finset.sum_congr rfl (fun i _ => hL2 i)
    have hsum_le : ∑ i, (randomSubsetLaw p)[coordVar i] ≤ (k : ℝ) * s := by
      rw [hsum_eq]
      calc ∑ i, (p i : ℝ) ≤ ∑ _i : Fin k, s :=
            Finset.sum_le_sum (fun i _ => hs i)
        _ = (k : ℝ) * s := by simp [Finset.sum_const, Finset.card_univ]
    have h1k_pos : (0 : ℝ) < 1 / (k : ℝ) := by positivity
    have hsub : {ω : Fin k → Bool | T ≤ ∑ i, coordVar i ω} ⊆
        {ω | t ≤ (1 / (k : ℝ)) * ∑ i, coordVar i ω -
          (1 / (k : ℝ)) * ∑ i, (randomSubsetLaw p)[coordVar i]} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [htdef]
      have hST : T / (k : ℝ) ≤ (1 / (k : ℝ)) * ∑ i, coordVar i ω := by
        have hmul : (1 / (k : ℝ)) * T ≤ (1 / (k : ℝ)) * ∑ i, coordVar i ω :=
          mul_le_mul_of_nonneg_left hω (le_of_lt h1k_pos)
        have heq : (1 / (k : ℝ)) * T = T / (k : ℝ) := by ring
        linarith
      have hM : (1 / (k : ℝ)) *
          ∑ i, (randomSubsetLaw p)[coordVar i] ≤ s := by
        have hmul : (1 / (k : ℝ)) *
            ∑ i, (randomSubsetLaw p)[coordVar i] ≤
            (1 / (k : ℝ)) * ((k : ℝ) * s) :=
          mul_le_mul_of_nonneg_left hsum_le (le_of_lt h1k_pos)
        have heq : (1 / (k : ℝ)) * ((k : ℝ) * s) = s := by field_simp
        linarith
      linarith
    have hmono := measureReal_mono hsub
      (measure_ne_top (randomSubsetLaw p) _)
    have hbound :=
      MathlibExt.Probability.HoeffdingBounded.measureReal_avg_sub_ge_le
        (μ := randomSubsetLaw p) (Z := coordVar) (n := k)
        h_indep hmeas (a := (0 : ℝ)) (b := (1 : ℝ)) hZ ht
    have hexp_eq : (-2 * (k : ℝ) * t ^ 2 / (1 - 0) ^ 2 : ℝ) =
        (-2 * (T - (k : ℝ) * s) ^ 2 / (k : ℝ) : ℝ) := by
      rw [htdef]
      field_simp
      ring
    calc (randomSubsetLaw p).real {ω | T ≤ ∑ i, coordVar i ω}
        ≤ (randomSubsetLaw p).real
          {ω | t ≤ (1 / (k : ℝ)) * ∑ i, coordVar i ω -
            (1 / (k : ℝ)) * ∑ i, (randomSubsetLaw p)[coordVar i]} :=
          hmono
      _ ≤ Real.exp (-2 * (k : ℝ) * t ^ 2 / (1 - 0) ^ 2) := hbound
      _ = Real.exp (-2 * (T - (k : ℝ) * s) ^ 2 / (k : ℝ)) := by rw [hexp_eq]
      _ = Real.exp (-2 * (T - k * s) ^ 2 / k) := by norm_cast

/-- **Hoeffding lower tail bound.** If every `c ≤ p i` and `T ≤ (k : ℝ) * c`, the probability
that the coordinate sum is at most `T` is at most
`Real.exp (-2 * (k * c - T) ^ 2 / k)`. At `k = 0` the exponent divides by the real cast of
`k`, so the bound is `Real.exp 0 = 1` by real division, and the inequality is the trivial
probability bound. -/
theorem measureReal_sum_le_le_exp {k : ℕ} (p : Fin k → I) (c T : ℝ)
    (hc : ∀ i, c ≤ (p i : ℝ)) (hT : T ≤ (k : ℝ) * c) :
    (randomSubsetLaw p).real {ω | ∑ i, coordVar i ω ≤ T} ≤
      Real.exp (-2 * (k * c - T) ^ 2 / k) := by
  by_cases hk : k = 0
  · subst hk
    simp only [Nat.cast_zero, zero_mul] at hT ⊢
    have hle1 : (randomSubsetLaw p).real
        {ω | ∑ i, coordVar i ω ≤ T} ≤ 1 := measureReal_le_one
    have hexp : Real.exp (-2 * ((0 : ℝ) * c - T) ^ 2 / (0 : ℝ)) = 1 := by simp
    simp
  · have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
    have h_indep : iIndepFun
        (fun (i : Fin k) (ω : Fin k → Bool) => 1 - coordVar i ω)
        (randomSubsetLaw p) := by
      unfold randomSubsetLaw
      have hX : ∀ i : Fin k, AEMeasurable
          (fun b : Bool => 1 - (if b then (1 : ℝ) else 0))
          (bernoulliMeasure true false (p i)) := by
        intro i
        exact Measurable.aemeasurable Measurable.of_discrete
      have h := iIndepFun_pi
        (μ := fun i => bernoulliMeasure true false (p i))
        (X := fun _ b => 1 - (if b then (1 : ℝ) else 0)) hX
      have heq : (fun (i : Fin k) (ω : Fin k → Bool) => 1 - coordVar i ω) =
          fun i ω => (fun (_ : Fin k) (b : Bool) =>
            1 - (if b then (1 : ℝ) else 0)) i (ω i) := by
        unfold coordVar
        rfl
      rw [heq]
      exact h
    have hmeas : ∀ i, AEMeasurable
        ((fun (i : Fin k) (ω : Fin k → Bool) => 1 - coordVar i ω) i)
        (randomSubsetLaw p) := by
      intro i
      apply Measurable.aemeasurable
      have hf : Measurable
          (fun b : Bool => 1 - (if b then (1 : ℝ) else 0)) :=
        Measurable.of_discrete
      have heval : Measurable (fun ω : Fin k → Bool => ω i) :=
        measurable_pi_apply i
      have hcomp : Measurable
          ((fun b : Bool => 1 - (if b then (1 : ℝ) else 0)) ∘
            (fun ω : Fin k → Bool => ω i)) := hf.comp heval
      have heq : ((fun (i : Fin k) (ω : Fin k → Bool) => 1 - coordVar i ω) i) =
          ((fun b : Bool => 1 - (if b then (1 : ℝ) else 0)) ∘
            (fun ω : Fin k → Bool => ω i)) := by
        unfold coordVar
        rfl
      rw [heq]
      exact hcomp
    have hZ : ∀ i, ∀ᵐ ω ∂(randomSubsetLaw p),
        (fun (i : Fin k) (ω : Fin k → Bool) => 1 - coordVar i ω) i ω ∈
          Set.Icc (0 : ℝ) 1 := by
      intro i
      apply Filter.Eventually.of_forall
      intro ω
      change (1 - coordVar i ω) ∈ Set.Icc (0 : ℝ) 1
      unfold coordVar
      cases h : ω i <;> simp
    have hsum_id : ∀ ω : Fin k → Bool,
        ∑ i, (1 - coordVar i ω) = (k : ℝ) - ∑ i, coordVar i ω := by
      intro ω
      rw [Finset.sum_sub_distrib]
      congr 1
      simp [Finset.sum_const, Finset.card_univ]
    have hL2f : ∀ i, ∫ ω, (1 - coordVar i ω)
        ∂(randomSubsetLaw p) = 1 - (p i : ℝ) := by
      intro i
      have hf : AEStronglyMeasurable
          (fun b : Bool => 1 - (if b then (1 : ℝ) else 0))
          (bernoulliMeasure true false (p i)) :=
        Measurable.aestronglyMeasurable Measurable.of_discrete
      have hcomp := integral_comp_eval
        (μ := fun j => bernoulliMeasure true false (p j))
        (f := fun b : Bool => 1 - (if b then (1 : ℝ) else 0)) (i := i) hf
      have hbern := integral_bernoulliMeasure (x := true) (y := false)
        (p := p i)
        (fun b : Bool => 1 - (if b then (1 : ℝ) else 0))
      have heq : (fun ω : Fin k → Bool => 1 - coordVar i ω) =
          (fun ω => (fun b : Bool => 1 - (if b then (1 : ℝ) else 0)) (ω i)) := by
        unfold coordVar
        rfl
      rw [heq]
      unfold randomSubsetLaw
      rw [hcomp, hbern]
      simp
    have hsum_eq : ∑ i, ∫ ω, (1 - coordVar i ω)
        ∂(randomSubsetLaw p) = ∑ i, (1 - (p i : ℝ)) :=
      Finset.sum_congr rfl (fun i _ => hL2f i)
    set s' : ℝ := 1 - c with hs'def
    set T' : ℝ := (k : ℝ) - T with hT'def
    have hs'_bound : ∀ i, (1 - (p i : ℝ)) ≤ s' := by
      intro i
      rw [hs'def]
      have := hc i
      linarith
    have hT'_bound : (k : ℝ) * s' ≤ T' := by
      rw [hs'def, hT'def]
      have := hT
      linarith
    have hsum_le : ∑ i, ∫ ω, (1 - coordVar i ω)
        ∂(randomSubsetLaw p) ≤ (k : ℝ) * s' := by
      rw [hsum_eq]
      calc ∑ i, (1 - (p i : ℝ)) ≤ ∑ _i : Fin k, s' :=
            Finset.sum_le_sum (fun i _ => hs'_bound i)
        _ = (k : ℝ) * s' := by simp [Finset.sum_const, Finset.card_univ]
    set t : ℝ := T' / (k : ℝ) - s' with htdef
    have hs_le : s' ≤ T' / (k : ℝ) := by
      rw [le_div_iff₀ hkpos]
      have := hT'_bound
      linarith [mul_comm ((k : ℝ)) s']
    have ht : 0 ≤ t := by
      rw [htdef]
      linarith
    have h1k_pos : (0 : ℝ) < 1 / (k : ℝ) := by positivity
    have hsub : {ω : Fin k → Bool | T' ≤ ∑ i, (1 - coordVar i ω)} ⊆
        {ω | t ≤ (1 / (k : ℝ)) * ∑ i, (1 - coordVar i ω) -
          (1 / (k : ℝ)) * ∑ i, ∫ ω, (1 - coordVar i ω)
            ∂(randomSubsetLaw p)} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [htdef]
      have hST : T' / (k : ℝ) ≤ (1 / (k : ℝ)) * ∑ i, (1 - coordVar i ω) := by
        have hmul : (1 / (k : ℝ)) * T' ≤
            (1 / (k : ℝ)) * ∑ i, (1 - coordVar i ω) :=
          mul_le_mul_of_nonneg_left hω (le_of_lt h1k_pos)
        have heq : (1 / (k : ℝ)) * T' = T' / (k : ℝ) := by ring
        linarith
      have hM : (1 / (k : ℝ)) * ∑ i, ∫ ω, (1 - coordVar i ω)
          ∂(randomSubsetLaw p) ≤ s' := by
        have hmul : (1 / (k : ℝ)) * ∑ i, ∫ ω, (1 - coordVar i ω)
            ∂(randomSubsetLaw p) ≤ (1 / (k : ℝ)) * ((k : ℝ) * s') :=
          mul_le_mul_of_nonneg_left hsum_le (le_of_lt h1k_pos)
        have heq : (1 / (k : ℝ)) * ((k : ℝ) * s') = s' := by field_simp
        linarith
      linarith
    have hmono := measureReal_mono hsub
      (measure_ne_top (randomSubsetLaw p) _)
    have hbound0 :=
      MathlibExt.Probability.HoeffdingBounded.measureReal_avg_sub_ge_le
        (μ := randomSubsetLaw p)
        (Z := fun (i : Fin k) (ω : Fin k → Bool) => 1 - coordVar i ω)
        (n := k) h_indep hmeas (a := (0 : ℝ)) (b := (1 : ℝ)) hZ ht
    have hbound : (randomSubsetLaw p).real
        {ω | t ≤ (1 / (k : ℝ)) * ∑ i, (1 - coordVar i ω) -
          (1 / (k : ℝ)) * ∑ i, ∫ ω, (1 - coordVar i ω)
            ∂(randomSubsetLaw p)} ≤
        Real.exp (-2 * (k : ℝ) * t ^ 2 / (1 - 0) ^ 2) := hbound0
    have hev_eq : {ω : Fin k → Bool | ∑ i, coordVar i ω ≤ T} =
        {ω | T' ≤ ∑ i, (1 - coordVar i ω)} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [hsum_id, hT'def]
      constructor
      · intro h
        linarith
      · intro h
        linarith
    have hexp_eq : (-2 * (k : ℝ) * t ^ 2 / (1 - 0) ^ 2 : ℝ) =
        (-2 * ((k : ℝ) * c - T) ^ 2 / (k : ℝ) : ℝ) := by
      rw [htdef, hs'def, hT'def]
      field_simp
      ring
    calc (randomSubsetLaw p).real {ω | ∑ i, coordVar i ω ≤ T}
        = (randomSubsetLaw p).real
          {ω | T' ≤ ∑ i, (1 - coordVar i ω)} := by rw [hev_eq]
      _ ≤ (randomSubsetLaw p).real
          {ω | t ≤ (1 / (k : ℝ)) * ∑ i, (1 - coordVar i ω) -
            (1 / (k : ℝ)) * ∑ i, ∫ ω, (1 - coordVar i ω)
              ∂(randomSubsetLaw p)} := hmono
      _ ≤ Real.exp (-2 * (k : ℝ) * t ^ 2 / (1 - 0) ^ 2) := hbound
      _ = Real.exp (-2 * ((k : ℝ) * c - T) ^ 2 / (k : ℝ)) := by rw [hexp_eq]
      _ = Real.exp (-2 * (k * c - T) ^ 2 / k) := by norm_cast

end MathlibExt.Probability.BernoulliProductTail
