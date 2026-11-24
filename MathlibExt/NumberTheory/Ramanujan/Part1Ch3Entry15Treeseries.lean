/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Section8Example4Integrable
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry15Treeseries

/-- Tree-function coefficient: `(n+1)^(n-1)/n!`, matching the wanted summand factor. -/
private noncomputable def treeCoeff (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ (n - 1) / (Nat.factorial n : ℝ)

/-- Tree series `S(w) = ∑ (n+1)^(n-1)/n! * w^n`. -/
private noncomputable def treeSeries (w : ℝ) : ℝ :=
  ∑' n : ℕ, treeCoeff n * w ^ n

/-- Derivative series `D(w) = ∑ (n+1) * c(n+1) * w^n`. -/
private noncomputable def treeSeriesD (w : ℝ) : ℝ :=
  ∑' n : ℕ, (((n : ℝ) + 1) * treeCoeff (n + 1) * w ^ n)

/-- Auxiliary series `E(w) = ∑ (n+1) * c(n) * w^n`. -/
private noncomputable def treeSeriesE (w : ℝ) : ℝ :=
  ∑' n : ℕ, (((n : ℝ) + 1) * treeCoeff n * w ^ n)

/-- Radius of convergence `ρ₀ = exp (-1)`. -/
private noncomputable def rho0 : ℝ := Real.exp (-1)

/-- `(m+1) * (m+1)^(m-1) = (m+1)^m`, handling the `m = 0` truncation. -/
private lemma pow_succ_mul_eq (m : ℕ) :
    (((m : ℝ) + 1) * (((m : ℝ) + 1) ^ (m - 1))) = ((m : ℝ) + 1) ^ m := by
  cases m with
  | zero => norm_num
  | succ j =>
    have h : j + 1 - 1 = j := Nat.add_sub_cancel j 1
    rw [h]
    have hcast : (((j + 1 : ℕ)) : ℝ) + 1 = ((j : ℝ) + 1) + 1 := by push_cast; ring
    rw [hcast, pow_succ']

/-- N1: vanishing alternating binomial moments. -/
private lemma alternating_choose_mul_succ_pow_eq_zero (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * (((k : ℝ) + 1) ^ (n - 1)) = 0 := by
  have h0 := fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) (j := n - 1) (n := n) (by omega)
  have h1 := congrFun h0 (1 : ℝ)
  simp only [fwdDiff_iter_eq_sum_shift, Pi.zero_apply] at h1
  refine (Finset.sum_congr rfl (fun k _ => ?_)).trans h1
  rw [zsmul_eq_mul]
  have hk1 : (k • (1 : ℝ)) = (k : ℝ) := by rw [nsmul_eq_mul, mul_one]
  rw [hk1]
  have h21 : (1 : ℝ) + (k : ℝ) = (k : ℝ) + 1 := by ring
  rw [h21]
  push_cast
  ring

/-- Per-term derivative for the Abel sum. -/
private lemma abelTerm_hasDerivAt (n k : ℕ) (y : ℝ) :
    HasDerivAt
      (fun t : ℝ => (n.choose k : ℝ) * (((k : ℝ) + 1) ^ (k - 1))
        * ((t - (k : ℝ)) ^ (n - k)))
      ((n.choose k : ℝ) * (((k : ℝ) + 1) ^ (k - 1))
        * ((((n - k : ℕ)) : ℝ)
          * ((y - (k : ℝ)) ^ (n - k - 1)))) y := by
  have hbase : HasDerivAt (fun t : ℝ => t - (k : ℝ)) 1 y := (hasDerivAt_id' y).sub_const (k : ℝ)
  have hpow : HasDerivAt (fun t : ℝ => (t - (k : ℝ)) ^ (n - k))
      ((((n - k : ℕ)) : ℝ) * ((y - (k : ℝ)) ^ (n - k - 1)) * 1) y := hbase.fun_pow (n - k)
  have hmul : HasDerivAt
      (fun t : ℝ => (n.choose k : ℝ) * (((k : ℝ) + 1) ^ (k - 1))
        * ((t - (k : ℝ)) ^ (n - k)))
      (((n.choose k : ℝ) * (((k : ℝ) + 1) ^ (k - 1)))
        * ((((n - k : ℕ)) : ℝ)
          * ((y - (k : ℝ)) ^ (n - k - 1)) * 1)) y :=
    hpow.const_mul ((n.choose k : ℝ) * (((k : ℝ) + 1) ^ (k - 1)))
  have hval : (((n.choose k : ℝ) * (((k : ℝ) + 1) ^ (k - 1)))
        * ((((n - k : ℕ)) : ℝ) * ((y - (k : ℝ)) ^ (n - k - 1)) * 1))
      = (n.choose k : ℝ) * (((k : ℝ) + 1) ^ (k - 1))
        * ((((n - k : ℕ)) : ℝ) * ((y - (k : ℝ)) ^ (n - k - 1))) := by
    ring
  rw [hval] at hmul
  exact hmul

/-- Termwise derivative of the Abel sum. -/
private lemma abel_sum_hasDerivAt (n : ℕ) (y : ℝ) :
    HasDerivAt (fun t : ℝ => ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * (((k : ℝ) + 1) ^ (k - 1)) * ((t - (k : ℝ)) ^ (n - k)))
      (∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * (((k : ℝ) + 1) ^ (k - 1))
          * ((((n - k : ℕ)) : ℝ)
            * ((y - (k : ℝ)) ^ (n - k - 1)))) y :=
  HasDerivAt.fun_sum (fun k _ => abelTerm_hasDerivAt n k y)

/-- N2a: the derivative of the size-`(n+1)` Abel sum equals `(n+1)` times the
size-`n` sum. -/
private lemma abel_deriv_value_eq (n : ℕ) (y : ℝ)
    (ih : ∀ t : ℝ, ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * (((k : ℝ) + 1) ^ (k - 1)) * ((t - (k : ℝ)) ^ (n - k)) = (t + 1) ^ n) :
    (∑ k ∈ Finset.range (n + 1 + 1),
      (((n + 1).choose k : ℕ) : ℝ) * ((((k : ℝ) + 1) ^ (k - 1))) *
        (((((n + 1 - k : ℕ))) : ℝ) * (((y - (k : ℝ)) ^ (n + 1 - k - 1)))))
      = ((((n + 1 : ℕ))) : ℝ) * ((y + 1) ^ ((n + 1) - 1)) := by
  rw [Finset.sum_range_succ]
  have h00 : n + 1 - (n + 1) = 0 := by omega
  simp only [h00, Nat.cast_zero, zero_mul, mul_zero, add_zero]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      ((((n + 1).choose k : ℕ)) : ℝ) * ((((k : ℝ) + 1) ^ (k - 1))) *
          (((((n + 1 - k : ℕ))) : ℝ)
            * (((y - (k : ℝ)) ^ (n + 1 - k - 1))))
        = ((((n + 1 : ℕ))) : ℝ)
          * (((n.choose k : ℝ) * ((((k : ℝ) + 1) ^ (k - 1)))
            * (((y - (k : ℝ)) ^ (n - k))))) := by
    intro k hk
    have hkn : k < n + 1 := Finset.mem_range.mp hk
    have hexp : n + 1 - k - 1 = n - k := by omega
    have hchoose : ((((n + 1).choose k : ℕ)) : ℝ) * (((((n + 1 - k : ℕ))) : ℝ))
        = ((((n + 1 : ℕ))) : ℝ) * ((n.choose k : ℝ)) := by
      have h := Nat.choose_mul_succ_eq n k
      have h2 := congrArg (Nat.cast : ℕ → ℝ) h
      simp only [Nat.cast_mul] at h2
      linear_combination -h2
    rw [hexp]
    linear_combination ((((k : ℝ) + 1) ^ (k - 1)) * ((y - (k : ℝ)) ^ (n - k))) * hchoose
  calc (∑ k ∈ Finset.range (n + 1),
          ((((n + 1).choose k : ℕ)) : ℝ) * ((((k : ℝ) + 1) ^ (k - 1))) *
            (((((n + 1 - k : ℕ))) : ℝ) * (((y - (k : ℝ)) ^ (n + 1 - k - 1)))))
      = ∑ k ∈ Finset.range (n + 1),
          ((((n + 1 : ℕ))) : ℝ)
            * (((n.choose k : ℝ) * ((((k : ℝ) + 1) ^ (k - 1)))
              * (((y - (k : ℝ)) ^ (n - k))))) :=
        Finset.sum_congr rfl hterm
    _ = ((((n + 1 : ℕ))) : ℝ) * ∑ k ∈ Finset.range (n + 1),
          ((n.choose k : ℝ) * ((((k : ℝ) + 1) ^ (k - 1))) * (((y - (k : ℝ)) ^ (n - k)))) := by
        rw [Finset.mul_sum]
    _ = ((((n + 1 : ℕ))) : ℝ) * (y + 1) ^ n := by rw [ih y]
    _ = ((((n + 1 : ℕ))) : ℝ) * ((y + 1) ^ ((n + 1) - 1)) := by rw [Nat.add_sub_cancel]

/-- N2: Abel's binomial identity at `x = 1`. -/
private lemma abel_identity_one : ∀ (n : ℕ) (y : ℝ),
    ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * (((k : ℝ) + 1) ^ (k - 1)) * ((y - (k : ℝ)) ^ (n - k)) = (y + 1) ^ n := by
  intro n
  induction n with
  | zero =>
    intro y
    simp
  | succ n ih =>
    intro y
    have hR_gen : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (s + 1) ^ (n + 1))
        (((((n + 1 : ℕ))) : ℝ) * ((t + 1) ^ ((n + 1) - 1))) t := by
      intro t
      have hb : HasDerivAt (fun s : ℝ => s + 1) 1 t := (hasDerivAt_id' t).add_const 1
      have hp : HasDerivAt (fun s : ℝ => (s + 1) ^ (n + 1))
          (((((n + 1 : ℕ))) : ℝ) * ((t + 1) ^ ((n + 1) - 1)) * 1) t := hb.fun_pow (n + 1)
      have hval : (((((n + 1 : ℕ))) : ℝ) * ((t + 1) ^ ((n + 1) - 1)) * 1)
          = (((((n + 1 : ℕ))) : ℝ) * ((t + 1) ^ ((n + 1) - 1))) := by ring
      rw [hval] at hp
      exact hp
    have hD : ∀ t : ℝ, HasDerivAt
        (fun s : ℝ => (∑ k ∈ Finset.range (n + 1 + 1),
          ((((n + 1).choose k : ℕ)) : ℝ)
            * ((((k : ℝ) + 1) ^ (k - 1)))
            * (((s - (k : ℝ)) ^ (n + 1 - k))) - (s + 1) ^ (n + 1)))
        ((∑ k ∈ Finset.range (n + 1 + 1),
          ((((n + 1).choose k : ℕ)) : ℝ) * ((((k : ℝ) + 1) ^ (k - 1))) *
            (((((n + 1 - k : ℕ))) : ℝ) * (((t - (k : ℝ)) ^ (n + 1 - k - 1))))) -
          (((((n + 1 : ℕ))) : ℝ) * ((t + 1) ^ ((n + 1) - 1)))) t :=
      fun t => (abel_sum_hasDerivAt (n + 1) t).sub (hR_gen t)
    have hderiv0 : ∀ t : ℝ, deriv
        (fun s : ℝ => (∑ k ∈ Finset.range (n + 1 + 1),
          ((((n + 1).choose k : ℕ)) : ℝ)
            * ((((k : ℝ) + 1) ^ (k - 1)))
            * (((s - (k : ℝ)) ^ (n + 1 - k)))
            - (s + 1) ^ (n + 1))) t = 0 := by
      intro t
      rw [(hD t).deriv, abel_deriv_value_eq n t ih, sub_self]
    have hdiff : Differentiable ℝ (fun s : ℝ =>
        (∑ k ∈ Finset.range (n + 1 + 1),
          ((((n + 1).choose k : ℕ)) : ℝ)
            * ((((k : ℝ) + 1) ^ (k - 1)))
            * (((s - (k : ℝ)) ^ (n + 1 - k))) - (s + 1) ^ (n + 1))) :=
      fun t => (hD t).differentiableAt
    have hconst := is_const_of_deriv_eq_zero hdiff hderiv0 y (-1)
    have hN1 := alternating_choose_mul_succ_pow_eq_zero (n + 1) (by omega)
    have hLm1 : (∑ k ∈ Finset.range (n + 1 + 1),
        ((((n + 1).choose k : ℕ)) : ℝ)
          * ((((k : ℝ) + 1) ^ (k - 1)))
          * ((((-1 : ℝ) - (k : ℝ)) ^ (n + 1 - k)))) = 0 := by
      have hsum : (∑ k ∈ Finset.range (n + 1 + 1),
            ((((n + 1).choose k : ℕ)) : ℝ)
              * ((((k : ℝ) + 1) ^ (k - 1)))
              * ((((-1 : ℝ) - (k : ℝ)) ^ (n + 1 - k))))
          = ∑ k ∈ Finset.range (n + 1 + 1),
            (-1 : ℝ) ^ ((n + 1) - k)
              * ((((n + 1).choose k : ℕ)) : ℝ)
              * (((k : ℝ) + 1) ^ ((n + 1) - 1)) :=
        Finset.sum_congr rfl (fun k hk => by
          have hkn : k < n + 1 + 1 := Finset.mem_range.mp hk
          have hneg : (-1 : ℝ) - (k : ℝ) = (-1) * ((k : ℝ) + 1) := by ring
          rw [hneg, mul_pow]
          have hexp1 : (n + 1) - 1 = n := Nat.add_sub_cancel n 1
          rw [hexp1]
          by_cases hk0 : k = 0
          · subst hk0
            simp [Nat.choose_zero_right]
          · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
            have hexp : (k - 1) + (n + 1 - k) = n := by omega
            have hpow : ((k : ℝ) + 1) ^ (k - 1)
                * (((k : ℝ) + 1) ^ (n + 1 - k))
                = ((k : ℝ) + 1) ^ n := by
              rw [← pow_add, hexp]
            linear_combination ((-1 : ℝ) ^ ((n + 1) - k) * ((((n + 1).choose k : ℕ)) : ℝ)) * hpow)
      rw [hsum]
      exact hN1
    have hRm1 : ((-1 : ℝ) + 1) ^ (n + 1) = 0 := by
      have h : (-1 : ℝ) + 1 = 0 := by ring
      rw [h]
      exact zero_pow (by omega)
    have hDm10 : (fun s : ℝ => (∑ k ∈ Finset.range (n + 1 + 1),
        ((((n + 1).choose k : ℕ)) : ℝ)
          * ((((k : ℝ) + 1) ^ (k - 1)))
          * (((s - (k : ℝ)) ^ (n + 1 - k)))
          - (s + 1) ^ (n + 1))) (-1) = 0 := by
      change (∑ k ∈ Finset.range (n + 1 + 1),
        ((((n + 1).choose k : ℕ)) : ℝ)
          * ((((k : ℝ) + 1) ^ (k - 1)))
          * ((((-1 : ℝ) - (k : ℝ)) ^ (n + 1 - k))))
          - ((-1 : ℝ) + 1) ^ (n + 1) = 0
      rw [hLm1, hRm1, sub_zero]
    have hDy0 : (fun s : ℝ => (∑ k ∈ Finset.range (n + 1 + 1),
        ((((n + 1).choose k : ℕ)) : ℝ)
          * ((((k : ℝ) + 1) ^ (k - 1)))
          * (((s - (k : ℝ)) ^ (n + 1 - k)))
          - (s + 1) ^ (n + 1))) y = 0 :=
      hconst.trans hDm10
    have hfin : (∑ k ∈ Finset.range (n + 1 + 1),
        ((((n + 1).choose k : ℕ)) : ℝ)
          * ((((k : ℝ) + 1) ^ (k - 1)))
          * (((y - (k : ℝ)) ^ (n + 1 - k))))
          - (y + 1) ^ (n + 1) = 0 := hDy0
    exact sub_eq_zero.mp hfin

/-- N3: coefficient identity `(n+1) * c(n+1) = ∑ c(k) * ((n-k)+1) * c(n-k)`. -/
private lemma treeCoeff_succ_mul_eq_sum (n : ℕ) :
    (((n : ℝ) + 1) * treeCoeff (n + 1))
      = ∑ k ∈ Finset.range (n + 1),
        treeCoeff k * (((((n - k : ℕ))) : ℝ) + 1) * treeCoeff (n - k) := by
  have hN2 := abel_identity_one n ((((n + 1 : ℕ))) : ℝ)
  have hbase : ∀ k ∈ Finset.range (n + 1),
      ((((n + 1 : ℕ))) : ℝ) - (k : ℝ)
        = ((((n - k : ℕ))) : ℝ) + 1 := by
    intro k hk
    have hkn : k < n + 1 := Finset.mem_range.mp hk
    have hsub : ((((n + 1 - k : ℕ))) : ℝ)
        = ((((n + 1 : ℕ))) : ℝ) - (k : ℝ) :=
      Nat.cast_sub (by omega)
    have hadd : n + 1 - k = (n - k) + 1 := by omega
    rw [← hsub, hadd]
    push_cast
    ring
  have hcongr : (∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * ((((k : ℝ) + 1) ^ (k - 1)))
          * ((((((n + 1 : ℕ))) : ℝ) - (k : ℝ)) ^ (n - k)))
      = (∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * ((((k : ℝ) + 1) ^ (k - 1)))
          * ((((((n - k : ℕ))) : ℝ) + 1) ^ (n - k))) :=
    Finset.sum_congr rfl (fun k hk => by rw [hbase k hk])
  have hN2r : (∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * ((((k : ℝ) + 1) ^ (k - 1)))
          * ((((((n - k : ℕ))) : ℝ) + 1) ^ (n - k)))
      = (((((n + 1 : ℕ))) : ℝ) + 1) ^ n :=
    hcongr.symm.trans hN2
  have hfact_ne : ((Nat.factorial n : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hdiv := congrArg
    (fun t : ℝ => t / ((Nat.factorial n : ℕ) : ℝ)) hN2r
  simp only [Finset.sum_div] at hdiv
  have hterm : ∀ k ∈ Finset.range (n + 1),
      ((n.choose k : ℝ) * ((((k : ℝ) + 1) ^ (k - 1)))
          * ((((((n - k : ℕ))) : ℝ) + 1) ^ (n - k))
        / ((Nat.factorial n : ℕ) : ℝ))
        = treeCoeff k * (((((n - k : ℕ))) : ℝ) + 1)
          * treeCoeff (n - k) := by
    intro k hk
    have hkn : k < n + 1 := Finset.mem_range.mp hk
    have hkle : k ≤ n := by omega
    have hchoose := Nat.cast_choose ℝ hkle
    have hB : (((((n - k : ℕ))) : ℝ) + 1) ^ (n - k)
        = (((((n - k : ℕ))) : ℝ) + 1)
          * (((((n - k : ℕ))) : ℝ) + 1) ^ ((n - k) - 1) :=
      (pow_succ_mul_eq (n - k)).symm
    rw [hchoose, hB]
    unfold treeCoeff
    have hkf : ((Nat.factorial k : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hnkf : ((Nat.factorial (n - k) : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))
    have hkk : ((Nat.factorial k : ℕ) : ℝ)
        * ((Nat.factorial (n - k) : ℕ) : ℝ) ≠ 0 :=
      mul_ne_zero hkf hnkf
    field_simp
  have hrhs : ((((((n + 1 : ℕ))) : ℝ) + 1) ^ n
      / ((Nat.factorial n : ℕ) : ℝ))
      = (((n : ℝ) + 1) * treeCoeff (n + 1)) := by
    have hfact : ((Nat.factorial (n + 1) : ℕ) : ℝ)
        = (((n : ℝ) + 1)) * ((Nat.factorial n : ℕ) : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hexp : (n + 1) - 1 = n := Nat.add_sub_cancel n 1
    have hbase2 : ((((n + 1 : ℕ))) : ℝ) + 1
        = ((n : ℝ) + 1) + 1 := by
      push_cast
      ring
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1ne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt h1
    have hprod : ((n : ℝ) + 1) * ((Nat.factorial n : ℕ) : ℝ)
        ≠ 0 := mul_ne_zero h1ne hfact_ne
    unfold treeCoeff
    rw [hfact, hexp, hbase2]
    field_simp
  have hsum := Finset.sum_congr rfl hterm
  rw [hsum] at hdiv
  rw [hrhs] at hdiv
  exact hdiv.symm

/-- N4a: tree coefficients are nonnegative. -/
private lemma treeCoeff_nonneg (n : ℕ) : 0 ≤ treeCoeff n := by
  unfold treeCoeff
  positivity

/-- N4b: `c(n) ≤ (n+1) * c(n)`. -/
private lemma treeCoeff_le_succ_mul (n : ℕ) :
    treeCoeff n ≤ (((n : ℝ) + 1) * treeCoeff n) := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  exact le_mul_of_one_le_left (treeCoeff_nonneg n) h1

/-- N4c: `(n+1) * c(n) ≤ (exp 1)^(n+1)`. -/
private lemma treeCoeff_succ_mul_le (n : ℕ) :
    (((n : ℝ) + 1) * treeCoeff n) ≤ (Real.exp 1) ^ (n + 1) := by
  have hpow := pow_succ_mul_eq n
  have hfact : ((Nat.factorial (n + 1) : ℕ) : ℝ)
      = (((n : ℝ) + 1)) * ((Nat.factorial n : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hnsucc : ((n : ℝ) + 1) ^ (n + 1)
      = ((n : ℝ) + 1) ^ n * ((n : ℝ) + 1) := pow_succ _ _
  have hbase_nn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hexp_eq : ((n : ℝ) + 1) * treeCoeff n
      = ((n : ℝ) + 1) ^ (n + 1)
        / ((Nat.factorial (n + 1) : ℕ) : ℝ) := by
    unfold treeCoeff
    rw [hfact, hnsucc]
    have h1 : ((n : ℝ) + 1)
          * ((((n : ℝ) + 1) ^ (n - 1))
            / ((Nat.factorial n : ℕ) : ℝ))
        = (((n : ℝ) + 1) ^ n) / ((Nat.factorial n : ℕ) : ℝ) := by
      rw [← mul_div_assoc, hpow]
    rw [h1]
    have hfact_ne : ((Nat.factorial n : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have h1ne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
    field_simp
  rw [hexp_eq]
  calc ((n : ℝ) + 1) ^ (n + 1)
        / ((Nat.factorial (n + 1) : ℕ) : ℝ)
      ≤ Real.exp ((n : ℝ) + 1) :=
        Real.pow_div_factorial_le_exp _ hbase_nn (n + 1)
    _ = (Real.exp 1) ^ (n + 1) := by
        have he : ((n : ℝ) + 1) = ((((n + 1 : ℕ))) : ℝ) * 1 := by
          push_cast
          ring
        rw [he, Real.exp_nat_mul]

/-- `ρ₀` is positive. -/
private lemma rho0_pos : 0 < rho0 := by
  unfold rho0
  exact Real.exp_pos _

/-- `exp 1 * ρ₀ = 1`. -/
private lemma exp1_mul_rho0 : Real.exp 1 * rho0 = 1 := by
  unfold rho0
  have h : (1 : ℝ) + (-1) = 0 := by ring
  rw [← Real.exp_add, h, Real.exp_zero]

/-- The geometric ratio is below 1. -/
private lemma geom_ratio_lt_one (ρ : ℝ) (hρ : ρ < rho0) :
    Real.exp 1 * ρ < 1 := by
  have he1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h := mul_lt_mul_of_pos_left hρ he1
  rw [exp1_mul_rho0] at h
  exact h

/-- N5a: `(n+1) * c(n) * ρ^n` is summable for `ρ < ρ₀`. -/
private lemma summable_treeCoeff_a (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < rho0) :
    Summable
      (fun n : ℕ => (((n : ℝ) + 1) * treeCoeff n * ρ ^ n)) := by
  have hratio_nn : (0 : ℝ) ≤ Real.exp 1 * ρ := by positivity
  have hratio_lt := geom_ratio_lt_one ρ hρ
  have hgeom := summable_geometric_of_lt_one hratio_nn hratio_lt
  have hmaj := hgeom.mul_left (Real.exp 1)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · have hc := treeCoeff_nonneg n
    have h1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hpn : (0 : ℝ) ≤ ρ ^ n := pow_nonneg hρ0 n
    exact mul_nonneg (mul_nonneg h1 hc) hpn
  · have hc := treeCoeff_succ_mul_le n
    have hpn : (0 : ℝ) ≤ ρ ^ n := pow_nonneg hρ0 n
    have hle := mul_le_mul_of_nonneg_right hc hpn
    have heq : (Real.exp 1) ^ (n + 1) * ρ ^ n
        = Real.exp 1 * (Real.exp 1 * ρ) ^ n := by
      rw [pow_succ', mul_pow]
      ring
    rw [heq] at hle
    exact hle

/-- N5b: `(n+1) * c(n+1) * ρ^n` is summable for `ρ < ρ₀`. -/
private lemma summable_treeCoeff_b (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < rho0) :
    Summable
      (fun n : ℕ => (((n : ℝ) + 1) * treeCoeff (n + 1) * ρ ^ n)) := by
  have hratio_nn : (0 : ℝ) ≤ Real.exp 1 * ρ := by positivity
  have hratio_lt := geom_ratio_lt_one ρ hρ
  have hgeom := summable_geometric_of_lt_one hratio_nn hratio_lt
  have hmaj := hgeom.mul_left ((Real.exp 1) ^ 2)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · have hc := treeCoeff_nonneg (n + 1)
    have h1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hpn : (0 : ℝ) ≤ ρ ^ n := pow_nonneg hρ0 n
    exact mul_nonneg (mul_nonneg h1 hc) hpn
  · have hc1 := treeCoeff_nonneg (n + 1)
    have hstep : ((n : ℝ) + 1) * treeCoeff (n + 1)
        ≤ (((((n + 1 : ℕ))) : ℝ) + 1) * treeCoeff (n + 1) := by
      have hle : (n : ℝ) + 1 ≤ ((((n + 1 : ℕ))) : ℝ) + 1 := by
        have hcast : ((((n + 1 : ℕ))) : ℝ) = (n : ℝ) + 1 := by
          push_cast
          ring
        rw [hcast]
        linarith
      exact mul_le_mul_of_nonneg_right hle hc1
    have hc2 := treeCoeff_succ_mul_le (n + 1)
    have hpn : (0 : ℝ) ≤ ρ ^ n := pow_nonneg hρ0 n
    have hle := mul_le_mul_of_nonneg_right (hstep.trans hc2) hpn
    have heq : (Real.exp 1) ^ ((n + 1) + 1) * ρ ^ n
        = (Real.exp 1) ^ 2 * (Real.exp 1 * ρ) ^ n := by
      have hadd : (n + 1) + 1 = 2 + n := by omega
      rw [hadd, pow_add, mul_pow]
      ring
    rw [heq] at hle
    exact hle

/-- N5 norm bound for the `E`-family. -/
private lemma summable_norm_tree_a (ρ r : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < rho0) (hr : |r| ≤ ρ) :
    Summable
      (fun n : ℕ => ‖(((n : ℝ) + 1) * treeCoeff n * r ^ n)‖) := by
  have hA := summable_treeCoeff_a ρ hρ0 hρ
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_) hA
  have hc := treeCoeff_nonneg n
  have h1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hnonneg : (0 : ℝ) ≤ ((n : ℝ) + 1) * treeCoeff n :=
    mul_nonneg h1 hc
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h1,
    abs_of_nonneg hc, abs_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg r) hr n) hnonneg

/-- N5 norm bound for the `D`-family. -/
private lemma summable_norm_tree_b (ρ r : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < rho0) (hr : |r| ≤ ρ) :
    Summable
      (fun n : ℕ => ‖(((n : ℝ) + 1) * treeCoeff (n + 1) * r ^ n)‖) := by
  have hB := summable_treeCoeff_b ρ hρ0 hρ
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_) hB
  have hc := treeCoeff_nonneg (n + 1)
  have h1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hnonneg : (0 : ℝ) ≤ ((n : ℝ) + 1) * treeCoeff (n + 1) :=
    mul_nonneg h1 hc
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h1,
    abs_of_nonneg hc, abs_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg r) hr n) hnonneg

/-- N5 norm bound for the `S`-family. -/
private lemma summable_norm_tree_c (ρ r : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < rho0) (hr : |r| ≤ ρ) :
    Summable (fun n : ℕ => ‖treeCoeff n * r ^ n‖) := by
  have hA := summable_treeCoeff_a ρ hρ0 hρ
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_) hA
  have hc := treeCoeff_nonneg n
  have hle1 := treeCoeff_le_succ_mul n
  have hrr : |r| ^ n ≤ ρ ^ n :=
    pow_le_pow_left₀ (abs_nonneg r) hr n
  have hpow_nn : (0 : ℝ) ≤ |r| ^ n := by positivity
  have hE_nn : (0 : ℝ) ≤ ((n : ℝ) + 1) * treeCoeff n := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    exact mul_nonneg h1 hc
  have hmul := mul_le_mul hle1 hrr hpow_nn hE_nn
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, abs_pow]
  calc treeCoeff n * |r| ^ n
      ≤ (((n : ℝ) + 1) * treeCoeff n) * ρ ^ n := hmul
    _ = ((n : ℝ) + 1) * treeCoeff n * ρ ^ n := by ring

/-- N5 norm bound for `n * c(n) * r^n`. -/
private lemma summable_norm_tree_F (ρ r : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < rho0) (hr : |r| ≤ ρ) :
    Summable (fun n : ℕ => ‖((n : ℝ) * treeCoeff n * r ^ n)‖) := by
  have hA := summable_treeCoeff_a ρ hρ0 hρ
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_) hA
  have hc := treeCoeff_nonneg n
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hle1 : (n : ℝ) * treeCoeff n
      ≤ ((n : ℝ) + 1) * treeCoeff n := by
    have hle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    exact mul_le_mul_of_nonneg_right hle hc
  have hrr : |r| ^ n ≤ ρ ^ n :=
    pow_le_pow_left₀ (abs_nonneg r) hr n
  have hpow_nn : (0 : ℝ) ≤ |r| ^ n := by positivity
  have hE_nn : (0 : ℝ) ≤ ((n : ℝ) + 1) * treeCoeff n := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    exact mul_nonneg h1 hc
  have hmul := mul_le_mul hle1 hrr hpow_nn hE_nn
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hn,
    abs_of_nonneg hc, abs_pow]
  calc (n : ℝ) * treeCoeff n * |r| ^ n
      ≤ (((n : ℝ) + 1) * treeCoeff n) * ρ ^ n := hmul
    _ = ((n : ℝ) + 1) * treeCoeff n * ρ ^ n := by ring

/-- N5 last family: `n * c(n) * ρ^(n-1)` is summable. -/
private lemma summable_tree_deriv_bound (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < rho0) :
    Summable
      (fun n : ℕ => ((n : ℝ) * treeCoeff n * ρ ^ (n - 1))) := by
  have hB := summable_treeCoeff_b ρ hρ0 hρ
  have heq : (fun m : ℕ => (((m : ℝ) + 1) * treeCoeff (m + 1) * ρ ^ m))
      = (fun m : ℕ => ((((m + 1 : ℕ))) : ℝ) * treeCoeff (m + 1)
        * ρ ^ ((m + 1) - 1)) := by
    funext m
    have hc : ((((m + 1 : ℕ))) : ℝ) = (m : ℝ) + 1 := by
      push_cast
      ring
    have he : (m + 1) - 1 = m := Nat.add_sub_cancel m 1
    rw [hc, he]
  rw [heq] at hB
  have hshift2 : (fun m : ℕ => ((((m + 1 : ℕ))) : ℝ)
        * treeCoeff (m + 1) * ρ ^ ((m + 1) - 1))
      = (fun m : ℕ => (fun n : ℕ => ((n : ℝ) * treeCoeff n
        * ρ ^ (n - 1))) (m + 1)) := rfl
  rw [hshift2] at hB
  exact (summable_nat_add_iff (G := ℝ) 1).mp hB

/-- N6: derivative of the tree series on `|y| < ρ₀`. -/
private lemma hasDerivAt_treeSeries (y : ℝ) (hy : |y| < rho0) :
    HasDerivAt treeSeries (treeSeriesD y) y := by
  set ρ : ℝ := (|y| + rho0) / 2 with hρdef
  have hyρ : |y| < ρ := by
    rw [hρdef]
    linarith [hy]
  have hρ0 : (0 : ℝ) ≤ ρ := by
    rw [hρdef]
    have h1 : (0 : ℝ) ≤ |y| := abs_nonneg y
    have h2 : (0 : ℝ) < rho0 := rho0_pos
    linarith
  have hρ : ρ < rho0 := by
    rw [hρdef]
    linarith [hy]
  have hρpos : (0 : ℝ) < ρ := lt_of_le_of_lt (abs_nonneg y) hyρ
  have hbound : ∀ n : ℕ, ∀ z : ℝ, z ∈ Set.Ioo (-ρ) ρ →
      ‖treeCoeff n * ((n : ℝ) * z ^ (n - 1))‖
        ≤ (n : ℝ) * treeCoeff n * ρ ^ (n - 1) := by
    intro n z hz
    have hzρ : |z| < ρ := abs_lt.mpr hz
    have hc := treeCoeff_nonneg n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hpow : |z| ^ (n - 1) ≤ ρ ^ (n - 1) :=
      pow_le_pow_left₀ (abs_nonneg z) (le_of_lt hzρ) (n - 1)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hc,
      abs_of_nonneg hn, abs_pow]
    calc treeCoeff n * ((n : ℝ) * |z| ^ (n - 1))
        ≤ treeCoeff n * ((n : ℝ) * ρ ^ (n - 1)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpow hn) hc
      _ = (n : ℝ) * treeCoeff n * ρ ^ (n - 1) := by ring
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ :=
    Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  have hr0 : |(0 : ℝ)| ≤ ρ := by
    rw [abs_zero]
    exact hρ0
  have h0sum : Summable (fun n : ℕ => treeCoeff n * (0 : ℝ) ^ n) :=
    (summable_norm_tree_c ρ 0 hρ0 hρ hr0).of_norm
  have hymem : y ∈ Set.Ioo (-ρ) ρ :=
    Set.mem_Ioo.mpr (abs_lt.mp hyρ)
  have hmain : HasDerivAt
      (fun z : ℝ => ∑' n : ℕ, treeCoeff n * z ^ n)
      (∑' n : ℕ, treeCoeff n * ((n : ℝ) * y ^ (n - 1))) y :=
    hasDerivAt_tsum_of_isPreconnected
      (u := fun n : ℕ => (n : ℝ) * treeCoeff n * ρ ^ (n - 1))
      (summable_tree_deriv_bound ρ hρ0 hρ)
      isOpen_Ioo isPreconnected_Ioo
      (fun n z _ => (hasDerivAt_pow n z).const_mul (treeCoeff n))
      hbound h0mem h0sum hymem
  have hF : Summable
      (fun n : ℕ => treeCoeff n * ((n : ℝ) * y ^ (n - 1))) := by
    have hB := summable_tree_deriv_bound ρ hρ0 hρ
    refine Summable.of_norm_bounded hB (fun n => ?_)
    have hc := treeCoeff_nonneg n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hyρ' : |y| ≤ ρ := le_of_lt hyρ
    have hpow : |y| ^ (n - 1) ≤ ρ ^ (n - 1) :=
      pow_le_pow_left₀ (abs_nonneg y) hyρ' (n - 1)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hc,
      abs_of_nonneg hn, abs_pow]
    calc treeCoeff n * ((n : ℝ) * |y| ^ (n - 1))
        ≤ treeCoeff n * ((n : ℝ) * ρ ^ (n - 1)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpow hn) hc
      _ = (n : ℝ) * treeCoeff n * ρ ^ (n - 1) := by ring
  have hdecomp := hF.tsum_eq_zero_add
  have hFm : ∀ m : ℕ, treeCoeff (m + 1)
        * (((((m + 1 : ℕ))) : ℝ) * y ^ ((m + 1) - 1))
      = ((m : ℝ) + 1) * treeCoeff (m + 1) * y ^ m := by
    intro m
    have hc : ((((m + 1 : ℕ))) : ℝ) = (m : ℝ) + 1 := by
      push_cast
      ring
    have he : (m + 1) - 1 = m := Nat.add_sub_cancel m 1
    rw [hc, he]
    ring
  have hF0b : treeCoeff 0 * (((((0 : ℕ))) : ℝ) * y ^ ((0 : ℕ) - 1))
      = 0 := by
    rw [Nat.cast_zero, zero_mul, mul_zero]
  rw [hF0b, zero_add] at hdecomp
  rw [tsum_congr hFm] at hdecomp
  rw [hdecomp] at hmain
  exact hmain

/-- N6b: `S(0) = 1`. -/
private lemma treeSeries_zero : treeSeries 0 = 1 := by
  have h : (∑' n : ℕ, treeCoeff n * (0 : ℝ) ^ n)
      = treeCoeff 0 * (0 : ℝ) ^ (0 : ℕ) :=
    tsum_eq_single 0 (fun b hb => by
      change treeCoeff b * (0 : ℝ) ^ b = 0
      rw [zero_pow hb, mul_zero])
  have hc0 : treeCoeff 0 * (0 : ℝ) ^ (0 : ℕ) = 1 := by
    unfold treeCoeff
    norm_num
  exact h.trans hc0

/-- N7: `S(w) * E(w) = D(w)` for `|w| < ρ₀`. -/
private lemma treeSeries_mul_E_eq_D (w : ℝ) (hw : |w| < rho0) :
    treeSeries w * treeSeriesE w = treeSeriesD w := by
  have hρ0 : (0 : ℝ) ≤ |w| := abs_nonneg w
  have hf : Summable (fun n : ℕ => ‖treeCoeff n * w ^ n‖) :=
    summable_norm_tree_c |w| w hρ0 hw le_rfl
  have hg : Summable
      (fun n : ℕ => ‖(((n : ℝ) + 1) * treeCoeff n * w ^ n)‖) :=
    summable_norm_tree_a |w| w hρ0 hw le_rfl
  have hprod :=
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg
  have hprod2 : (∑' n : ℕ, treeCoeff n * w ^ n)
        * (∑' n : ℕ, (((n : ℝ) + 1) * treeCoeff n * w ^ n))
      = ∑' n : ℕ, ∑ k ∈ Finset.range (n + 1),
        (treeCoeff k * w ^ k)
          * ((((((n - k : ℕ))) : ℝ) + 1) * treeCoeff (n - k)
            * w ^ (n - k)) := hprod
  have hinner : ∀ n : ℕ,
      (∑ k ∈ Finset.range (n + 1),
        (treeCoeff k * w ^ k)
          * ((((((n - k : ℕ))) : ℝ) + 1) * treeCoeff (n - k)
            * w ^ (n - k)))
        = ((n : ℝ) + 1) * treeCoeff (n + 1) * w ^ n := by
    intro n
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (treeCoeff k * w ^ k)
            * ((((((n - k : ℕ))) : ℝ) + 1) * treeCoeff (n - k)
              * w ^ (n - k))
          = (treeCoeff k * (((((n - k : ℕ))) : ℝ) + 1)
            * treeCoeff (n - k)) * w ^ n := by
      intro k hk
      have hkn : k < n + 1 := Finset.mem_range.mp hk
      have hkle : k ≤ n := by omega
      have hpow : w ^ k * w ^ (n - k) = w ^ n := by
        rw [← pow_add, Nat.add_sub_cancel' hkle]
      calc (treeCoeff k * w ^ k)
              * ((((((n - k : ℕ))) : ℝ) + 1) * treeCoeff (n - k)
                * w ^ (n - k))
          = (treeCoeff k * (((((n - k : ℕ))) : ℝ) + 1)
              * treeCoeff (n - k)) * (w ^ k * w ^ (n - k)) := by
            ring
        _ = (treeCoeff k * (((((n - k : ℕ))) : ℝ) + 1)
            * treeCoeff (n - k)) * w ^ n := by
            rw [hpow]
    calc (∑ k ∈ Finset.range (n + 1),
            (treeCoeff k * w ^ k)
              * ((((((n - k : ℕ))) : ℝ) + 1) * treeCoeff (n - k)
                * w ^ (n - k)))
        = ∑ k ∈ Finset.range (n + 1),
            (treeCoeff k * (((((n - k : ℕ))) : ℝ) + 1)
              * treeCoeff (n - k)) * w ^ n :=
          Finset.sum_congr rfl hterm
      _ = (∑ k ∈ Finset.range (n + 1),
            treeCoeff k * (((((n - k : ℕ))) : ℝ) + 1)
              * treeCoeff (n - k)) * w ^ n := by
          rw [Finset.sum_mul]
      _ = (((n : ℝ) + 1) * treeCoeff (n + 1)) * w ^ n := by
          rw [treeCoeff_succ_mul_eq_sum n]
      _ = ((n : ℝ) + 1) * treeCoeff (n + 1) * w ^ n := by ring
  have hRHS : (∑' n : ℕ, ∑ k ∈ Finset.range (n + 1),
        (treeCoeff k * w ^ k)
          * ((((((n - k : ℕ))) : ℝ) + 1) * treeCoeff (n - k)
            * w ^ (n - k)))
      = ∑' n : ℕ, ((n : ℝ) + 1) * treeCoeff (n + 1) * w ^ n :=
    tsum_congr hinner
  exact hprod2.trans hRHS

/-- N8: `S(w) + w * D(w) = E(w)` for `|w| < ρ₀`. -/
private lemma treeSeries_add_mul_D_eq_E (w : ℝ) (hw : |w| < rho0) :
    treeSeries w + w * treeSeriesD w = treeSeriesE w := by
  have hρ0 : (0 : ℝ) ≤ |w| := abs_nonneg w
  have hD : Summable
      (fun n : ℕ => ((n : ℝ) + 1) * treeCoeff (n + 1) * w ^ n) :=
    (summable_norm_tree_b |w| w hρ0 hw le_rfl).of_norm
  have hF : Summable (fun n : ℕ => (n : ℝ) * treeCoeff n * w ^ n) :=
    (summable_norm_tree_F |w| w hρ0 hw le_rfl).of_norm
  have hS : Summable (fun n : ℕ => treeCoeff n * w ^ n) :=
    (summable_norm_tree_c |w| w hρ0 hw le_rfl).of_norm
  have hwD : w * (∑' n : ℕ, ((n : ℝ) + 1) * treeCoeff (n + 1) * w ^ n)
      = ∑' n : ℕ, (n : ℝ) * treeCoeff n * w ^ n := by
    have h1 : w * (∑' n : ℕ, ((n : ℝ) + 1) * treeCoeff (n + 1) * w ^ n)
        = ∑' n : ℕ, w * (((n : ℝ) + 1) * treeCoeff (n + 1) * w ^ n) :=
      (hD.tsum_mul_left w).symm
    have h2 : (∑' n : ℕ, w * (((n : ℝ) + 1) * treeCoeff (n + 1) * w ^ n))
        = ∑' n : ℕ, ((((n : ℕ)) : ℝ) + 1) * treeCoeff (n + 1)
          * w ^ (n + 1) := by
      refine tsum_congr (fun n => ?_)
      rw [pow_succ']
      ring
    have hdecomp := hF.tsum_eq_zero_add
    have hF0 : ((((0 : ℕ))) : ℝ) * treeCoeff 0 * w ^ (0 : ℕ) = 0 := by
      rw [Nat.cast_zero, zero_mul, zero_mul]
    rw [hF0, zero_add] at hdecomp
    have hshift : (∑' n : ℕ, ((((n + 1 : ℕ))) : ℝ) * treeCoeff (n + 1)
          * w ^ (n + 1))
        = ∑' n : ℕ, ((((n : ℕ)) : ℝ) + 1) * treeCoeff (n + 1)
          * w ^ (n + 1) := by
      refine tsum_congr (fun n => ?_)
      have hc : ((((n + 1 : ℕ))) : ℝ) = (n : ℝ) + 1 := by
        push_cast
        ring
      rw [hc]
    have h3 : (∑' n : ℕ, ((((n : ℕ)) : ℝ) + 1) * treeCoeff (n + 1)
          * w ^ (n + 1))
        = ∑' n : ℕ, (n : ℝ) * treeCoeff n * w ^ n :=
      hshift.symm.trans hdecomp.symm
    exact h1.trans (h2.trans h3)
  have hfin : (∑' n : ℕ, treeCoeff n * w ^ n)
      + w * (∑' n : ℕ, ((n : ℝ) + 1) * treeCoeff (n + 1) * w ^ n)
      = ∑' n : ℕ, ((n : ℝ) + 1) * treeCoeff n * w ^ n := by
    rw [hwD]
    have hadd := hS.tsum_add hF
    rw [← hadd]
    refine tsum_congr (fun n => ?_)
    change treeCoeff n * w ^ n + (n : ℝ) * treeCoeff n * w ^ n
      = ((n : ℝ) + 1) * treeCoeff n * w ^ n
    ring
  exact hfin

/-- N9: `S(w) = exp (w * S(w))` for `|w| < ρ₀`. -/
private lemma treeSeries_eq_exp_mul (w : ℝ) (hw : |w| < rho0) :
    treeSeries w = Real.exp (w * treeSeries w) := by
  have hS : ∀ t : ℝ, t ∈ Set.Ioo (-rho0) rho0 →
      HasDerivAt treeSeries (treeSeriesD t) t := fun t ht =>
    hasDerivAt_treeSeries t (abs_lt.mpr ht)
  have hderiv : ∀ t : ℝ, ∀ ht : t ∈ Set.Ioo (-rho0) rho0,
      HasDerivAt
        (fun s : ℝ => treeSeries s * Real.exp (-(s * treeSeries s)))
        (treeSeriesD t * Real.exp (-(t * treeSeries t))
          + treeSeries t * (Real.exp (-(t * treeSeries t))
            * -(1 * treeSeries t + t * treeSeriesD t))) t := by
    intro t ht
    have hSt := hS t ht
    have hV : HasDerivAt (fun s : ℝ => s * treeSeries s)
        (1 * treeSeries t + t * treeSeriesD t) t :=
      (hasDerivAt_id' t).fun_mul hSt
    have hE : HasDerivAt (fun s : ℝ => Real.exp (-(s * treeSeries s)))
        (Real.exp (-(t * treeSeries t))
          * -(1 * treeSeries t + t * treeSeriesD t)) t :=
      hV.neg.exp
    exact hSt.fun_mul hE
  have hderiv0 : ∀ t : ℝ, ∀ ht : t ∈ Set.Ioo (-rho0) rho0,
      deriv (fun s : ℝ => treeSeries s
        * Real.exp (-(s * treeSeries s))) t = 0 := by
    intro t ht
    have h7 := treeSeries_mul_E_eq_D t (abs_lt.mpr ht)
    have h8 := treeSeries_add_mul_D_eq_E t (abs_lt.mpr ht)
    rw [(hderiv t ht).deriv]
    linear_combination (-Real.exp (-(t * treeSeries t))) * h7
      - (treeSeries t * Real.exp (-(t * treeSeries t))) * h8
  have hdiff : DifferentiableOn ℝ
      (fun s : ℝ => treeSeries s * Real.exp (-(s * treeSeries s)))
      (Set.Ioo (-rho0) rho0) :=
    fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt
  have hconst : ∀ a b : ℝ, a ∈ Set.Ioo (-rho0) rho0 →
      b ∈ Set.Ioo (-rho0) rho0 →
      (fun s : ℝ => treeSeries s * Real.exp (-(s * treeSeries s))) a
        = (fun s : ℝ => treeSeries s
          * Real.exp (-(s * treeSeries s))) b := by
    intro a b ha hb
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hdiff (fun x hx => hderiv0 x hx) ha hb
  have hwmem : w ∈ Set.Ioo (-rho0) rho0 :=
    Set.mem_Ioo.mpr (abs_lt.mp hw)
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-rho0) rho0 :=
    Set.mem_Ioo.mpr ⟨neg_lt_zero.mpr rho0_pos, rho0_pos⟩
  have h1 : treeSeries w * Real.exp (-(w * treeSeries w))
      = treeSeries 0 * Real.exp (-((0 : ℝ) * treeSeries 0)) :=
    hconst w 0 hwmem h0mem
  have h10 : treeSeries 0 * Real.exp (-((0 : ℝ) * treeSeries 0))
      = 1 := by
    rw [treeSeries_zero, zero_mul, neg_zero, Real.exp_zero, one_mul]
  rw [h10] at h1
  have he : Real.exp (-(w * treeSeries w))
      * Real.exp (w * treeSeries w) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc treeSeries w
      = treeSeries w * (Real.exp (-(w * treeSeries w))
        * Real.exp (w * treeSeries w)) := by
        rw [he, mul_one]
    _ = (treeSeries w * Real.exp (-(w * treeSeries w)))
        * Real.exp (w * treeSeries w) := by
        ring
    _ = Real.exp (w * treeSeries w) := by rw [h1, one_mul]

/-- N10: `t ↦ t * exp (-t)` is strictly monotone on `[0,1]`. -/
private lemma mul_exp_neg_strictMonoOn :
    StrictMonoOn (fun t : ℝ => t * Real.exp (-t))
      (Set.Icc 0 1) := by
  have hcont : ContinuousOn (fun t : ℝ => t * Real.exp (-t))
      (Set.Icc 0 1) := by
    have h1 : Continuous (fun t : ℝ => t * Real.exp (-t)) :=
      continuous_id.mul (Real.continuous_exp.comp continuous_id.neg)
    exact h1.continuousOn
  have hderiv : ∀ x ∈ interior (Set.Icc 0 1),
      0 < deriv (fun t : ℝ => t * Real.exp (-t)) x := by
    intro x hx
    rw [interior_Icc] at hx
    have hxI := Set.mem_Ioo.mp hx
    have hneg : HasDerivAt (fun t : ℝ => -t) (-1) x :=
      (hasDerivAt_id' x).neg
    have hE : HasDerivAt (fun t : ℝ => Real.exp (-t))
        (Real.exp (-x) * (-1)) x := hneg.exp
    have hmul : HasDerivAt (fun t : ℝ => t * Real.exp (-t))
        (1 * Real.exp (-x) + x * (Real.exp (-x) * (-1))) x :=
      (hasDerivAt_id' x).fun_mul hE
    rw [hmul.deriv]
    have hval : (1 : ℝ) * Real.exp (-x) + x * (Real.exp (-x) * (-1))
        = Real.exp (-x) * (1 - x) := by ring
    rw [hval]
    have he : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
    have hx1 : (0 : ℝ) < 1 - x := by linarith [hxI.2]
    exact mul_pos he hx1
  exact strictMonoOn_of_deriv_pos (convex_Icc 0 1) hcont hderiv

/-- N10 corollary: `t * exp (-t) < exp (-1)` for `0 ≤ t < 1`. -/
private lemma mul_exp_neg_lt (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    t * Real.exp (-t) < Real.exp (-1) := by
  have hmono := mul_exp_neg_strictMonoOn
  have htm : t ∈ Set.Icc (0 : ℝ) 1 :=
    Set.mem_Icc.mpr ⟨ht0, le_of_lt ht1⟩
  have h1m : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩
  have hlt := hmono htm h1m ht1
  have hlt2 : t * Real.exp (-t) < (1 : ℝ) * Real.exp (-1) := hlt
  rw [one_mul] at hlt2
  exact hlt2

/-- N11: `w * S(w) < 1` for `0 ≤ w < ρ₀`. -/
private lemma mul_treeSeries_lt_one (w : ℝ) (hw0 : 0 ≤ w)
    (hw : w < rho0) : w * treeSeries w < 1 := by
  have hV0 : (0 : ℝ) * treeSeries 0 = 0 := zero_mul _
  have hcont : ContinuousOn (fun t : ℝ => t * treeSeries t)
      (Set.Icc 0 w) := by
    intro t ht
    have htI : t ∈ Set.Ioo (-rho0) rho0 := by
      have htw := Set.mem_Icc.mp ht
      have hρ : (0 : ℝ) < rho0 := rho0_pos
      refine Set.mem_Ioo.mpr ⟨?_, ?_⟩ <;> linarith
    have hSt : ContinuousAt treeSeries t :=
      (hasDerivAt_treeSeries t (abs_lt.mpr htI)).continuousAt
    have hV : ContinuousAt (fun t : ℝ => t * treeSeries t) t :=
      continuousAt_id.mul hSt
    exact hV.continuousWithinAt
  by_contra hcon
  have hcon : 1 ≤ w * treeSeries w := le_of_not_gt hcon
  have hIV := intermediate_value_Icc hw0 hcont
  have h1mem : (1 : ℝ) ∈ Set.Icc ((0 : ℝ) * treeSeries 0)
      (w * treeSeries w) :=
    Set.mem_Icc.mpr ⟨by rw [hV0]; exact zero_le_one, hcon⟩
  have hex := hIV h1mem
  obtain ⟨t₀, ht₀mem, ht₀eq⟩ := hex
  have ht₀I : t₀ ∈ Set.Ioo (-rho0) rho0 := by
    have htw := Set.mem_Icc.mp ht₀mem
    have hρ : (0 : ℝ) < rho0 := rho0_pos
    refine Set.mem_Ioo.mpr ⟨?_, ?_⟩ <;> linarith
  have ht₀eq' : t₀ * treeSeries t₀ = 1 := ht₀eq
  have hS := treeSeries_eq_exp_mul t₀ (abs_lt.mpr ht₀I)
  rw [ht₀eq'] at hS
  have ht₀ρ : t₀ = rho0 := by
    have h1 : t₀ * Real.exp 1 = 1 := by
      rw [← hS]
      exact ht₀eq'
    have h2 : t₀ = (Real.exp 1)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (Real.exp 1)⁻¹ = rho0 := (Real.exp_neg 1).symm
    exact h2.trans h3
  have htw := Set.mem_Icc.mp ht₀mem
  rw [ht₀ρ] at htw
  linarith [htw.2, hw]

/-- N12: tree-function evaluation
`∑ c(n) * (u*exp(-u))^n = exp u` for `0 ≤ u < 1`. -/
private lemma hasSum_treeCoeff_mul_exp (u : ℝ) (hu0 : 0 ≤ u)
    (hu : u < 1) :
    HasSum (fun n : ℕ => treeCoeff n * (u * Real.exp (-u)) ^ n)
      (Real.exp u) := by
  have hw0 : (0 : ℝ) ≤ u * Real.exp (-u) := by positivity
  have hw : u * Real.exp (-u) < rho0 :=
    mul_exp_neg_lt u hu0 hu
  have habs : |u * Real.exp (-u)| < rho0 := by
    rw [abs_of_nonneg hw0]
    exact hw
  have hSpos : (0 : ℝ) < treeSeries (u * Real.exp (-u)) := by
    have h9 := treeSeries_eq_exp_mul (u * Real.exp (-u)) habs
    rw [h9]
    exact Real.exp_pos _
  have hVnn : (0 : ℝ)
      ≤ (u * Real.exp (-u)) * treeSeries (u * Real.exp (-u)) :=
    mul_nonneg hw0 (le_of_lt hSpos)
  have hVlt : (u * Real.exp (-u)) * treeSeries (u * Real.exp (-u))
      < 1 :=
    mul_treeSeries_lt_one _ hw0 hw
  have hVeq : ((u * Real.exp (-u)) * treeSeries (u * Real.exp (-u)))
        * Real.exp (-((u * Real.exp (-u))
          * treeSeries (u * Real.exp (-u))))
      = u * Real.exp (-u) := by
    have h9 := treeSeries_eq_exp_mul (u * Real.exp (-u)) habs
    have h1 : treeSeries (u * Real.exp (-u))
        * Real.exp (-((u * Real.exp (-u))
          * treeSeries (u * Real.exp (-u)))) = 1 := by
      nth_rewrite 1 [h9]
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc ((u * Real.exp (-u)) * treeSeries (u * Real.exp (-u)))
            * Real.exp (-((u * Real.exp (-u))
              * treeSeries (u * Real.exp (-u))))
        = (u * Real.exp (-u)) * (treeSeries (u * Real.exp (-u))
          * Real.exp (-((u * Real.exp (-u))
            * treeSeries (u * Real.exp (-u))))) := by
          ring
      _ = u * Real.exp (-u) := by rw [h1, mul_one]
  have hmono := mul_exp_neg_strictMonoOn
  have hinj := hmono.injOn
  have hVmem : (u * Real.exp (-u)) * treeSeries (u * Real.exp (-u))
      ∈ Set.Icc (0 : ℝ) 1 :=
    Set.mem_Icc.mpr ⟨hVnn, le_of_lt hVlt⟩
  have humem : u ∈ Set.Icc (0 : ℝ) 1 :=
    Set.mem_Icc.mpr ⟨hu0, le_of_lt hu⟩
  have hVu : (u * Real.exp (-u)) * treeSeries (u * Real.exp (-u))
      = u :=
    hinj hVmem humem hVeq
  have hSval : treeSeries (u * Real.exp (-u)) = Real.exp u := by
    have h9 := treeSeries_eq_exp_mul (u * Real.exp (-u)) habs
    rw [hVu] at h9
    exact h9
  have hSval' : (∑' n : ℕ, treeCoeff n * (u * Real.exp (-u)) ^ n)
      = Real.exp u := hSval
  have hnorm : Summable
      (fun n : ℕ => ‖treeCoeff n * (u * Real.exp (-u)) ^ n‖) :=
    summable_norm_tree_c |u * Real.exp (-u)| (u * Real.exp (-u))
      (abs_nonneg _) habs le_rfl
  have hhas := hnorm.of_norm.hasSum
  rw [hSval'] at hhas
  exact hhas

/-- Rewrite of each series term using `hu_eq`: `exp (-k * c) = (u * exp (-u)) ^ k`
where `c = 1 + x ^ 2 / 2 = u - log u`. -/
private lemma term_eq_treeTerm {x u : ℝ} (hu_pos : 0 < u)
    (hu_eq : u - Real.log u = 1 + x ^ 2 / 2) (k : ℕ) :
    ((k + 1 : ℝ) ^ (k - 1) / (Nat.factorial k : ℝ)) *
        Real.exp (-(k : ℝ) * (1 + x ^ 2 / 2))
      = ((k + 1 : ℝ) ^ (k - 1) / (Nat.factorial k : ℝ)) * (u * Real.exp (-u)) ^ k := by
  have h1 : (-(k : ℝ) * (1 + x ^ 2 / 2)) = (k : ℝ) * (Real.log u - u) := by
    have hc : (1 + x ^ 2 / 2) = u - Real.log u := hu_eq.symm
    rw [hc]
    ring
  rw [h1, Real.exp_nat_mul]
  congr 1
  have h2 : Real.log u - u = Real.log u + -u := by ring
  rw [h2, Real.exp_add, Real.exp_log hu_pos]

/-- Rewrite of the right-hand side using `hu_eq`: `u * exp c = exp u`. -/
private lemma rhs_eq_exp {x u : ℝ} (hu_pos : 0 < u)
    (hu_eq : u - Real.log u = 1 + x ^ 2 / 2) :
    u * Real.exp (1 + x ^ 2 / 2) = Real.exp u := by
  have hne : u ≠ 0 := ne_of_gt hu_pos
  have hc : (1 + x ^ 2 / 2) = u - Real.log u := hu_eq.symm
  rw [hc, Real.exp_sub, Real.exp_log hu_pos]
  field_simp

/-- **Ramanujan's tree-function series (Chapter 3, Entry 15).** Let $x$ and $u$ be real numbers
with $0 < u < 1$ and $u - \log u = 1 + x^2/2$. Then the series
$$\sum_{k=0}^{\infty} \frac{(k+1)^{k-1}}{k!}\, e^{-k(1 + x^2/2)}$$
converges to $u\, e^{1 + x^2/2}$.

Proves `Wanted` entry `ramanujan_part1_ch3_entry15_treeseries`.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 15, formulas (15.1)-(15.2),
    printed p. 73; scan PDF p. 83.
-/
theorem ramanujan_part1_ch3_entry15_treeseries (x : ℝ)
    (u : ℝ) (hu_pos : 0 < u) (hu_lt : u < 1)
    (hu_eq : u - Real.log u = 1 + x ^ 2 / 2) :
    HasSum (fun k : ℕ => ((k + 1 : ℝ) ^ (k - 1) / (Nat.factorial k : ℝ)) *
        Real.exp (-(k : ℝ) * (1 + x ^ 2 / 2)))
      (u * Real.exp (1 + x ^ 2 / 2)) := by
  have hfun : (fun k : ℕ => ((k + 1 : ℝ) ^ (k - 1) / (Nat.factorial k : ℝ)) *
        Real.exp (-(k : ℝ) * (1 + x ^ 2 / 2)))
      = (fun k : ℕ => treeCoeff k * (u * Real.exp (-u)) ^ k) :=
    funext (term_eq_treeTerm hu_pos hu_eq)
  have hC := rhs_eq_exp hu_pos hu_eq
  rw [hfun, hC]
  exact hasSum_treeCoeff_mul_exp u (le_of_lt hu_pos) hu_lt

end Entry15Treeseries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
