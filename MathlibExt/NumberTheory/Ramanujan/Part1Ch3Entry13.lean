/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
public import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Section8Example4Integrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.UniformSpace.UniformApproximation

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry13

/-- Abel factor: `1` at `k = 0`, `t * (t + k) ^ (k - 1)` otherwise. -/
private noncomputable def abelTerm (k : ℕ) (t : ℝ) : ℝ :=
  if k = 0 then 1 else t * (t + (k : ℝ)) ^ (k - 1)

private theorem abelTerm_zero (t : ℝ) : abelTerm 0 t = 1 := by
  simp [abelTerm]

private theorem abelTerm_succ (k : ℕ) (t : ℝ) :
    abelTerm (k + 1) t = t * (t + ((k + 1 : ℕ) : ℝ)) ^ k := by
  simp [abelTerm]

private theorem abelTerm_one (t : ℝ) : abelTerm 1 t = t := by
  have h := abelTerm_succ 0 t
  simpa using h

private theorem abelTerm_eq_zero_of_eq_zero (k : ℕ) (hk : k ≠ 0) :
    abelTerm k 0 = 0 := by
  simp [abelTerm, hk]

private theorem hasDerivAt_abelTerm_zero (t : ℝ) :
    HasDerivAt (fun t => abelTerm 0 t) 0 t := by
  simpa [abelTerm_zero] using hasDerivAt_const t (1 : ℝ)

private theorem hasDerivAt_abelTerm_one (t : ℝ) :
    HasDerivAt (fun t => abelTerm 1 t) 1 t := by
  have hfun : (fun t => abelTerm 1 t) = (fun t : ℝ => t) := by
    funext u
    exact abelTerm_one u
  rw [hfun]
  exact hasDerivAt_id t

private theorem hasDerivAt_abelTerm_succ_succ (j : ℕ) (t : ℝ) :
    HasDerivAt (fun t => abelTerm (j + 2) t)
      (((j + 2 : ℕ) : ℝ) * (t + 1) * (t + ((j + 2 : ℕ) : ℝ)) ^ j) t := by
  have hC : j + 2 ≠ 0 := by omega
  have hfun : (fun t => abelTerm (j + 2) t)
      = (fun t => t * (t + ((j + 2 : ℕ) : ℝ)) ^ (j + 1)) := by
    funext u
    simp only [abelTerm, hC, ↓reduceIte]
    rw [show j + 2 - 1 = j + 1 by omega]
  rw [hfun]
  have hf : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
  have hg0 : HasDerivAt (fun t : ℝ => t + ((j + 2 : ℕ) : ℝ)) 1 t := by
    have h := (hasDerivAt_id t).add_const (((j + 2 : ℕ) : ℝ))
    simpa using h
  have hg := hg0.pow (j + 1)
  have hmul := hf.mul hg
  have hexp : j + 1 - 1 = j := by omega
  simp only [hexp, Pi.pow_apply] at hmul
  convert hmul using 1
  have hpow : (t + ((j + 2 : ℕ) : ℝ)) ^ (j + 1)
      = (t + ((j + 2 : ℕ) : ℝ)) ^ j * (t + ((j + 2 : ℕ) : ℝ)) := by
    rw [pow_succ]
  rw [hpow]
  push_cast
  ring

private theorem choose_succ_mul (n j : ℕ) :
    ((n + 1 : ℕ) : ℝ) * ((n.choose j : ℕ) : ℝ)
      = (((n + 1).choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
  have h := Nat.add_one_mul_choose_eq n j
  exact_mod_cast h

/-- Abel convolution identity by induction on `N`, via differentiation in `t`. -/
private theorem abel_convolution (N : ℕ) (t s : ℝ) :
    (∑ k ∈ Finset.range (N + 1),
      (((N.choose k : ℕ) : ℝ) * abelTerm k t * abelTerm (N - k) s))
      = abelTerm N (t + s) := by
  induction N generalizing t s with
  | zero =>
      simp [abelTerm_zero]
  | succ n ih =>
      have hval : (∑ k ∈ Finset.range (n + 2),
            ((((n + 1).choose k : ℕ) : ℝ) * abelTerm k 0 * abelTerm (n + 1 - k) s))
            = abelTerm (n + 1) s := by
        rw [Finset.sum_eq_single 0]
        · simp [abelTerm_zero]
        · intro k _ hk0
          rw [abelTerm_eq_zero_of_eq_zero k hk0]
          ring
        · simp
      have hLHSderiv : ∀ u : ℝ, HasDerivAt
          (fun t => ∑ k ∈ Finset.range (n + 2),
            ((((n + 1).choose k : ℕ) : ℝ) * abelTerm k t * abelTerm (n + 1 - k) s))
          ((((n + 1 : ℕ)) : ℝ) * ∑ j ∈ Finset.range (n + 1),
            (((n.choose j : ℕ) : ℝ) * abelTerm j (u + 1) * abelTerm (n - j) s)) u := by
        intro u
        have hterm : ∀ k ∈ Finset.range (n + 2), HasDerivAt
            (fun t => ((((n + 1).choose k : ℕ) : ℝ) * abelTerm k t * abelTerm (n + 1 - k) s))
            ((((n + 1).choose k : ℕ) : ℝ)
              * (if k = 0 then 0 else if k = 1 then 1
                else (k : ℝ) * (u + 1) * (u + (k : ℝ)) ^ (k - 2))
              * abelTerm (n + 1 - k) s) u := by
          intro k hk
          by_cases hk0 : k = 0
          · subst hk0
            simp only [↓reduceIte]
            have hconst : (fun t => ((((n + 1).choose 0 : ℕ) : ℝ) * abelTerm 0 t
                * abelTerm (n + 1 - 0) s))
                = (fun _ => ((((n + 1).choose 0 : ℕ) : ℝ) * abelTerm (n + 1 - 0) s)) := by
              funext v
              rw [abelTerm_zero]
              ring
            rw [hconst]
            simpa using hasDerivAt_const u _
          · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
            by_cases hj0 : j = 0
            · subst hj0
              simp only [show (0 + 1 : ℕ) ≠ 0 by omega, ↓reduceIte,
                show (0 + 1 : ℕ) = 1 by rfl, ↓reduceIte]
              have h1 := hasDerivAt_abelTerm_one u
              have hfun : (fun t => ((((n + 1).choose 1 : ℕ) : ℝ) * abelTerm 1 t
                  * abelTerm (n + 1 - 1) s))
                  = (fun t => (((((n + 1).choose 1 : ℕ) : ℝ)
                    * abelTerm (n + 1 - 1) s)) * abelTerm 1 t) := by
                funext v
                ring
              rw [hfun]
              have h2 := h1.const_mul
                (((((n + 1).choose 1 : ℕ) : ℝ) * abelTerm (n + 1 - 1) s))
              convert h2 using 1
              ring
            · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
              have hk2 : i + 1 + 1 ≠ 0 := by omega
              have hk1 : i + 1 + 1 ≠ 1 := by omega
              simp only [hk2, ↓reduceIte, hk1, ↓reduceIte]
              have h2 := hasDerivAt_abelTerm_succ_succ i u
              have hfun : (fun t => ((((n + 1).choose (i + 1 + 1) : ℕ) : ℝ)
                  * abelTerm (i + 1 + 1) t * abelTerm (n + 1 - (i + 1 + 1)) s))
                  = (fun t => (((((n + 1).choose (i + 1 + 1) : ℕ) : ℝ)
                    * abelTerm (n + 1 - (i + 1 + 1)) s)) * abelTerm (i + 1 + 1) t) := by
                funext v
                ring
              rw [hfun]
              have hcast : ((i + 1 + 1 : ℕ) : ℝ) = ((i + 2 : ℕ) : ℝ) := by
                push_cast
                ring
              have hexp : i + 1 + 1 - 2 = i := by omega
              rw [hcast, hexp]
              have h3 := h2.const_mul
                (((((n + 1).choose (i + 1 + 1) : ℕ) : ℝ)
                  * abelTerm (n + 1 - (i + 1 + 1)) s))
              convert h3 using 1
              ring
        have hsum := HasDerivAt.sum hterm
        have hfun_eq : (∑ k ∈ Finset.range (n + 2), fun t =>
              ((((n + 1).choose k : ℕ) : ℝ) * abelTerm k t * abelTerm (n + 1 - k) s))
              = (fun t => ∑ k ∈ Finset.range (n + 2),
                ((((n + 1).choose k : ℕ) : ℝ) * abelTerm k t * abelTerm (n + 1 - k) s)) := by
          funext t
          simp
        rw [hfun_eq] at hsum
        convert hsum using 1
        rw [Finset.mul_sum]
        rw [Finset.sum_range_succ' (fun k => ((((n + 1).choose k : ℕ) : ℝ)
          * (if k = 0 then 0 else if k = 1 then 1
            else (k : ℝ) * (u + 1) * (u + (k : ℝ)) ^ (k - 2))
          * abelTerm (n + 1 - k) s)) (n + 1)]
        simp only [↓reduceIte, zero_mul, mul_zero, add_zero]
        apply Finset.sum_congr rfl
        intro j hj
        have hmem : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        by_cases hj0 : j = 0
        · subst hj0
          simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, abelTerm_zero]
          have hC : ((n + 1).choose 1 : ℕ) = n + 1 := Nat.choose_one_right (n + 1)
          rw [hC]
          have hn1 : n + 1 - 1 = n := by omega
          rw [hn1]
          simp [show (0 + 1 : ℕ) ≠ 0 by omega]
        · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          have hC := choose_succ_mul n (i + 1)
          have hA : abelTerm (i + 1) (u + 1)
              = (u + 1) * (u + 1 + ((i + 1 : ℕ) : ℝ)) ^ i := by
            rw [abelTerm_succ]
          have hexp : i + 1 + 1 - 2 = i := by omega
          have hsub : n + 1 - (i + 1 + 1) = n - (i + 1) := by omega
          rw [hsub, hexp]
          have hbase : u + 1 + ((i + 1 : ℕ) : ℝ) = u + ((i + 1 + 1 : ℕ) : ℝ) := by
            push_cast
            ring
          rw [hA, hbase]
          simp only [show (i + 1 + 1 : ℕ) ≠ 0 by omega, ↓reduceIte,
            show (i + 1 + 1 : ℕ) ≠ 1 by omega, ↓reduceIte]
          linear_combination hC * (((u + 1) * (u + ((i + 1 + 1 : ℕ) : ℝ)) ^ i)
            * abelTerm (n - (i + 1)) s)
      have hRHSderiv : ∀ u : ℝ, HasDerivAt (fun t => abelTerm (n + 1) (t + s))
          ((((n + 1 : ℕ)) : ℝ) * abelTerm n (u + 1 + s)) u := by
        intro u
        by_cases hn0 : n = 0
        · subst hn0
          simp only [abelTerm_zero, mul_one]
          have h1 : (fun t => abelTerm 1 (t + s)) = (fun t => t + s) := by
            funext v
            exact abelTerm_one (v + s)
          rw [h1]
          simpa using (hasDerivAt_id u).add_const s
        · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          have hinner : HasDerivAt (fun t : ℝ => t + s) 1 u := by
            have h := (hasDerivAt_id u).add_const s
            simpa using h
          have houter := hasDerivAt_abelTerm_succ_succ m (u + s)
          have hcomp := houter.comp u hinner
          have hfun : (fun t => abelTerm (m + 1 + 1) (t + s))
              = ((fun v => abelTerm (m + 2) v) ∘ (fun t : ℝ => t + s)) := rfl
          rw [hfun]
          have hA : abelTerm (m + 1) (u + 1 + s)
                = (u + 1 + s) * (u + 1 + s + ((m + 1 : ℕ) : ℝ)) ^ m := by
            rw [abelTerm_succ]
          have hderiv_eq : ((((m + 1 + 1 : ℕ)) : ℝ) * abelTerm (m + 1) (u + 1 + s))
              = ((((m + 2 : ℕ)) : ℝ) * (u + s + 1)
                * (u + s + (((m + 2 : ℕ)) : ℝ)) ^ m * 1) := by
            rw [hA]
            have hcast : ((m + 2 : ℕ) : ℝ) = ((m + 1 + 1 : ℕ) : ℝ) := by
              push_cast
              ring
            have hbase : u + s + ((m + 2 : ℕ) : ℝ) = u + 1 + s + ((m + 1 : ℕ) : ℝ) := by
              push_cast
              ring
            have hplus : u + s + 1 = u + 1 + s := by ring
            rw [hbase, hplus, hcast]
            ring
          rw [hderiv_eq]
          exact hcomp
      have hHeq : ∀ u : ℝ, (∑ k ∈ Finset.range (n + 2),
            ((((n + 1).choose k : ℕ) : ℝ) * abelTerm k u * abelTerm (n + 1 - k) s))
            = abelTerm (n + 1) (u + s) := by
        have hHderiv : ∀ u : ℝ, HasDerivAt
            ((fun t => ∑ k ∈ Finset.range (n + 2),
              ((((n + 1).choose k : ℕ) : ℝ) * abelTerm k t * abelTerm (n + 1 - k) s))
              - (fun t => abelTerm (n + 1) (t + s))) 0 u := by
          intro u
          have h1 := hLHSderiv u
          have h2 := hRHSderiv u
          have hIH : ((((n + 1 : ℕ)) : ℝ) * ∑ j ∈ Finset.range (n + 1),
              (((n.choose j : ℕ) : ℝ) * abelTerm j (u + 1) * abelTerm (n - j) s))
              = ((((n + 1 : ℕ)) : ℝ) * abelTerm n (u + 1 + s)) := by
            rw [ih (u + 1) s]
          rw [hIH] at h1
          have hsub := h1.sub h2
          simpa using hsub
        have hHdiff : Differentiable ℝ ((fun t =>
            ∑ k ∈ Finset.range (n + 2),
              ((((n + 1).choose k : ℕ) : ℝ) * abelTerm k t * abelTerm (n + 1 - k) s))
              - (fun t => abelTerm (n + 1) (t + s))) := by
          intro u
          exact (hHderiv u).differentiableAt
        have hH0 : deriv ((fun t =>
            ∑ k ∈ Finset.range (n + 2),
              ((((n + 1).choose k : ℕ) : ℝ) * abelTerm k t * abelTerm (n + 1 - k) s))
              - (fun t => abelTerm (n + 1) (t + s))) = 0 := by
          funext u
          exact (hHderiv u).deriv
        have hconst := is_const_of_deriv_eq_zero hHdiff (fun x => congrFun hH0 x)
        intro u
        have h0 : ((fun t => ∑ k ∈ Finset.range (n + 2),
              ((((n + 1).choose k : ℕ) : ℝ) * abelTerm k t * abelTerm (n + 1 - k) s))
              - (fun t => abelTerm (n + 1) (t + s))) 0 = 0 := by
          rw [Pi.sub_apply]
          simp only [zero_add]
          rw [hval, sub_self]
        have hcu := hconst u 0
        have hcu2 : (∑ k ∈ Finset.range (n + 2),
            ((((n + 1).choose k : ℕ) : ℝ) * abelTerm k u * abelTerm (n + 1 - k) s))
            - abelTerm (n + 1) (u + s) = 0 := by
          have hcu' : ((fun t => ∑ k ∈ Finset.range (n + 2),
              ((((n + 1).choose k : ℕ) : ℝ) * abelTerm k t * abelTerm (n + 1 - k) s))
              - (fun t => abelTerm (n + 1) (t + s))) u = 0 := by
            rw [hcu]
            exact h0
          rwa [Pi.sub_apply] at hcu'
        linarith
      exact hHeq t

private theorem exp_base_le (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (hk : 1 ≤ k) :
    (1 + R / (k : ℝ)) ^ k ≤ Real.exp R := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have h1 : (1 : ℝ) + R / (k : ℝ) ≤ Real.exp (R / (k : ℝ)) := by
    have h := Real.add_one_le_exp (R / (k : ℝ))
    linarith
  have h2 : ((1 : ℝ) + R / (k : ℝ)) ^ k ≤ (Real.exp (R / (k : ℝ))) ^ k :=
    pow_le_pow_left₀ (add_nonneg zero_le_one (div_nonneg hR (Nat.cast_nonneg k))) h1 k
  have h3 : (Real.exp (R / (k : ℝ))) ^ k = Real.exp R := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [mul_comm, div_mul_cancel₀ _ hkne]
  exact le_trans h2 (le_of_eq h3)

private theorem fact_stirling_bound (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ^ k / (Nat.factorial k : ℝ)
      ≤ Real.exp 1 ^ k / Real.sqrt (2 * Real.pi * (k : ℝ)) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hS := Stirling.le_factorial_stirling k
  have harg : (0 : ℝ) < 2 * Real.pi * (k : ℝ) :=
    mul_pos (by linarith [Real.pi_pos]) hkpos
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi * (k : ℝ)) := Real.sqrt_pos.mpr harg
  have hfact_pos : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hexp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hexpand : (k : ℝ) ^ k = ((k : ℝ) / Real.exp 1) ^ k * Real.exp 1 ^ k := by
    rw [← mul_pow, div_mul_cancel₀ _ (ne_of_gt hexp_pos)]
  have hstep : Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k
        * Real.exp 1 ^ k ≤ (Nat.factorial k : ℝ) * Real.exp 1 ^ k :=
    mul_le_mul_of_nonneg_right hS (pow_nonneg hexp_pos.le k)
  rw [div_le_iff₀ hfact_pos, div_mul_eq_mul_div, le_div_iff₀ hsqrt_pos, hexpand]
  calc ((k : ℝ) / Real.exp 1) ^ k * Real.exp 1 ^ k
          * Real.sqrt (2 * Real.pi * (k : ℝ))
        = Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k
          * Real.exp 1 ^ k := by ring
    _ ≤ (Nat.factorial k : ℝ) * Real.exp 1 ^ k := hstep
    _ = Real.exp 1 ^ k * (Nat.factorial k : ℝ) := by ring

private theorem rpow_three_halves (X : ℝ) (hX : 0 < X) :
    X * Real.sqrt X = X ^ ((3 / 2 : ℝ)) := by
  have e : ((3 / 2 : ℝ)) = 1 + 1 / 2 := by ring
  rw [e, Real.rpow_add hX, Real.rpow_one, Real.sqrt_eq_rpow]

private theorem abel_summable (t : ℝ) (a : ℝ) (ha : |a| ≥ Real.exp 1) :
    Summable (fun k : ℕ => ‖abelTerm k t * (1 / a) ^ k / (Nat.factorial k : ℝ)‖) := by
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, abs_zero] at ha
    linarith [hepos]
  have haz : |(1 : ℝ) / a| ≤ 1 / Real.exp 1 := by
    have h1 : (0 : ℝ) < |a| := lt_of_lt_of_le hepos ha
    rw [abs_div, abs_one, one_div, one_div]
    exact inv_le_inv₀ h1 hepos |>.mpr ha
  have haz0 : (0 : ℝ) ≤ |(1 : ℝ) / a| := abs_nonneg _
  have he0 : (0 : ℝ) ≤ 1 / Real.exp 1 := by positivity
  set R : ℝ := |t| with hRdef
  have hR : (0 : ℝ) ≤ R := abs_nonneg t
  have hpow_le : ∀ k : ℕ, |(1 / a) ^ k| ≤ (1 / Real.exp 1) ^ k := by
    intro k
    rw [abs_pow]
    exact pow_le_pow_left₀ haz0 haz k
  have hlib : Summable (fun m : ℕ => 1 / ((m : ℝ)) ^ ((3 / 2 : ℝ))) :=
    (Real.summable_one_div_nat_rpow (p := (3 / 2 : ℝ))).mpr (by norm_num)
  have hshift : Summable (fun j : ℕ => 1 / ((((j + 1 : ℕ)) : ℝ)) ^ ((3 / 2 : ℝ))) := by
    have h := (summable_nat_add_iff (f := fun m : ℕ => 1 / ((m : ℝ)) ^ ((3 / 2 : ℝ))) 1).mpr hlib
    simpa using h
  set C0 : ℝ := R * Real.exp R / Real.sqrt (2 * Real.pi) with hC0def
  have hC0 : (0 : ℝ) ≤ C0 := by
    unfold C0
    apply div_nonneg _ (Real.sqrt_nonneg _)
    exact mul_nonneg hR (Real.exp_pos _).le
  have hmajor : Summable (fun j : ℕ => C0 * (1 / ((((j + 1 : ℕ)) : ℝ)) ^ ((3 / 2 : ℝ)))) :=
    hshift.mul_left C0
  rw [← summable_nat_add_iff (f := fun k : ℕ =>
    ‖abelTerm k t * (1 / a) ^ k / (Nat.factorial k : ℝ)‖) 1]
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hmajor
  have hk1 : 1 ≤ j + 1 := Nat.le_add_left 1 j
  have hkpos : (0 : ℝ) < (((j + 1 : ℕ)) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hk0 : j + 1 ≠ 0 := by omega
  have hRk : (0 : ℝ) < R + (((j + 1 : ℕ)) : ℝ) := by linarith [hR, hkpos]
  have hfact_pos : (0 : ℝ) < ((Nat.factorial (j + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j + 1)
  have habel : abelTerm (j + 1) t = t * (t + (((j + 1 : ℕ)) : ℝ)) ^ j := by
    rw [abelTerm_succ]
  have htk : |t + (((j + 1 : ℕ)) : ℝ)| ≤ R + (((j + 1 : ℕ)) : ℝ) := by
    have h1 : ‖t + (((j + 1 : ℕ)) : ℝ)‖ ≤ ‖t‖ + ‖(((j + 1 : ℕ)) : ℝ)‖ :=
      norm_add_le t _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h1
    have hK : |(((j + 1 : ℕ)) : ℝ)| = (((j + 1 : ℕ)) : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    rw [hK, ← hRdef] at h1
    exact h1
  have hpowtk : |t + (((j + 1 : ℕ)) : ℝ)| ^ j ≤ (R + (((j + 1 : ℕ)) : ℝ)) ^ j := by
    exact pow_le_pow_left₀ (abs_nonneg _) htk j
  have hNk_eq : R + (((j + 1 : ℕ)) : ℝ)
      = (1 + R / (((j + 1 : ℕ)) : ℝ)) * (((j + 1 : ℕ)) : ℝ) := by
    have hkne : ((((j + 1 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt hkpos
    have e : (1 + R / (((j + 1 : ℕ)) : ℝ)) * (((j + 1 : ℕ)) : ℝ)
        = R + (((j + 1 : ℕ)) : ℝ) := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ hkne, add_comm]
    exact e.symm
  have hbase_le : (1 + R / (((j + 1 : ℕ)) : ℝ)) ^ (j + 1) ≤ Real.exp R :=
    exp_base_le R hR (j + 1) hk1
  have hstir := fact_stirling_bound (j + 1) hk1
  have hnorm : ‖abelTerm (j + 1) t * (1 / a) ^ (j + 1) / ((Nat.factorial (j + 1) : ℕ) : ℝ)‖
      = |t| * |t + (((j + 1 : ℕ)) : ℝ)| ^ j * |(1 / a) ^ (j + 1)|
        / ((Nat.factorial (j + 1) : ℕ) : ℝ) := by
    rw [habel]
    simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs, abs_one]
    have h1a : (1 : ℝ) / |a| = |(1 : ℝ) / a| := by
      rw [abs_div, abs_one]
    rw [h1a, ← abs_pow (a := (1 / a)) (n := j + 1),
      abs_of_nonneg (a := (((Nat.factorial (j + 1) : ℕ)) : ℝ))
        (Nat.cast_nonneg (Nat.factorial (j + 1)))]
  rw [hnorm]
  have htR : |t| = R := rfl
  rw [htR]
  have hle1 : R * |t + (((j + 1 : ℕ)) : ℝ)| ^ j * |(1 / a) ^ (j + 1)|
        / ((Nat.factorial (j + 1) : ℕ) : ℝ)
        ≤ R * (R + (((j + 1 : ℕ)) : ℝ)) ^ j * (1 / Real.exp 1) ^ (j + 1)
        / ((Nat.factorial (j + 1) : ℕ) : ℝ) := by
    apply div_le_div_of_nonneg_right _ hfact_pos.le
    have hXY : |t + (((j + 1 : ℕ)) : ℝ)| ^ j * |(1 / a) ^ (j + 1)|
        ≤ (R + (((j + 1 : ℕ)) : ℝ)) ^ j * (1 / Real.exp 1) ^ (j + 1) :=
      mul_le_mul hpowtk (hpow_le (j + 1)) (abs_nonneg _)
        (pow_nonneg (add_nonneg hR (Nat.cast_nonneg _)) _)
    calc R * |t + (((j + 1 : ℕ)) : ℝ)| ^ j * |(1 / a) ^ (j + 1)|
        = R * (|t + (((j + 1 : ℕ)) : ℝ)| ^ j * |(1 / a) ^ (j + 1)|) := by ring
      _ ≤ R * ((R + (((j + 1 : ℕ)) : ℝ)) ^ j * (1 / Real.exp 1) ^ (j + 1)) :=
          mul_le_mul_of_nonneg_left hXY hR
      _ = R * (R + (((j + 1 : ℕ)) : ℝ)) ^ j * (1 / Real.exp 1) ^ (j + 1) := by ring
  have hRpow : (R + (((j + 1 : ℕ)) : ℝ)) ^ j
      = (R + (((j + 1 : ℕ)) : ℝ)) ^ (j + 1) / (R + (((j + 1 : ℕ)) : ℝ)) := by
    rw [eq_div_iff hRk.ne']
    have h1 : (R + (((j + 1 : ℕ)) : ℝ)) ^ (j + 1)
        = (R + (((j + 1 : ℕ)) : ℝ)) ^ j * (R + (((j + 1 : ℕ)) : ℝ)) := by
      rw [pow_succ]
    rw [h1]
  have hNk_pow : (R + (((j + 1 : ℕ)) : ℝ)) ^ (j + 1)
      = (1 + R / (((j + 1 : ℕ)) : ℝ)) ^ (j + 1) * ((((j + 1 : ℕ)) : ℝ)) ^ (j + 1) := by
    rw [hNk_eq, mul_pow]
  have hstir2 : ((((j + 1 : ℕ)) : ℝ)) ^ (j + 1) / ((Nat.factorial (j + 1) : ℕ) : ℝ)
      * (1 / Real.exp 1) ^ (j + 1)
      ≤ 1 / Real.sqrt (2 * Real.pi * ((((j + 1 : ℕ)) : ℝ))) := by
    have hnonneg : (0 : ℝ) ≤ (1 / Real.exp 1) ^ (j + 1) := by positivity
    calc ((((j + 1 : ℕ)) : ℝ)) ^ (j + 1) / ((Nat.factorial (j + 1) : ℕ) : ℝ)
            * (1 / Real.exp 1) ^ (j + 1)
        ≤ Real.exp 1 ^ (j + 1) / Real.sqrt (2 * Real.pi * ((((j + 1 : ℕ)) : ℝ)))
          * (1 / Real.exp 1) ^ (j + 1) :=
          mul_le_mul_of_nonneg_right hstir hnonneg
      _ = 1 / Real.sqrt (2 * Real.pi * ((((j + 1 : ℕ)) : ℝ))) := by
          have hexp_ne : Real.exp 1 ^ (j + 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hepos)
          have hsqrt_ne : Real.sqrt (2 * Real.pi * ((((j + 1 : ℕ)) : ℝ))) ≠ 0 := by
            apply ne_of_gt
            apply Real.sqrt_pos.mpr
            exact mul_pos (by linarith [Real.pi_pos]) hkpos
          have h1 : (1 / Real.exp 1) ^ (j + 1) = 1 / Real.exp 1 ^ (j + 1) := by
            rw [div_pow, one_pow]
          rw [h1]
          field_simp
  have hsqrt_split : Real.sqrt (2 * Real.pi * ((((j + 1 : ℕ)) : ℝ)))
      = Real.sqrt (2 * Real.pi) * Real.sqrt ((((j + 1 : ℕ)) : ℝ)) := by
    rw [← Real.sqrt_mul (by positivity)]
  have hrpow := rpow_three_halves ((((j + 1 : ℕ)) : ℝ)) hkpos
  refine le_trans hle1 ?_
  rw [hC0def]
  calc R * (R + (((j + 1 : ℕ)) : ℝ)) ^ j * (1 / Real.exp 1) ^ (j + 1)
          / ((Nat.factorial (j + 1) : ℕ) : ℝ)
        = R * ((1 + R / (((j + 1 : ℕ)) : ℝ)) ^ (j + 1)
          * (((((j + 1 : ℕ)) : ℝ)) ^ (j + 1) / ((Nat.factorial (j + 1) : ℕ) : ℝ)
            * (1 / Real.exp 1) ^ (j + 1)))
          / (R + (((j + 1 : ℕ)) : ℝ)) := by
          rw [hRpow, hNk_pow]
          ring
      _ ≤ R * (Real.exp R
          * (1 / Real.sqrt (2 * Real.pi * ((((j + 1 : ℕ)) : ℝ)))))
          / (R + (((j + 1 : ℕ)) : ℝ)) := by
          apply div_le_div_of_nonneg_right _ hRk.le
          apply mul_le_mul_of_nonneg_left _ hR
          exact mul_le_mul hbase_le hstir2 (by positivity) (Real.exp_pos _).le
      _ = R * Real.exp R / Real.sqrt (2 * Real.pi * ((((j + 1 : ℕ)) : ℝ)))
          / (R + (((j + 1 : ℕ)) : ℝ)) := by
          ring
      _ ≤ R * Real.exp R / Real.sqrt (2 * Real.pi * ((((j + 1 : ℕ)) : ℝ)))
          / ((((j + 1 : ℕ)) : ℝ)) := by
          have ha0 : (0 : ℝ) ≤ R * Real.exp R
              / Real.sqrt (2 * Real.pi * ((((j + 1 : ℕ)) : ℝ))) := by
            apply div_nonneg _ (Real.sqrt_nonneg _)
            exact mul_nonneg hR (Real.exp_pos _).le
          have hle : ((((j + 1 : ℕ)) : ℝ)) ≤ R + (((j + 1 : ℕ)) : ℝ) := by
            linarith [hR]
          exact div_le_div_of_nonneg_left ha0 hkpos hle
      _ = R * Real.exp R / Real.sqrt (2 * Real.pi)
          * (1 / (((((j + 1 : ℕ)) : ℝ)) ^ ((3 / 2 : ℝ)))) := by
          rw [hsqrt_split, ← hrpow]
          have hsqrt2 : (0 : ℝ) < Real.sqrt (2 * Real.pi) := by
            apply Real.sqrt_pos.mpr
            linarith [Real.pi_pos]
          have hsqrtk : (0 : ℝ) < Real.sqrt ((((j + 1 : ℕ)) : ℝ)) :=
            Real.sqrt_pos.mpr hkpos
          have hkne : ((((j + 1 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt hkpos
          field_simp
      _ = (R * Real.exp R / Real.sqrt (2 * Real.pi))
          * (1 / (((((j + 1 : ℕ)) : ℝ)) ^ ((3 / 2 : ℝ)))) := by
          ring

private theorem abel_summable' (t : ℝ) (a : ℝ) (ha : |a| ≥ Real.exp 1) :
    Summable (fun k : ℕ => abelTerm k t * (1 / a) ^ k / (Nat.factorial k : ℝ)) :=
  Summable.of_norm (abel_summable t a ha)

private theorem abel_tsum_mul (t s : ℝ) (a : ℝ) (ha : |a| ≥ Real.exp 1) :
    (∑' k : ℕ, abelTerm k t * (1 / a) ^ k / (Nat.factorial k : ℝ))
      * (∑' k : ℕ, abelTerm k s * (1 / a) ^ k / (Nat.factorial k : ℝ))
      = ∑' k : ℕ, abelTerm k (t + s) * (1 / a) ^ k / (Nat.factorial k : ℝ) := by
  have hftN := abel_summable t a ha
  have hfsN := abel_summable s a ha
  have hprod := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hftN hfsN
  rw [hprod]
  apply tsum_congr
  intro n
  have hcoeff : ∀ k ∈ Finset.range (n + 1),
      (abelTerm k t * (1 / a) ^ k / (Nat.factorial k : ℝ))
        * (abelTerm (n - k) s * (1 / a) ^ (n - k) / ((Nat.factorial (n - k) : ℕ) : ℝ))
      = ((n.choose k : ℕ) : ℝ) * abelTerm k t * abelTerm (n - k) s
        * (1 / a) ^ n / (Nat.factorial n : ℝ) := by
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hpow : (1 / a) ^ k * (1 / a) ^ (n - k) = (1 / a) ^ n := by
      rw [← pow_add]
      congr 1
      omega
    have hfact : ((Nat.factorial n : ℕ) : ℝ)
        = ((n.choose k : ℕ) : ℝ) * (Nat.factorial k : ℝ) * ((Nat.factorial (n - k) : ℕ) : ℝ) := by
      have h := Nat.choose_mul_factorial_mul_factorial hkn
      have h2 : ((Nat.factorial n : ℕ) : ℝ)
          = (((n.choose k * Nat.factorial k * Nat.factorial (n - k) : ℕ)) : ℝ) := by
        exact_mod_cast h.symm
      rw [h2]
      push_cast
      ring
    have hkfact_ne : (Nat.factorial k : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    have hnkfact_ne : ((Nat.factorial (n - k) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n - k)
    have hnfact_ne : (Nat.factorial n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    have hCne : ((n.choose k : ℕ) : ℝ) ≠ 0 := by
      have hpos := Nat.choose_pos hkn
      exact_mod_cast ne_of_gt hpos
    calc (abelTerm k t * (1 / a) ^ k / (Nat.factorial k : ℝ))
            * (abelTerm (n - k) s * (1 / a) ^ (n - k) / ((Nat.factorial (n - k) : ℕ) : ℝ))
        = abelTerm k t * abelTerm (n - k) s * ((1 / a) ^ k * (1 / a) ^ (n - k))
          / ((Nat.factorial k : ℝ) * ((Nat.factorial (n - k) : ℕ) : ℝ)) := by
          field_simp
      _ = abelTerm k t * abelTerm (n - k) s * (1 / a) ^ n
          / ((Nat.factorial k : ℝ) * ((Nat.factorial (n - k) : ℕ) : ℝ)) := by
          rw [hpow]
      _ = ((n.choose k : ℕ) : ℝ) * abelTerm k t * abelTerm (n - k) s
          * (1 / a) ^ n / (Nat.factorial n : ℝ) := by
          rw [hfact]
          field_simp
  rw [Finset.sum_congr rfl (fun k hk => hcoeff k hk)]
  have hsum : (∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℕ) : ℝ) * abelTerm k t * abelTerm (n - k) s
          * (1 / a) ^ n / (Nat.factorial n : ℝ))
      = abelTerm n (t + s) * (1 / a) ^ n / (Nat.factorial n : ℝ) := by
    have hconv := abel_convolution n t s
    have hfactor : (∑ k ∈ Finset.range (n + 1),
          ((n.choose k : ℕ) : ℝ) * abelTerm k t * abelTerm (n - k) s
            * (1 / a) ^ n / (Nat.factorial n : ℝ))
        = (∑ k ∈ Finset.range (n + 1),
          ((n.choose k : ℕ) : ℝ) * abelTerm k t * abelTerm (n - k) s)
          * (1 / a) ^ n / (Nat.factorial n : ℝ) := by
      rw [Finset.sum_mul, Finset.sum_div]
    rw [hfactor, hconv]
  exact hsum

private theorem abel_tsum_zero (a : ℝ) (_ha : |a| ≥ Real.exp 1) :
    (∑' k : ℕ, abelTerm k 0 * (1 / a) ^ k / (Nat.factorial k : ℝ)) = 1 := by
  have hsum : HasSum (fun k : ℕ => abelTerm k 0 * (1 / a) ^ k / (Nat.factorial k : ℝ)) 1 := by
    have hfun : (fun k : ℕ => abelTerm k 0 * (1 / a) ^ k / (Nat.factorial k : ℝ))
        = (fun k : ℕ => if k = 0 then (1 : ℝ) else 0) := by
      funext k
      by_cases hk : k = 0
      · subst hk
        simp [abelTerm_zero]
      · simp only [hk, ↓reduceIte]
        rw [abelTerm_eq_zero_of_eq_zero k hk]
        ring
    rw [hfun]
    exact hasSum_ite_eq 0 1
  exact hsum.tsum_eq

private theorem abel_tsum_nat_pow (m : ℕ) (a : ℝ) (ha : |a| ≥ Real.exp 1) :
    (∑' k : ℕ, abelTerm k (m : ℝ) * (1 / a) ^ k / (Nat.factorial k : ℝ))
      = (∑' k : ℕ, abelTerm k 1 * (1 / a) ^ k / (Nat.factorial k : ℝ)) ^ m := by
  induction m with
  | zero =>
      simp only [Nat.cast_zero, pow_zero]
      exact abel_tsum_zero a ha
  | succ n ih =>
      have hstep := abel_tsum_mul (n : ℝ) 1 a ha
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast, ← hstep, ih]
      ring

private theorem real_exp_tsum (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) (Real.exp x) := by
  have hsum : Summable (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) :=
    Real.summable_pow_div_factorial x
  have htsum : (∑' n : ℕ, x ^ n / (Nat.factorial n : ℝ)) = Real.exp x := by
    have hexp : Real.exp x = NormedSpace.exp x := by
      rw [Real.exp_eq_exp_ℝ]
    rw [hexp]
    have htsum2 : NormedSpace.exp x = ∑' n : ℕ, x ^ n / (Nat.factorial n : ℝ) := by
      have h := NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)
      exact congrFun h x
    exact htsum2.symm
  rw [← htsum]
  exact hsum.hasSum

private theorem hasDerivAt_abelTerm_all (k : ℕ) (t : ℝ) :
    HasDerivAt (fun t => abelTerm k t)
      (if k = 0 then 0 else if k = 1 then 1
        else (k : ℝ) * (t + 1) * (t + (k : ℝ)) ^ (k - 2)) t := by
  by_cases hk0 : k = 0
  · subst hk0
    simpa using hasDerivAt_abelTerm_zero t
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    by_cases hj0 : j = 0
    · subst hj0
      simpa using hasDerivAt_abelTerm_one t
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hk2 : i + 1 + 1 ≠ 0 := by omega
      have hk1 : i + 1 + 1 ≠ 1 := by omega
      simp only [hk2, ↓reduceIte, hk1, ↓reduceIte]
      have h2 := hasDerivAt_abelTerm_succ_succ i t
      have hidx : i + 1 + 1 = i + 2 := by omega
      have hexp : i + 1 + 1 - 2 = i := by omega
      have hcast : ((i + 1 + 1 : ℕ) : ℝ) = ((i + 2 : ℕ) : ℝ) := by
        rw [hidx]
      rw [hexp]
      convert h2 using 1

private theorem abel_hasDerivAt_tsum (a : ℝ) (ha : |a| ≥ Real.exp 1) (y : ℝ) :
    HasDerivAt (fun t => ∑' k : ℕ, abelTerm k t * (1 / a) ^ k / (Nat.factorial k : ℝ))
      ((1 / a) * ∑' k : ℕ, abelTerm k (y + 1) * (1 / a) ^ k / (Nat.factorial k : ℝ)) y := by
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, abs_zero] at ha
    linarith [hepos]
  have haz : |(1 : ℝ) / a| ≤ 1 / Real.exp 1 := by
    have h1 : (0 : ℝ) < |a| := lt_of_lt_of_le hepos ha
    rw [abs_div, abs_one, one_div, one_div]
    exact inv_le_inv₀ h1 hepos |>.mpr ha
  set R : ℝ := |y| + 2 with hRdef
  have hRpos : (0 : ℝ) < R := by linarith [abs_nonneg y]
  have hyR : y ∈ Set.Ioo (-R) R := by
    rw [hRdef]
    constructor <;> linarith [neg_abs_le y, le_abs_self y]
  have h0R : (0 : ℝ) ∈ Set.Ioo (-R) R := by
    constructor <;> linarith [hRpos]
  set z : ℝ := 1 / a with hzdef
  have hz_ne : z ≠ 0 := by
    rw [hzdef]
    exact one_div_ne_zero ha0
  have habs_z : |z| = 1 / |a| := by rw [hzdef, abs_div, abs_one]
  set u : ℕ → ℝ := fun k => if k = 0 then 0 else if k = 1 then |z|
    else (R + 1) * (R + (k : ℝ)) ^ (k - 2) * |z| ^ k
      / ((Nat.factorial (k - 1) : ℕ) : ℝ) with hu_def
  have hu_summ : Summable u := by
    have ha' : |(|a|)| ≥ Real.exp 1 := by rwa [abs_abs]
    have hF : Summable (fun j : ℕ => abelTerm j (R + 1) * |z| ^ j
        / (Nat.factorial j : ℝ)) := by
      have hS := abel_summable' (R + 1) (|a|) ha'
      have hz_eq : |z| = 1 / |a| := habs_z
      have hfun : (fun j : ℕ => abelTerm j (R + 1) * |z| ^ j / (Nat.factorial j : ℝ))
          = (fun j : ℕ => abelTerm j (R + 1) * (1 / |a|) ^ j / (Nat.factorial j : ℝ)) := by
        rw [hz_eq]
      rw [hfun]
      exact hS
    have hFtail : Summable (fun i : ℕ => abelTerm (i + 1) (R + 1) * |z| ^ (i + 1)
        / ((Nat.factorial (i + 1) : ℕ) : ℝ)) :=
      (summable_nat_add_iff (f := fun j : ℕ => abelTerm j (R + 1) * |z| ^ j
        / (Nat.factorial j : ℝ)) 1).mpr hF
    have hshift : Summable (fun i : ℕ => u (i + 2)) := by
      have hu_eq : ∀ i : ℕ, u (i + 2)
          = |z| * (abelTerm (i + 1) (R + 1) * |z| ^ (i + 1)
            / ((Nat.factorial (i + 1) : ℕ) : ℝ)) := by
        intro i
        rw [hu_def]
        simp only [show i + 2 ≠ 0 by omega, ↓reduceIte,
          show i + 2 ≠ 1 by omega, ↓reduceIte]
        have hA : abelTerm (i + 1) (R + 1)
            = (R + 1) * (R + 1 + ((i + 1 : ℕ) : ℝ)) ^ i := by
          rw [abelTerm_succ]
        rw [hA]
        have hcast : R + 1 + ((i + 1 : ℕ) : ℝ) = R + ((i + 2 : ℕ) : ℝ) := by
          push_cast
          ring
        have hexp : i + 2 - 2 = i := by omega
        have hfact : ((Nat.factorial (i + 2 - 1) : ℕ) : ℝ)
            = ((Nat.factorial (i + 1) : ℕ) : ℝ) := rfl
        have hzpow : |z| ^ (i + 2) = |z| * |z| ^ (i + 1) := by
          rw [pow_succ']
        rw [hcast, hexp, hfact, hzpow]
        ring
      have hmul := hFtail.mul_left |z|
      simpa [hu_eq] using hmul
    exact (summable_nat_add_iff (f := u) 2).mp hshift
  have hg : ∀ k : ℕ, ∀ t : ℝ, t ∈ Set.Ioo (-R) R →
      HasDerivAt (fun t => abelTerm k t * z ^ k / (Nat.factorial k : ℝ))
        ((if k = 0 then 0 else if k = 1 then 1
          else (k : ℝ) * (t + 1) * (t + (k : ℝ)) ^ (k - 2))
          * z ^ k / (Nat.factorial k : ℝ)) t := by
    intro k t ht
    have hA := hasDerivAt_abelTerm_all k t
    have hfun : (fun t => abelTerm k t * z ^ k / (Nat.factorial k : ℝ))
        = (fun t => abelTerm k t * (z ^ k / (Nat.factorial k : ℝ))) := by
      funext v
      ring
    rw [hfun]
    have h2 := hA.mul_const (z ^ k / (Nat.factorial k : ℝ))
    convert h2 using 1
    ring
  have hg' : ∀ k : ℕ, ∀ t : ℝ, t ∈ Set.Ioo (-R) R →
      ‖(if k = 0 then 0 else if k = 1 then 1
        else (k : ℝ) * (t + 1) * (t + (k : ℝ)) ^ (k - 2))
        * z ^ k / (Nat.factorial k : ℝ)‖ ≤ u k := by
    intro k t ht
    have htR : |t| < R := abs_lt.mpr ht
    have ht1 : |t + 1| ≤ R + 1 := by
      calc |t + 1| ≤ |t| + 1 := by
            have h1 : ‖t + (1 : ℝ)‖ ≤ ‖t‖ + ‖(1 : ℝ)‖ := norm_add_le t 1
            rwa [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_one] at h1
        _ ≤ R + 1 := by linarith [htR]
    have htk : ∀ k : ℕ, |t + (k : ℝ)| ≤ R + (k : ℝ) := by
      intro k
      calc |t + (k : ℝ)| ≤ |t| + |(k : ℝ)| := by
            have h1 : ‖t + ((k : ℕ) : ℝ)‖ ≤ ‖t‖ + ‖(((k : ℕ)) : ℝ)‖ :=
              norm_add_le t _
            rwa [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h1
        _ = |t| + (k : ℝ) := by rw [abs_of_nonneg (a := ((k : ℕ) : ℝ)) (Nat.cast_nonneg k)]
        _ ≤ R + (k : ℝ) := by linarith [htR]
    by_cases hk0 : k = 0
    · subst hk0
      simp [hu_def]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      by_cases hj0 : j = 0
      · subst hj0
        simp only [show (0 + 1 : ℕ) ≠ 0 by omega, ↓reduceIte,
          show (0 + 1 : ℕ) = 1 by rfl, ↓reduceIte]
        simp only [hu_def, show (0 + 1 : ℕ) ≠ 0 by omega, ↓reduceIte, ↓reduceIte]
        have h1 : (1 : ℝ) * z ^ 1 / (Nat.factorial 1 : ℝ) = z := by simp
        rw [h1]
        simp [Real.norm_eq_abs]
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have hk2 : i + 1 + 1 ≠ 0 := by omega
        have hk1 : i + 1 + 1 ≠ 1 := by omega
        simp only [hu_def, hk2, ↓reduceIte, hk1, ↓reduceIte]
        have hfact_pos : (0 : ℝ) < (Nat.factorial (i + 1 + 1) : ℝ) := by
          exact_mod_cast Nat.factorial_pos _
        have hpow : |t + ((i + 1 + 1 : ℕ) : ℝ)| ^ (i + 1 + 1 - 2)
            ≤ (R + ((i + 1 + 1 : ℕ) : ℝ)) ^ (i + 1 + 1 - 2) :=
          pow_le_pow_left₀ (abs_nonneg _) (htk (i + 1 + 1)) _
        have hexp : i + 1 + 1 - 2 = i := by omega
        have hfact : (Nat.factorial (i + 1 + 1) : ℕ)
            = (i + 1 + 1) * Nat.factorial (i + 1) := by
          have h := Nat.factorial_succ (i + 1)
          simpa using h
        have hcast_ne : ((i + 1 + 1 : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast hk2
        have hfact_succ : (Nat.factorial (i + 1 + 1) : ℝ)
            = ((i + 1 + 1 : ℕ) : ℝ) * ((Nat.factorial (i + 1) : ℕ) : ℝ) := by
          have h := Nat.factorial_succ (i + 1)
          have hidx : i + 1 + 1 = (i + 1) + 1 := rfl
          rw [hidx] at h ⊢
          exact_mod_cast h
        have hfact1_pos : (0 : ℝ) < ((Nat.factorial (i + 1) : ℕ) : ℝ) := by
          exact_mod_cast Nat.factorial_pos _
        calc ‖(((i + 1 + 1 : ℕ) : ℝ) * (t + 1) * (t + ((i + 1 + 1 : ℕ) : ℝ)) ^ (i + 1 + 1 - 2))
              * z ^ (i + 1 + 1) / (Nat.factorial (i + 1 + 1) : ℝ)‖
            = ((i + 1 + 1 : ℕ) : ℝ) * |t + 1| * |t + ((i + 1 + 1 : ℕ) : ℝ)| ^ (i + 1 + 1 - 2)
              * |z| ^ (i + 1 + 1) / (Nat.factorial (i + 1 + 1) : ℝ) := by
              have habs : |(((i + 1 + 1 : ℕ)) : ℝ)| = (((i + 1 + 1 : ℕ)) : ℝ) :=
                abs_of_nonneg (Nat.cast_nonneg _)
              have habs2 : |(((Nat.factorial (i + 1 + 1) : ℕ)) : ℝ)|
                  = (((Nat.factorial (i + 1 + 1) : ℕ)) : ℝ) :=
                abs_of_nonneg (Nat.cast_nonneg _)
              simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs, habs, habs2]
          _ = |t + 1| * |t + ((i + 1 + 1 : ℕ) : ℝ)| ^ (i + 1 + 1 - 2)
              * |z| ^ (i + 1 + 1) / ((Nat.factorial (i + 1) : ℕ) : ℝ) := by
              rw [hfact_succ]
              have hkne : ((i + 1 + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hk2
              have hfne : ((Nat.factorial (i + 1) : ℕ) : ℝ) ≠ 0 := ne_of_gt hfact1_pos
              field_simp
          _ ≤ (R + 1) * (R + ((i + 1 + 1 : ℕ) : ℝ)) ^ (i + 1 + 1 - 2)
              * |z| ^ (i + 1 + 1) / ((Nat.factorial (i + 1) : ℕ) : ℝ) := by
              apply div_le_div_of_nonneg_right _ hfact1_pos.le
              have h1 : |t + 1| * |t + ((i + 1 + 1 : ℕ) : ℝ)| ^ (i + 1 + 1 - 2)
                  ≤ (R + 1) * (R + ((i + 1 + 1 : ℕ) : ℝ)) ^ (i + 1 + 1 - 2) :=
                mul_le_mul ht1 hpow (pow_nonneg (abs_nonneg _) _)
                  (by linarith [hRpos])
              calc |t + 1| * |t + ((i + 1 + 1 : ℕ) : ℝ)| ^ (i + 1 + 1 - 2) * |z| ^ (i + 1 + 1)
                  = (|t + 1| * |t + ((i + 1 + 1 : ℕ) : ℝ)| ^ (i + 1 + 1 - 2))
                    * |z| ^ (i + 1 + 1) := by
                    ring
                _ ≤ ((R + 1) * (R + ((i + 1 + 1 : ℕ) : ℝ)) ^ (i + 1 + 1 - 2)) * |z| ^ (i + 1 + 1) :=
                    mul_le_mul_of_nonneg_right h1 (pow_nonneg (abs_nonneg _) _)
                _ = (R + 1) * (R + ((i + 1 + 1 : ℕ) : ℝ)) ^ (i + 1 + 1 - 2)
                  * |z| ^ (i + 1 + 1) := by
                    ring
          _ = u (i + 1 + 1) := by
              rw [hu_def]
              simp only [hk2, ↓reduceIte, hk1, ↓reduceIte]
              rw [show (i + 1 + 1 - 1 : ℕ) = i + 1 by omega]
  have h't : IsPreconnected (Set.Ioo (-R) R) := isPreconnected_Ioo
  have hg0 : Summable (fun n : ℕ => abelTerm n 0 * z ^ n / (Nat.factorial n : ℝ)) :=
    abel_summable' 0 a ha
  have hmain : HasDerivAt (fun t => ∑' k : ℕ, abelTerm k t * z ^ k / (Nat.factorial k : ℝ))
      (∑' n : ℕ, ((if n = 0 then (0 : ℝ) else if n = 1 then 1
        else (n : ℝ) * (y + 1) * (y + (n : ℝ)) ^ (n - 2)) * z ^ n
        / (Nat.factorial n : ℝ))) y :=
    hasDerivAt_tsum_of_isPreconnected (u := u)
      (g := fun k t => abelTerm k t * z ^ k / (Nat.factorial k : ℝ))
      (g' := fun k v => ((if k = 0 then (0 : ℝ) else if k = 1 then 1
        else (k : ℝ) * (v + 1) * (v + (k : ℝ)) ^ (k - 2)) * z ^ k
        / (Nat.factorial k : ℝ)))
      hu_summ isOpen_Ioo h't hg hg' h0R hg0 hyR
  have hD : (∑' n : ℕ, ((if n = 0 then (0 : ℝ) else if n = 1 then 1
        else (n : ℝ) * (y + 1) * (y + (n : ℝ)) ^ (n - 2)) * z ^ n
        / (Nat.factorial n : ℝ)))
      = z * ∑' k : ℕ, abelTerm k (y + 1) * z ^ k / (Nat.factorial k : ℝ) := by
    have hderiv_summ : Summable (fun n : ℕ => ((if n = 0 then (0 : ℝ) else if n = 1 then 1
          else (n : ℝ) * (y + 1) * (y + (n : ℝ)) ^ (n - 2)) * z ^ n
          / (Nat.factorial n : ℝ))) :=
      Summable.of_norm_bounded hu_summ (fun n => hg' n y hyR)
    have hterm : ∀ m : ℕ, ((if m + 1 = 0 then (0 : ℝ) else if m + 1 = 1 then 1
          else ((m + 1 : ℕ) : ℝ) * (y + 1) * (y + ((m + 1 : ℕ) : ℝ)) ^ (m + 1 - 2))
          * z ^ (m + 1) / (Nat.factorial (m + 1) : ℝ))
        = z * (abelTerm m (y + 1) * z ^ m / (Nat.factorial m : ℝ)) := by
      intro m
      by_cases hm0 : m = 0
      · subst hm0
        simp only [show (0 + 1 : ℕ) ≠ 0 by omega, ↓reduceIte,
          show (0 + 1 : ℕ) = 1 by rfl, ↓reduceIte]
        simp [abelTerm_zero]
      · obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
        have hk2 : i + 1 + 1 ≠ 0 := by omega
        have hk1 : i + 1 + 1 ≠ 1 := by omega
        simp only [hk2, ↓reduceIte, hk1, ↓reduceIte]
        have hA : abelTerm (i + 1) (y + 1)
            = (y + 1) * (y + 1 + ((i + 1 : ℕ) : ℝ)) ^ i := by
          rw [abelTerm_succ]
        rw [hA]
        have hbase : y + 1 + ((i + 1 : ℕ) : ℝ) = y + ((i + 1 + 1 : ℕ) : ℝ) := by
          push_cast
          ring
        rw [hbase]
        have hexp : i + 1 + 1 - 2 = i := by omega
        rw [hexp]
        have hfact : (Nat.factorial (i + 1 + 1) : ℝ)
            = ((i + 1 + 1 : ℕ) : ℝ) * ((Nat.factorial (i + 1) : ℕ) : ℝ) := by
          have h := Nat.factorial_succ (i + 1)
          have hidx : i + 1 + 1 = (i + 1) + 1 := rfl
          rw [hidx] at h ⊢
          exact_mod_cast h
        rw [hfact]
        have hzpow : z ^ (i + 1 + 1) = z * z ^ (i + 1) := by
          have hidx : i + 1 + 1 = (i + 1) + 1 := rfl
          rw [hidx, pow_succ']
        rw [hzpow]
        have hkne : ((i + 1 + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hk2
        have hfne : ((Nat.factorial (i + 1) : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero _
        field_simp
    have h0 : ((if (0 : ℕ) = 0 then (0 : ℝ) else if (0 : ℕ) = 1 then 1
          else ((0 : ℕ) : ℝ) * (y + 1) * (y + ((0 : ℕ) : ℝ)) ^ (0 - 2)) * z ^ 0
          / (Nat.factorial 0 : ℝ)) = 0 := by simp
    calc (∑' n : ℕ, ((if n = 0 then (0 : ℝ) else if n = 1 then 1
            else (n : ℝ) * (y + 1) * (y + (n : ℝ)) ^ (n - 2)) * z ^ n
            / (Nat.factorial n : ℝ)))
        = ((if (0 : ℕ) = 0 then (0 : ℝ) else if (0 : ℕ) = 1 then 1
            else ((0 : ℕ) : ℝ) * (y + 1) * (y + ((0 : ℕ) : ℝ)) ^ (0 - 2)) * z ^ 0
            / (Nat.factorial 0 : ℝ))
          + ∑' m : ℕ, ((if m + 1 = 0 then (0 : ℝ) else if m + 1 = 1 then 1
            else ((m + 1 : ℕ) : ℝ) * (y + 1) * (y + ((m + 1 : ℕ) : ℝ)) ^ (m + 1 - 2))
            * z ^ (m + 1) / (Nat.factorial (m + 1) : ℝ)) :=
          hderiv_summ.tsum_eq_zero_add
      _ = 0 + ∑' m : ℕ, z * (abelTerm m (y + 1) * z ^ m
          / (Nat.factorial m : ℝ)) := by
          have hcongr : (∑' m : ℕ, ((if m + 1 = 0 then (0 : ℝ) else if m + 1 = 1 then 1
              else ((m + 1 : ℕ) : ℝ) * (y + 1) * (y + ((m + 1 : ℕ) : ℝ)) ^ (m + 1 - 2))
              * z ^ (m + 1) / (Nat.factorial (m + 1) : ℝ)))
              = ∑' m : ℕ, z * (abelTerm m (y + 1) * z ^ m / (Nat.factorial m : ℝ)) :=
            tsum_congr hterm
          rw [h0, hcongr]
      _ = z * ∑' k : ℕ, abelTerm k (y + 1) * z ^ k / (Nat.factorial k : ℝ) := by
          rw [zero_add, tsum_mul_left]
  rw [hD] at hmain
  exact hmain

/-- The `n = 0` case of the Entry 13 series: every tail term contains a factor `n = 0`,
so the series is `1` at `k = 0` and `0` elsewhere, summing to `x ^ (0 : ℝ) = 1`. -/
private theorem hasSum_entry13_at_zero (a x : ℝ) :
    HasSum (fun k : ℕ => if k = 0 then (1 : ℝ) else (0 : ℝ) * ((0 : ℝ) + (k : ℝ)) ^ (k - 1) /
        (a ^ k * (Nat.factorial k : ℝ))) (x ^ (0 : ℝ)) := by
  rw [Real.rpow_zero]
  have hfun : (fun k : ℕ => if k = 0 then (1 : ℝ) else (0 : ℝ) * ((0 : ℝ) + (k : ℝ)) ^ (k - 1) /
        (a ^ k * (Nat.factorial k : ℝ))) = (fun k : ℕ => if k = 0 then (1 : ℝ) else 0) := by
    funext k
    by_cases hk : k = 0 <;> simp [hk]
  rw [hfun]
  exact hasSum_ite_eq 0 1

/-- **Ramanujan's series for powers of a root of $x = a \log x$ (Entry 13).** Let $a$ be a real
number with $|a| \ge e$. Then there is a real number $x > 0$ with $x = a \log x$ such that for
every real number $n$ the series
$$1 + \sum_{k=1}^{\infty} \frac{n (n+k)^{k-1}}{a^k\, k!}$$
is summable with sum $x^n$.

Proves `Wanted` entry `ramanujan_part1_ch3_entry13`.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, definition (12.1), printed p. 66
    / PDF p. 76, and Entry 13, printed pp. 69--70 / PDF pp. 79--80; historical attribution on
    printed p. 72 / PDF p. 82.
-/
theorem ramanujan_part1_ch3_entry13 (a : ℝ) (ha : |a| ≥ Real.exp 1) :
    ∃ x : ℝ, 0 < x ∧ x = a * Real.log x ∧ ∀ n : ℝ,
      HasSum (fun k : ℕ => if k = 0 then (1 : ℝ) else n * (n + (k : ℝ)) ^ (k - 1) /
          (a ^ k * (Nat.factorial k : ℝ))) (x ^ n) := by
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, abs_zero] at ha
    linarith [hepos]
  set F : ℝ → ℝ := fun t => ∑' k : ℕ, abelTerm k t * (1 / a) ^ k / (Nat.factorial k : ℝ)
    with hFdef
  set x : ℝ := F 1 with hxdef
  set c : ℝ := (1 / a) * x with hcdef
  have hFadd : ∀ t s : ℝ, F t * F s = F (t + s) := fun t s => abel_tsum_mul t s a ha
  have hF0 : F 0 = 1 := abel_tsum_zero a ha
  have hFderiv : ∀ t : ℝ, HasDerivAt F (c * F t) t := by
    intro t
    have h := abel_hasDerivAt_tsum a ha t
    have hFt1 : (∑' k : ℕ, abelTerm k (t + 1) * (1 / a) ^ k / (Nat.factorial k : ℝ))
        = F t * x := by
      calc (∑' k : ℕ, abelTerm k (t + 1) * (1 / a) ^ k / (Nat.factorial k : ℝ))
          = F (t + 1) := rfl
        _ = F t * F 1 := (hFadd t 1).symm
        _ = F t * x := by rw [← hxdef]
    have hc : (1 / a) * (∑' k : ℕ, abelTerm k (t + 1) * (1 / a) ^ k
        / (Nat.factorial k : ℝ)) = c * F t := by
      rw [hFt1, hcdef]
      ring
    rw [hc] at h
    exact h
  have hGderiv : ∀ u : ℝ, HasDerivAt (fun t => F t * Real.exp (-(c * t))) 0 u := by
    intro u
    have hF := hFderiv u
    have hlin' : HasDerivAt (fun t : ℝ => -c * t) (-c) u := by
      have h1 := HasDerivAt.const_mul (-c) (hasDerivAt_id u)
      simpa using h1
    have hlin : HasDerivAt (fun t : ℝ => -(c * t)) (-c) u := by
      have hfeq : (fun t : ℝ => -(c * t)) = (fun t : ℝ => -c * t) := by
        funext t
        ring
      rw [hfeq]
      exact hlin'
    have hexp : HasDerivAt (fun t => Real.exp (-(c * t)))
        (Real.exp (-(c * u)) * -c) u :=
      HasDerivAt.exp hlin
    have hmul := HasDerivAt.mul hF hexp
    have heq : (c * F u) * Real.exp (-(c * u)) + F u * (Real.exp (-(c * u)) * -c)
        = 0 := by
      ring
    have hfun_eq : (fun t => F t * Real.exp (-(c * t)))
        = F * (fun t => Real.exp (-(c * t))) := by
      funext t
      rfl
    rw [hfun_eq]
    have hmul' : HasDerivAt (F * (fun t => Real.exp (-(c * t))))
        ((c * F u) * Real.exp (-(c * u)) + F u * (Real.exp (-(c * u)) * -c)) u :=
      hmul
    rw [heq] at hmul'
    exact hmul'
  have hGdiff : Differentiable ℝ (fun t => F t * Real.exp (-(c * t))) :=
    fun u => (hGderiv u).differentiableAt
  have hG0 : deriv (fun t => F t * Real.exp (-(c * t))) = 0 := by
    funext u
    exact (hGderiv u).deriv
  have hGconst := is_const_of_deriv_eq_zero hGdiff (fun x => congrFun hG0 x)
  have hG1 : ∀ t : ℝ, F t * Real.exp (-(c * t)) = 1 := by
    intro t
    have h : F t * Real.exp (-(c * t)) = F 0 * Real.exp (-(c * 0)) := hGconst t 0
    have hF0' : F 0 * Real.exp (-(c * 0)) = 1 := by
      rw [hF0]
      simp
    rw [hF0'] at h
    exact h
  have hFexp : ∀ t : ℝ, F t = Real.exp (c * t) := by
    intro t
    have h1 := hG1 t
    have hexp : Real.exp (c * t) * Real.exp (-(c * t)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc F t = F t * 1 := (mul_one _).symm
      _ = F t * (Real.exp (c * t) * Real.exp (-(c * t))) := by rw [hexp]
      _ = (F t * Real.exp (-(c * t))) * Real.exp (c * t) := by ring
      _ = 1 * Real.exp (c * t) := by rw [h1]
      _ = Real.exp (c * t) := one_mul _
  have hx_eq : x = Real.exp c := by
    have h1 := hFexp 1
    rw [← hxdef] at h1
    simpa using h1
  have hxpos : 0 < x := by
    rw [hx_eq]
    exact Real.exp_pos c
  have hlogx : Real.log x = c := by
    rw [hx_eq, Real.log_exp]
  have hax : x = a * Real.log x := by
    rw [hlogx, hcdef, ← mul_assoc, one_div, mul_inv_cancel₀ ha0, one_mul]
  have hseries : ∀ n : ℝ, HasSum (fun k : ℕ => abelTerm k n * (1 / a) ^ k
      / (Nat.factorial k : ℝ)) (x ^ n) := by
    intro n
    have hsum := (abel_summable' n a ha).hasSum
    have htsum : (∑' k : ℕ, abelTerm k n * (1 / a) ^ k / (Nat.factorial k : ℝ))
        = x ^ n := by
      have hFn : (∑' k : ℕ, abelTerm k n * (1 / a) ^ k / (Nat.factorial k : ℝ))
          = F n := by
        rw [hFdef]
      rw [hFn, hFexp n, Real.rpow_def_of_pos hxpos n, hlogx]
    rw [htsum] at hsum
    exact hsum
  refine ⟨x, hxpos, hax, fun n => ?_⟩
  have hser := hseries n
  have hfun : (fun k : ℕ => if k = 0 then (1 : ℝ) else n * (n + (k : ℝ)) ^ (k - 1) /
      (a ^ k * (Nat.factorial k : ℝ)))
      = (fun k : ℕ => abelTerm k n * (1 / a) ^ k / (Nat.factorial k : ℝ)) := by
    funext k
    by_cases hk : k = 0
    · subst hk
      simp [abelTerm_zero]
    · simp only [abelTerm, hk, ↓reduceIte]
      have hak : a ^ k ≠ 0 := pow_ne_zero k ha0
      have hfk : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      have h1 : ((1 : ℝ) / a) ^ k = 1 / a ^ k := by rw [div_pow, one_pow]
      rw [h1]
      conv_rhs => rw [mul_div_assoc, div_div, mul_one_div]
  rw [hfun]
  exact hser

end Entry13
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
