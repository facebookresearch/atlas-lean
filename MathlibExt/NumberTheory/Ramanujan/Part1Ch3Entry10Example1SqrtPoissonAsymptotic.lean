/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Finset.Range
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10Example1SqrtPoissonAsymptotic

namespace Aux

/-- Degree-5 Taylor polynomial of sqrt(1+u). -/
private noncomputable def P5 (u : ℝ) : ℝ :=
  1 + u/2 - u^2/8 + u^3/16 - 5*u^4/128 + 7*u^5/256

/-- Polynomial identity: P5(s^2-1) - s factors. -/
private lemma P5_identity (s : ℝ) :
    P5 (s^2 - 1) - s = (s-1)^6 * (7*s^4 + 42*s^3 + 102*s^2 + 122*s + 63) / 256 := by
  unfold P5; ring

/-- The quartic factor is small relative to (s+1)^6. -/
private lemma Q_le (s : ℝ) (hs : 0 ≤ s) :
    7*s^4 + 42*s^3 + 102*s^2 + 122*s + 63 ≤ 336*(s+1)^6 := by
  have e : (336:ℝ)*(s+1)^6
      = 336*s^6 + 2016*s^5 + 5040*s^4 + 6720*s^3 + 5040*s^2 + 2016*s + 336 := by ring
  have p2 := pow_nonneg hs 2
  have p3 := pow_nonneg hs 3
  have p4 := pow_nonneg hs 4
  have p5 := pow_nonneg hs 5
  have p6 := pow_nonneg hs 6
  linarith

/-- Taylor bound for sqrt via the polynomial identity. -/
private lemma P5_bound (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ P5 (s^2 - 1) - s ∧ P5 (s^2 - 1) - s ≤ (21/16) * (s^2 - 1)^6 := by
  have hQnn : (0:ℝ) ≤ 7*s^4 + 42*s^3 + 102*s^2 + 122*s + 63 := by positivity
  have h6nn : (0:ℝ) ≤ (s-1)^6 := by positivity
  have hQ := Q_le s hs
  have hid := P5_identity s
  have hsq : (s^2 - 1)^6 = (s-1)^6 * (s+1)^6 := by ring
  constructor
  · rw [hid]
    positivity
  · rw [hid, hsq]
    have h1 : (7*s^4 + 42*s^3 + 102*s^2 + 122*s + 63)/256
        ≤ (21/16) * (s+1)^6 := by
      have : 7*s^4 + 42*s^3 + 102*s^2 + 122*s + 63 ≤ 336 * (s+1)^6 := hQ
      linarith
    calc (s-1)^6 * (7*s^4 + 42*s^3 + 102*s^2 + 122*s + 63) / 256
        = (s-1)^6 * ((7*s^4 + 42*s^3 + 102*s^2 + 122*s + 63)/256) := by ring
      _ ≤ (s-1)^6 * ((21/16) * (s+1)^6) :=
          mul_le_mul_of_nonneg_left h1 h6nn
      _ = (21/16) * ((s-1)^6 * (s+1)^6) := by ring
/-- Poisson weights. -/
private noncomputable def pw (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-x) * x ^ n / (Nat.factorial n : ℝ)

private lemma poisson_base (x : ℝ) (hx : 0 ≤ x) :
    HasSum (fun n : ℕ => pw x n) 1 := by
  have h := ProbabilityTheory.hasSum_one_poissonMeasure (⟨x, hx⟩ : NNReal)
  have heq : (fun n : ℕ => pw x n)
      = (fun n : ℕ => Real.exp (-↑(⟨x, hx⟩ : NNReal)) * (↑(⟨x, hx⟩ : NNReal)) ^ n /
          ↑n.factorial) := by
    funext n
    unfold pw
    simp
  rw [heq]
  exact h

/-- Termwise identity for the shift. -/
private lemma shift_term (x : ℝ) (g : ℕ → ℝ) (m : ℕ) :
    (((m+1 : ℕ) : ℝ)) * g (m+1) * pw x (m+1) = x * (g (m+1) * pw x m) := by
  unfold pw
  have hfact : ((Nat.factorial m : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  have hm1 : (((m+1 : ℕ)) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Shift lemma: E[n g(n)] = x E[g(n+1)]. -/
private lemma shift_HasSum (x : ℝ) (g : ℕ → ℝ) (T : ℝ)
    (h : HasSum (fun m : ℕ => g (m+1) * pw x m) T) :
    HasSum (fun n : ℕ => (n : ℝ) * g n * pw x n) (x * T) := by
  have hmul := h.mul_left x
  have h2 : HasSum (fun m : ℕ => (((m+1 : ℕ) : ℝ)) * g (m+1) * pw x (m+1)) (x * T) := by
    refine hmul.congr_fun (fun m => ?_)
    exact shift_term x g m
  have h2' : HasSum (fun n : ℕ => (fun n : ℕ => (n:ℝ) * g n * pw x n) (n+1)) (x * T) := h2
  have hmain := (hasSum_nat_add_iff (f := fun n : ℕ => (n:ℝ) * g n * pw x n) 1).mp h2'
  simp only [Finset.sum_range_one] at hmain
  simpa using hmain

-- Moment 0
private lemma mu0 (x : ℝ) (hx : 0 ≤ x) :
    HasSum (fun n : ℕ => ((n : ℝ)-x)^0 * pw x n) 1 := by
  have h := poisson_base x hx
  refine h.congr_fun (fun n => ?_)
  show ((n : ℝ)-x)^0 * pw x n = pw x n
  rw [pow_zero, one_mul]

-- Moment 1: mu_1 = 0
private lemma mu1 (x : ℝ) (hx : 0 ≤ x) :
    HasSum (fun n : ℕ => ((n : ℝ)-x)^1 * pw x n) 0 := by
  have hbase := poisson_base x hx
  -- inner: g = fun n => 1, terms g(m+1) * pw = pw, sum 1
  have hinner : HasSum (fun m : ℕ => (1 : ℝ) * pw x m) 1 := by
    refine hbase.congr_fun (fun m => ?_)
    show (1 : ℝ) * pw x m = pw x m
    rw [one_mul]
  -- shift with g = fun _ => 1
  have hshift : HasSum (fun n : ℕ => (n : ℝ) * (1 : ℝ) * pw x n) (x * 1) :=
    shift_HasSum x (fun _ => 1) 1 hinner
  have hsub := hshift.sub (hbase.mul_left x)
  -- hsub : HasSum (fun n => n*1*pw - x*pw) (x*1 - x*1)
  have hval : x * 1 - x * 1 = (0 : ℝ) := by ring
  rw [hval] at hsub
  refine hsub.congr_fun (fun n => ?_)
  change ((n : ℝ)-x)^1 * pw x n = (n : ℝ) * 1 * pw x n - x * pw x n
  ring

-- Moment 2: mu_2 = x
private lemma mu2 (x : ℝ) (hx : 0 ≤ x) :
    HasSum (fun n : ℕ => ((n : ℝ)-x)^2 * pw x n) x := by
  have h0 := mu0 x hx
  have h1 := mu1 x hx
  have hinner : HasSum (fun m : ℕ => (((m+1 : ℕ) : ℝ)-x)^1 * pw x m) (0 + 1) := by
    refine (h1.add h0).congr_fun (fun m => ?_)
    show (((m+1 : ℕ) : ℝ)-x)^1 * pw x m
        = ((m : ℝ)-x)^1 * pw x m + ((m : ℝ)-x)^0 * pw x m
    push_cast
    ring
  have hshift := shift_HasSum x (fun n => ((n : ℝ)-x)^1) (0+1) hinner
  have hsub := hshift.sub (h1.mul_left x)
  have hval : x * (0+1) - x * 0 = x := by ring
  rw [hval] at hsub
  refine hsub.congr_fun (fun n => ?_)
  show ((n : ℝ)-x)^2 * pw x n
      = (n : ℝ) * (((n : ℝ)-x)^1) * pw x n - x * (((n : ℝ)-x)^1 * pw x n)
  ring

-- Moment 3: mu_3 = x
private lemma mu3 (x : ℝ) (hx : 0 ≤ x) :
    HasSum (fun n : ℕ => ((n : ℝ)-x)^3 * pw x n) x := by
  have h0 := mu0 x hx
  have h1 := mu1 x hx
  have h2 := mu2 x hx
  have hinner : HasSum (fun m : ℕ => (((m+1 : ℕ) : ℝ)-x)^2 * pw x m) ((x + 2*0) + 1) := by
    refine ((h2.add (h1.mul_left 2)).add h0).congr_fun (fun m => ?_)
    show (((m+1 : ℕ) : ℝ)-x)^2 * pw x m
        = (((m : ℝ)-x)^2 * pw x m + 2 * (((m : ℝ)-x)^1 * pw x m))
          + ((m : ℝ)-x)^0 * pw x m
    push_cast
    ring
  have hshift := shift_HasSum x (fun n => ((n : ℝ)-x)^2) ((x + 2*0) + 1) hinner
  have hsub := hshift.sub (h2.mul_left x)
  have hval : x * ((x + 2*0) + 1) - x * x = x := by ring
  rw [hval] at hsub
  refine hsub.congr_fun (fun n => ?_)
  show ((n : ℝ)-x)^3 * pw x n
      = (n : ℝ) * (((n : ℝ)-x)^2) * pw x n - x * (((n : ℝ)-x)^2 * pw x n)
  ring

-- Moment 4: mu_4 = 3x^2 + x
private lemma mu4 (x : ℝ) (hx : 0 ≤ x) :
    HasSum (fun n : ℕ => ((n : ℝ)-x)^4 * pw x n) (3*x^2 + x) := by
  have h0 := mu0 x hx
  have h1 := mu1 x hx
  have h2 := mu2 x hx
  have h3 := mu3 x hx
  have hinner : HasSum (fun m : ℕ => (((m+1 : ℕ) : ℝ)-x)^3 * pw x m)
      (((x + 3*x) + 3*0) + 1) := by
    refine (((h3.add (h2.mul_left 3)).add (h1.mul_left 3)).add h0).congr_fun (fun m => ?_)
    show (((m+1 : ℕ) : ℝ)-x)^3 * pw x m
        = ((((m : ℝ)-x)^3 * pw x m + 3 * (((m : ℝ)-x)^2 * pw x m))
            + 3 * (((m : ℝ)-x)^1 * pw x m))
          + ((m : ℝ)-x)^0 * pw x m
    push_cast
    ring
  have hshift := shift_HasSum x (fun n => ((n : ℝ)-x)^3) (((x + 3*x) + 3*0) + 1) hinner
  have hsub := hshift.sub (h3.mul_left x)
  have hval : x * (((x + 3*x) + 3*0) + 1) - x * x = 3*x^2 + x := by ring
  rw [hval] at hsub
  refine hsub.congr_fun (fun n => ?_)
  show ((n : ℝ)-x)^4 * pw x n
      = (n : ℝ) * (((n : ℝ)-x)^3) * pw x n - x * (((n : ℝ)-x)^3 * pw x n)
  ring

-- Moment 5: mu_5 = 10x^2 + x
private lemma mu5 (x : ℝ) (hx : 0 ≤ x) :
    HasSum (fun n : ℕ => ((n : ℝ)-x)^5 * pw x n) (10*x^2 + x) := by
  have h0 := mu0 x hx
  have h1 := mu1 x hx
  have h2 := mu2 x hx
  have h3 := mu3 x hx
  have h4 := mu4 x hx
  have hinner : HasSum (fun m : ℕ => (((m+1 : ℕ) : ℝ)-x)^4 * pw x m)
      (((((3*x^2+x) + 4*x) + 6*x) + 4*0) + 1) := by
    refine ((((h4.add (h3.mul_left 4)).add (h2.mul_left 6)).add
      (h1.mul_left 4)).add h0).congr_fun (fun m => ?_)
    show (((m+1 : ℕ) : ℝ)-x)^4 * pw x m
        = ((((((m : ℝ)-x)^4 * pw x m + 4 * (((m : ℝ)-x)^3 * pw x m))
            + 6 * (((m : ℝ)-x)^2 * pw x m))
            + 4 * (((m : ℝ)-x)^1 * pw x m)))
          + ((m : ℝ)-x)^0 * pw x m
    push_cast
    ring
  have hshift := shift_HasSum x (fun n => ((n : ℝ)-x)^4)
    (((((3*x^2+x) + 4*x) + 6*x) + 4*0) + 1) hinner
  have hsub := hshift.sub (h4.mul_left x)
  have hval : x * (((((3*x^2+x) + 4*x) + 6*x) + 4*0) + 1) - x * (3*x^2+x)
      = 10*x^2 + x := by ring
  rw [hval] at hsub
  refine hsub.congr_fun (fun n => ?_)
  show ((n : ℝ)-x)^5 * pw x n
      = (n : ℝ) * (((n : ℝ)-x)^4) * pw x n - x * (((n : ℝ)-x)^4 * pw x n)
  ring

-- Moment 6: mu_6 = 15x^3 + 25x^2 + x
private lemma mu6 (x : ℝ) (hx : 0 ≤ x) :
    HasSum (fun n : ℕ => ((n : ℝ)-x)^6 * pw x n) (15*x^3 + 25*x^2 + x) := by
  have h0 := mu0 x hx
  have h1 := mu1 x hx
  have h2 := mu2 x hx
  have h3 := mu3 x hx
  have h4 := mu4 x hx
  have h5 := mu5 x hx
  have hinner : HasSum (fun m : ℕ => (((m+1 : ℕ) : ℝ)-x)^5 * pw x m)
      ((((((10*x^2+x) + 5*(3*x^2+x)) + 10*x) + 10*x) + 5*0) + 1) := by
    refine (((((h5.add (h4.mul_left 5)).add (h3.mul_left 10)).add
      (h2.mul_left 10)).add (h1.mul_left 5)).add h0).congr_fun (fun m => ?_)
    show (((m+1 : ℕ) : ℝ)-x)^5 * pw x m
        = (((((((m : ℝ)-x)^5 * pw x m + 5 * (((m : ℝ)-x)^4 * pw x m))
            + 10 * (((m : ℝ)-x)^3 * pw x m))
            + 10 * (((m : ℝ)-x)^2 * pw x m))
            + 5 * (((m : ℝ)-x)^1 * pw x m)))
          + ((m : ℝ)-x)^0 * pw x m
    push_cast
    ring
  have hshift := shift_HasSum x (fun n => ((n : ℝ)-x)^5)
    ((((((10*x^2+x) + 5*(3*x^2+x)) + 10*x) + 10*x) + 5*0) + 1) hinner
  have hsub := hshift.sub (h5.mul_left x)
  have hval : x * ((((((10*x^2+x) + 5*(3*x^2+x)) + 10*x) + 10*x) + 5*0) + 1)
      - x * (10*x^2+x) = 15*x^3 + 25*x^2 + x := by ring
  rw [hval] at hsub
  refine hsub.congr_fun (fun n => ?_)
  show ((n : ℝ)-x)^6 * pw x n
      = (n : ℝ) * (((n : ℝ)-x)^5) * pw x n - x * (((n : ℝ)-x)^5 * pw x n)
  ring

-- Step 3: expectation of P5(u_n), for x > 0.
private lemma P5exp (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => P5 (((n : ℝ)-x)/x) * pw x n)
      (1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hxnn : (0:ℝ) ≤ x := le_of_lt hx
  have h0 := mu0 x hxnn
  have h1 := mu1 x hxnn
  have h2 := mu2 x hxnn
  have h3 := mu3 x hxnn
  have h4 := mu4 x hxnn
  have h5 := mu5 x hxnn
  have hcombo :=
    (((((h0.mul_left 1).add (h1.mul_left (1/2/x))).add
      (h2.mul_left (-1/8/x^2))).add (h3.mul_left (1/16/x^3))).add
      (h4.mul_left (-5/128/x^4))).add (h5.mul_left (7/256/x^5))
  have hval : ((((1*1 + (1/2/x)*0) + (-1/8/x^2)*x) + (1/16/x^3)*x)
      + (-5/128/x^4)*(3*x^2+x)) + (7/256/x^5)*(10*x^2+x)
      = 1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4) := by
    field_simp
    ring
  rw [hval] at hcombo
  refine hcombo.congr_fun (fun n => ?_)
  show P5 (((n:ℝ)-x)/x) * pw x n = (((((1 * (((n:ℝ)-x)^0 * pw x n)
      + (1/2/x) * (((n:ℝ)-x)^1 * pw x n))
      + (-1/8/x^2) * (((n:ℝ)-x)^2 * pw x n))
      + (1/16/x^3) * (((n:ℝ)-x)^3 * pw x n))
      + (-5/128/x^4) * (((n:ℝ)-x)^4 * pw x n))
      + (7/256/x^5) * (((n:ℝ)-x)^5 * pw x n))
  unfold P5
  field_simp
  ring

-- Step 4a: nonnegativity of Poisson weights.
private lemma pw_nn (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ pw x n := by
  unfold pw
  apply div_nonneg _ (by exact_mod_cast Nat.zero_le _)
  apply mul_nonneg (le_of_lt (Real.exp_pos _)) (pow_nonneg hx _)

-- Error terms E_n = P5(u_n) - s_n.
private noncomputable def TErr (x : ℝ) (n : ℕ) : ℝ :=
  P5 (((n:ℝ)-x)/x) - Real.sqrt ((n:ℝ)/x)

-- Step 4b: pointwise Taylor error bound.
private lemma E_bound (x : ℝ) (hx : 0 < x) (n : ℕ) :
    0 ≤ TErr x n ∧ TErr x n ≤ (21/16) * ((((n:ℝ)-x)/x))^6 := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hnn : (0:ℝ) ≤ (n:ℝ)/x := by
    apply div_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt hx)
  have hsq : (Real.sqrt ((n:ℝ)/x))^2 - 1 = ((n:ℝ)-x)/x := by
    rw [Real.sq_sqrt hnn]
    field_simp
  have hbd := P5_bound (Real.sqrt ((n:ℝ)/x)) (Real.sqrt_nonneg _)
  rw [hsq] at hbd
  unfold TErr
  exact hbd

-- Step 4c: the error series is summable with an explicit bound.
private lemma errExists (x : ℝ) (hx : 1 ≤ x) :
    ∃ errV : ℝ, HasSum (fun n => pw x n * TErr x n) errV ∧ 0 ≤ errV ∧
      errV ≤ (21/16/x^6)*(15*x^3+25*x^2+x) := by
  have hxp : 0 < x := by linarith
  have hxnn : (0:ℝ) ≤ x := le_of_lt hxp
  have hx0 : x ≠ 0 := ne_of_gt hxp
  have hBsum := (mu6 x hxnn).mul_left (21/16/x^6)
  have hle : ∀ n : ℕ, pw x n * TErr x n ≤ (21/16/x^6) * (((n:ℝ)-x)^6 * pw x n) := by
    intro n
    have hE := (E_bound x hxp n).2
    calc pw x n * TErr x n
        ≤ pw x n * ((21/16) * ((((n:ℝ)-x)/x))^6) :=
          mul_le_mul_of_nonneg_left hE (pw_nn x hxnn n)
      _ = (21/16/x^6) * (((n:ℝ)-x)^6 * pw x n) := by
          rw [div_pow]
          ring
  have hnn : ∀ n : ℕ, 0 ≤ pw x n * TErr x n := by
    intro n
    exact mul_nonneg (pw_nn x hxnn n) (E_bound x hxp n).1
  have hsum : Summable (fun n => pw x n * TErr x n) :=
    Summable.of_nonneg_of_le hnn hle hBsum.summable
  refine ⟨∑' n, pw x n * TErr x n, hsum.hasSum, ?_, ?_⟩
  · exact tsum_nonneg hnn
  · have h := hasSum_le hle hsum.hasSum hBsum
    simpa using h

-- Step 4d: A = sum p_n s_n equals P5-expectation minus error.
private lemma AHasSum (x : ℝ) (hx : 0 < x) (errV : ℝ)
    (herr : HasSum (fun n => pw x n * TErr x n) errV) :
    HasSum (fun n => pw x n * Real.sqrt ((n:ℝ)/x))
      ((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) := by
  have hP := P5exp x hx
  have hsub := hP.sub herr
  refine hsub.congr_fun (fun n => ?_)
  change pw x n * Real.sqrt ((n:ℝ)/x)
      = P5 (((n:ℝ)-x)/x) * pw x n - pw x n * TErr x n
  unfold TErr
  ring

-- Step 4e: sqrt(n) = sqrt(x) * sqrt(n/x), summed.
private lemma sqrtHasSum (x : ℝ) (hx : 0 < x) (errV : ℝ)
    (herr : HasSum (fun n => pw x n * TErr x n) errV) :
    HasSum (fun n => pw x n * Real.sqrt (n:ℝ))
      (Real.sqrt x * ((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV)) := by
  have hxnn : (0:ℝ) ≤ x := le_of_lt hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hA := AHasSum x hx errV herr
  have hmul := hA.mul_left (Real.sqrt x)
  refine hmul.congr_fun (fun n => ?_)
  have hsq : Real.sqrt (n:ℝ) = Real.sqrt x * Real.sqrt ((n:ℝ)/x) := by
    have h1 : x * ((n:ℝ)/x) = (n:ℝ) := by field_simp
    calc Real.sqrt (n:ℝ) = Real.sqrt (x * ((n:ℝ)/x)) := by rw [h1]
      _ = Real.sqrt x * Real.sqrt ((n:ℝ)/x) := Real.sqrt_mul hxnn _
  change pw x n * Real.sqrt (n:ℝ)
      = Real.sqrt x * (pw x n * Real.sqrt ((n:ℝ)/x))
  rw [hsq]
  ring

-- Step 4f: multiply by e^x to get the S-series terms.
private lemma FHasSum (x : ℝ) (hx : 0 < x) (errV : ℝ)
    (herr : HasSum (fun n => pw x n * TErr x n) errV) :
    HasSum (fun n : ℕ => x^n * Real.sqrt (n:ℝ) / (Nat.factorial n : ℝ))
      (Real.exp x * (Real.sqrt x *
        ((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV))) := by
  have hS := sqrtHasSum x hx errV herr
  have hmul := hS.mul_left (Real.exp x)
  refine hmul.congr_fun (fun n => ?_)
  have hexp : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hfact : ((Nat.factorial n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hcalc : Real.exp x * (pw x n * Real.sqrt (n:ℝ))
      = x^n * Real.sqrt (n:ℝ) / (Nat.factorial n : ℝ) := by
    calc Real.exp x * (pw x n * Real.sqrt (n:ℝ))
        = (Real.exp x * Real.exp (-x)) * (x^n * Real.sqrt (n:ℝ) / (Nat.factorial n : ℝ)) := by
          unfold pw
          field_simp
      _ = x^n * Real.sqrt (n:ℝ) / (Nat.factorial n : ℝ) := by
          rw [hexp, one_mul]
  change x^n * Real.sqrt (n:ℝ) / (Nat.factorial n : ℝ)
      = Real.exp x * (pw x n * Real.sqrt (n:ℝ))
  exact hcalc.symm

-- Step 4g: shift the index (n = j+1) to match the statement's sum.
private lemma SHasSum (x : ℝ) (hx : 0 < x) (errV : ℝ)
    (herr : HasSum (fun n => pw x n * TErr x n) errV) :
    HasSum (fun j : ℕ => x ^ (j + 1) * Real.sqrt (↑(j + 1) : ℝ) /
        (↑(Nat.factorial (j + 1)) : ℝ))
      (Real.exp x * (Real.sqrt x *
        ((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV))) := by
  have hF := FHasSum x hx errV herr
  have hshift := (hasSum_nat_add_iff'
    (f := fun n : ℕ => x^n * Real.sqrt (n:ℝ) / (Nat.factorial n : ℝ)) 1).mpr hF
  simp only [Finset.sum_range_one] at hshift
  have hF0' : x^(0:ℕ) * Real.sqrt (((0:ℕ)):ℝ) / (((Nat.factorial 0 : ℕ)):ℝ) = 0 := by
    simp
  rw [hF0'] at hshift
  simpa using hshift

-- Step 5a: the log-Taylor piece, with abstract center d.
private lemma logPiece (d L : ℝ) (hd : |d| ≤ 1 / 2) (hL : L = Real.log (1 + d)) :
    |L - d + d^2/2| ≤ 2*|d|^3 := by
  have hylt : |-d| < 1 := by
    rw [abs_neg]
    linarith
  have hlogbd := Real.abs_log_sub_add_sum_range_le (x := -d) hylt 2
  have e2 : Finset.range 2 = Finset.range (1 + 1) := rfl
  have e1 : Finset.range 1 = Finset.range (0 + 1) := rfl
  have hsum2 : (∑ i ∈ Finset.range 2, (-d)^(i+1)/((i:ℝ)+1)) = -d + d^2/2 := by
    rw [e2, Finset.sum_range_succ, e1, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  have h1d : (1:ℝ) - -d = 1 + d := by ring
  have e3 : (2:ℕ)+1 = 3 := rfl
  rw [hsum2, h1d, ← hL, abs_neg, e3] at hlogbd
  have hden : (1/2:ℝ) ≤ 1 - |d| := by linarith
  have hstep : |d|^3/(1-|d|) ≤ |d|^3/(1/2) :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
  have htwo : |d|^3/(1/2:ℝ) = 2*|d|^3 := by ring
  have hcong : (-d + d^2/2 + L) = (L - d + d^2/2) := by ring
  rw [hcong] at hlogbd
  linarith

-- Step 5b: master explicit bound for one x >= 8.
private lemma finalBound (x errV : ℝ) (hx : 8 ≤ x)
    (herr_nn : 0 ≤ errV)
    (herr_le : errV ≤ (21 / 16 / x ^ 6) * (15 * x ^ 3 + 25 * x ^ 2 + x))
    (hStsum : (∑' (j : ℕ), x ^ (j + 1) * Real.sqrt (↑(j + 1) : ℝ) /
        (↑(Nat.factorial (j + 1)) : ℝ))
      = Real.exp x * (Real.sqrt x *
        ((1 - 1 / (8 * x) - 7 / (128 * x ^ 2) + 15 / (64 * x ^ 3) + 7 / (256 * x ^ 4)) - errV))) :
    ‖Real.log (∑' (j : ℕ), x ^ (j + 1) * Real.sqrt (↑(j + 1) : ℝ) /
        (↑(Nat.factorial (j + 1)) : ℝ))
      - (x + 1 / 2 * Real.log x - 1 / (8 * x) - 1 / (16 * x ^ 2))‖
      ≤ 1705 * ‖(1 : ℝ)/x^3‖ := by
  have hxp : 0 < x := by linarith
  have hx0 : x ≠ 0 := ne_of_gt hxp
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hxnn : (0:ℝ) ≤ x := le_of_lt hxp
  have h3pos : (0:ℝ) < x^3 := pow_pos hxp 3
  have h8x : (0:ℝ) < 8*x := by linarith
  have h64x : (0:ℝ) < 64*x := by linarith
  -- powers of x comparisons
  have hx23 : x^2 ≤ x^3 := pow_le_pow_right₀ hx1 (by norm_num)
  have hx12 : x^1 ≤ x^2 := pow_le_pow_right₀ hx1 (by norm_num)
  have hx13 : x^1 ≤ x^3 := pow_le_pow_right₀ hx1 (by norm_num)
  have h8xxm : 8*x ≤ x*x := mul_le_mul_of_nonneg_right (by linarith) hxnn
  have h8xx : 8*x ≤ x^2 := by
    calc 8*x ≤ x*x := h8xxm
      _ = x^2 := by ring
  have h64xxx : 64*x ≤ x^3 := by
    calc 64*x = 8*(8*x) := by ring
      _ ≤ 8*(x*x) := mul_le_mul_of_nonneg_left h8xxm (by norm_num)
      _ = 8*x^2 := by ring
      _ ≤ x*x^2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = x^3 := by ring
  have h34 : x^3 ≤ x^4 := pow_le_pow_right₀ hx1 (by norm_num)
  -- reciprocal comparisons
  have r43 : (1:ℝ)/x^4 ≤ 1/x^3 :=
    one_div_le_one_div_of_le h3pos h34
  have r21 : (1:ℝ)/x^2 ≤ 1/(8*x) :=
    one_div_le_one_div_of_le h8x h8xx
  have r31 : (1:ℝ)/x^3 ≤ 1/(64*x) :=
    one_div_le_one_div_of_le h64x h64xxx
  -- |errV| bound
  have hCerr : |errV| ≤ 861/(16*x^3) := by
    have h3 : 15*x^3+25*x^2+x ≤ 41*x^3 := by
      have e1 : x^1 = x := pow_one x
      linarith
    have h4 : (21/16/x^6)*(15*x^3+25*x^2+x) ≤ (21/16/x^6)*(41*x^3) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : (21/16/x^6)*(41*x^3) = 861/(16*x^3) := by
      have hx6 : (x^6:ℝ) ≠ 0 := pow_ne_zero 6 hx0
      have hx3 : (x^3:ℝ) ≠ 0 := pow_ne_zero 3 hx0
      field_simp
      ring
    rw [abs_of_nonneg herr_nn]
    linarith
  -- eta bound
  have hpos3 : (0:ℝ) ≤ 1/x^3 := le_of_lt (one_div_pos.mpr h3pos)
  have hpos4 : (0:ℝ) ≤ 1/x^4 :=
    le_of_lt (one_div_pos.mpr (pow_pos hxp 4))
  have h2 : errV ≤ |errV| := le_abs_self errV
  have g1 : errV ≤ 861/(16*x^3) := le_trans h2 hCerr
  have g3 : (861:ℝ)/(16*x^3) ≤ 56/x^3 := by
    have h1 : (861:ℝ)/(16*x^3) = (861/16)*(1/x^3) := by ring
    have h4' : (56:ℝ)/x^3 = 56*(1/x^3) := by ring
    rw [h1, h4']
    exact mul_le_mul_of_nonneg_right (by norm_num) hpos3
  -- g2 : 15/(64x^3) + 7/(256x^4) ≤ 1/x^3
  have g2 : 15/(64*x^3) + 7/(256*x^4) ≤ 1/x^3 := by
    have e1 : (15:ℝ)/(64*x^3) = (15/64)*(1/x^3) := by ring
    have e2 : (7:ℝ)/(256*x^4) = (7/256)*(1/x^4) := by ring
    rw [e1, e2]
    have h1 : (15/64:ℝ)*(1/x^3) ≤ (15/64)*(1/x^3) := le_rfl
    have h2b : (7/256:ℝ)*(1/x^4) ≤ (7/256)*(1/x^3) :=
      mul_le_mul_of_nonneg_left r43 (by norm_num)
    have h3 : (15/64:ℝ)*(1/x^3) + (7/256)*(1/x^4) ≤ (15/64)*(1/x^3) + (7/256)*(1/x^3) :=
      add_le_add h1 h2b
    have h4 : (15/64:ℝ)*(1/x^3) + (7/256)*(1/x^3) ≤ 1*(1/x^3) := by
      have e : (15/64:ℝ)*(1/x^3) + (7/256)*(1/x^3) = ((15/64+7/256))*(1/x^3) := by ring
      rw [e]
      apply mul_le_mul_of_nonneg_right _ hpos3
      norm_num
    have h5 : (1:ℝ)*(1/x^3) = 1/x^3 := one_mul _
    linarith [h3, h4, h5]
  have ga : (0:ℝ) ≤ 15/(64*x^3) := by
    have h : (15:ℝ)/(64*x^3) = (15/64)*(1/x^3) := by ring
    rw [h]
    exact mul_nonneg (by norm_num) hpos3
  have gb : (0:ℝ) ≤ 7/(256*x^4) := by
    have h : (7:ℝ)/(256*x^4) = (7/256)*(1/x^4) := by ring
    rw [h]
    exact mul_nonneg (by norm_num) hpos4
  have heta : |15/(64*x^3) + 7/(256*x^4) - errV| ≤ 56/x^3 := by
    have hb : 7/(256*x^4) ≤ 7/(256*x^3) := by
      calc 7/(256*x^4) = (7/256)*(1/x^4) := by ring
        _ ≤ (7/256)*(1/x^3) :=
          mul_le_mul_of_nonneg_left r43 (by norm_num)
        _ = 7/(256*x^3) := by ring
    have h1 : -(errV) ≤ |errV| := by
      have h := le_abs_self (-errV)
      rwa [abs_neg] at h
    have hfin : (15:ℝ)/(64*x^3) + 7/(256*x^3) + 861/(16*x^3) ≤ 56/x^3 := by
      have hx3p : (0:ℝ) < 1/x^3 := one_div_pos.mpr h3pos
      calc 15/(64*x^3) + 7/(256*x^3) + 861/(16*x^3)
          = (15/64 + 7/256 + 861/16)*(1/x^3) := by ring
        _ ≤ 56*(1/x^3) := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hx3p)
            norm_num
        _ = 56/x^3 := by ring
    rw [abs_le]
    constructor
    · linarith [g1, g3, ga, gb]
    · linarith [hb, h1, hCerr, hfin]
  -- rho bound
  have hab7 : |-7/(128*x^2)| = 7/(128*x^2) := by
    have e : (-7:ℝ)/(128*x^2) = -(7/(128*x^2)) := by ring
    have hx2pos : (0:ℝ) < x^2 := pow_pos hxp 2
    have h128 : (0:ℝ) < 128*x^2 := by linarith
    have h7 : (0:ℝ) < 7/(128*x^2) := by
      have e2 : (7:ℝ)/(128*x^2) = 7 * (1/(128*x^2)) := by ring
      rw [e2]
      exact mul_pos (by norm_num) (one_div_pos.mpr h128)
    rw [e, abs_neg]
    exact abs_of_pos h7
  have hrho : |-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV)| ≤ 57/x^2 := by
    have t2 : |-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV)|
        ≤ |-7/(128*x^2)| + |15/(64*x^3) + 7/(256*x^4) - errV| :=
      abs_add_le _ _
    have t3 : |-7/(128*x^2)| = 7/(128*x^2) := hab7
    have t4 : 7/(128*x^2) + 56/x^3 ≤ 57/x^2 := by
      have c1 : 7/(128*x^2) = (7/128)*(1/x^2) := by ring
      have c2 : (56:ℝ)/x^3 = 56*(1/x^2)*(1/x) := by
        field_simp
      have c3 : (57:ℝ)/x^2 = 57*(1/x^2) := by ring
      have hxinv : (0:ℝ) ≤ 1/x := le_of_lt (one_div_pos.mpr hxp)
      have hx2 : (0:ℝ) ≤ 1/x^2 :=
        le_of_lt (one_div_pos.mpr (pow_pos hxp 2))
      have h8 : (1:ℝ)/x ≤ 1/8 := by
        have := one_div_le_one_div_of_le (show (0:ℝ) < 8 by norm_num) (by linarith : (8:ℝ) ≤ x)
        simpa using this
      rw [c1, c2, c3]
      have hnn : (0:ℝ) ≤ 56*(1/x^2) :=
        mul_nonneg (by norm_num) hx2
      have h56 : (56:ℝ)*(1/x^2)*(1/x) ≤ 56*(1/x^2)*(1/8) :=
        mul_le_mul_of_nonneg_left h8 hnn
      linarith [h56, hx2, hpos3]
    linarith [t2, t3, heta, t4]
  -- delta bound
  have hd_eq : (((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1)
      = -1/(8*x) + (-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV)) := by
    field_simp
    ring
  have t1 : |(((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1)|
      ≤ 1/(8*x) + |-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV)| := by
    have h2 := abs_add_le (-1/(8*x))
      (-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))
    have h3 : |-1/(8*x)| = 1/(8*x) := by
      have e : (-1:ℝ)/(8*x) = -(1/(8*x)) := by ring
      rw [e, abs_neg]
      exact abs_of_pos (one_div_pos.mpr h8x)
    rw [hd_eq]
    rw [h3] at h2
    exact h2
  have t2r : |-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV)|
      ≤ 7/(128*x^2) + |15/(64*x^3) + 7/(256*x^4) - errV| := by
    have h2 := abs_add_le (-7/(128*x^2)) (15/(64*x^3) + 7/(256*x^4) - errV)
    rw [hab7] at h2
    exact h2
  have hdelta : |(((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1)|
      ≤ 2/x := by
    have g1 : 7/(128*x^2) ≤ 7/(1024*x) := by
      calc 7/(128*x^2) = (7/128)*(1/x^2) := by ring
        _ ≤ (7/128)*(1/(8*x)) := mul_le_mul_of_nonneg_left r21 (by norm_num)
        _ = 7/(1024*x) := by ring
    have g2 : 56/x^3 ≤ 7/(8*x) := by
      calc 56/x^3 = 56*(1/x^3) := by ring
        _ ≤ 56*(1/(64*x)) := mul_le_mul_of_nonneg_left r31 (by norm_num)
        _ = 7/(8*x) := by ring
    have e1 : (1:ℝ)/(8*x) + 7/(1024*x) + 7/(8*x) = (1031/1024)*(1/x) := by
      field_simp
      ring
    have e2 : (2:ℝ)/x = 2*(1/x) := by ring
    have hx1inv : (0:ℝ) ≤ 1/x := le_of_lt (one_div_pos.mpr hxp)
    have e3 : (1031/1024:ℝ)*(1/x) ≤ 2*(1/x) :=
      mul_le_mul_of_nonneg_right (by norm_num) hx1inv
    linarith [t1, t2r, heta, g1, g2, e1, e2, e3]
  have hx8 : (2:ℝ)/x ≤ 1/2 := by
    have h14 : (1:ℝ)/x ≤ 1/4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith : (4:ℝ) ≤ x)
    have e : (2:ℝ)/x = 2*(1/x) := by ring
    rw [e]
    linarith [h14]
  have hhalf : |(((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1)|
      ≤ 1/2 := le_trans hdelta hx8
  have hApos : 0 < (1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV := by
    have h1 : -(1/2:ℝ)
        ≤ ((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1 :=
      (abs_le.mp hhalf).1
    linarith
  -- log decomposition
  have e1 : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have e2 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hxp).ne'
  have e3 : ((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) ≠ 0 :=
    ne_of_gt hApos
  have hlog : Real.log (Real.exp x * (Real.sqrt x *
      ((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV)))
      = x + Real.log x / 2
        + Real.log ((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) := by
    rw [Real.log_mul e1 (mul_ne_zero e2 e3), Real.log_exp,
      Real.log_mul e2 e3, Real.log_sqrt hxnn]
    ring
  -- R bound via the abstract log piece
  have hR : |Real.log ((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV)
      - ((((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1))
      + ((((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1)^2/2)|
      ≤ 16/x^3 := by
    have hLP := logPiece
      ((((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1))
      (Real.log (1 + ((((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1))))
      hhalf rfl
    have h1dA : (1:ℝ) + ((((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1))
        = ((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) := by
      ring
    rw [h1dA] at hLP
    have hcub : |(((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1)|^3
        ≤ (2/x)^3 :=
      pow_le_pow_left₀ (abs_nonneg _) hdelta 3
    have h83 : (2/x)^3 = 8/x^3 := by
      rw [div_pow]
      norm_num
    have h16 : (2:ℝ)*((2/x)^3) = 16/x^3 := by
      rw [h83]
      ring
    linarith [hLP, hcub, h16]
  -- Q bound
  have hQ : |(-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))/(8*x)| ≤ 8/x^3 := by
    have e : |(-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))/(8*x)|
        = |-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV)|/(8*x) := by
      rw [abs_div, abs_of_pos h8x]
    rw [e]
    have h2 : |-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV)|/(8*x)
        ≤ (57/x^2)/(8*x) :=
      div_le_div_of_nonneg_right hrho (by linarith : (0:ℝ) ≤ 8*x)
    have h3 : (57/x^2)/(8*x) = 57/(8*x^3) := by
      field_simp
    have h4 : (57:ℝ)/(8*x^3) ≤ 8/x^3 := by
      have e4 : (57:ℝ)/(8*x^3) = (57/8)*(1/x^3) := by ring
      have e5 : (8:ℝ)/x^3 = 8*(1/x^3) := by ring
      rw [e4, e5]
      apply mul_le_mul_of_nonneg_right _ hpos3
      norm_num
    rw [h3] at h2
    linarith [h2, h4]
  -- S bound
  have hS2 : |-(((-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))^2)/2)|
      ≤ 1625/x^3 := by
    have e : |-(((-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))^2)/2)|
        = (((-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))^2)/2) := by
      rw [abs_neg]
      apply abs_of_nonneg
      positivity
    rw [e]
    have hsq : (-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))^2
        ≤ (57/x^2)^2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) hrho 2
      rwa [sq_abs] at h
    have h4 : (57/x^2)^2 = 3249/x^4 := by
      field_simp
      ring
    have h5 : (3249:ℝ)/x^4 ≤ 3249/x^3 := by
      calc 3249/x^4 = 3249*(1/x^4) := by ring
        _ ≤ 3249*(1/x^3) := mul_le_mul_of_nonneg_left r43 (by norm_num)
        _ = 3249/x^3 := by ring
    have h6 : ((-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))^2)/2
        ≤ 1625/x^3 := by
      have e6 : (3249:ℝ)/x^3/2 = 3249/(2*x^3) := by ring
      have e7 : (1625:ℝ)/x^3 = 1625*(1/x^3) := by ring
      have e8 : (3249:ℝ)/(2*x^3) = (3249/2)*(1/x^3) := by ring
      have g : ((-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))^2)/2
          ≤ (3249/x^4)/2 := by
        linarith [hsq]
      have h65 : (3249/2:ℝ)*(1/x^3) ≤ 1625*(1/x^3) :=
        mul_le_mul_of_nonneg_right (by norm_num) hpos3
      linarith [g, h5, e6, e7, e8, h65]
    exact h6
  -- algebraic splitting identity (no logs)
  have hid0 : -(-1/(8*x) - 1/(16*x^2))
      = (15/(64*x^3) + 7/(256*x^4) - errV)
        + ((-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))/(8*x))
        + (-(((-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))^2)/2))
        - ((((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1))
        + ((((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1)^2/2) := by
    field_simp
    ring
  -- assemble
  rw [hStsum, Real.norm_eq_abs]
  have h13 : (0:ℝ) < 1/x^3 := one_div_pos.mpr h3pos
  have hnorm : ‖(1:ℝ)/x^3‖ = 1/x^3 := by
    rw [Real.norm_eq_abs, abs_of_pos h13]
  rw [hnorm]
  have eC : (1705:ℝ)*(1/x^3) = 1705/x^3 := by ring
  rw [eC]
  have herr_eq : Real.log (Real.exp x * (Real.sqrt x *
      ((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV)))
      - (x + 1 / 2 * Real.log x - 1 / (8 * x) - 1 / (16 * x ^ 2))
      = (Real.log ((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV)
        - (-1/(8*x) - 1/(16*x^2))) := by
    rw [hlog]
    ring
  rw [herr_eq]
  have hsplit : (Real.log ((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV)
      - (-1/(8*x) - 1/(16*x^2)))
      = (Real.log ((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV)
        - ((((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1))
        + ((((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1)^2/2))
        + ((15/(64*x^3) + 7/(256*x^4) - errV)
          + ((-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))/(8*x))
          + (-(((-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))^2)/2))) := by
    linarith [hid0]
  rw [hsplit]
  have h1 := abs_add_le
    (Real.log ((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV)
      - ((((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1))
      + ((((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1)^2/2))
    ((15/(64*x^3) + 7/(256*x^4) - errV)
      + ((-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))/(8*x))
      + (-(((-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))^2)/2)))
  have h2 := abs_add_le
    ((15/(64*x^3) + 7/(256*x^4) - errV)
      + ((-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))/(8*x)))
    (-(((-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))^2)/2))
  have h3 := abs_add_le
    (15/(64*x^3) + 7/(256*x^4) - errV)
    ((-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))/(8*x))
  have htri := le_trans h1 (add_le_add le_rfl (le_trans h2 (add_le_add h3 le_rfl)))
  have hfin : |(Real.log ((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV)
      - ((((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1))
      + ((((1 - 1/(8*x) - 7/(128*x^2) + 15/(64*x^3) + 7/(256*x^4)) - errV) - 1)^2/2))
      + ((15/(64*x^3) + 7/(256*x^4) - errV)
        + ((-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))/(8*x))
        + (-(((-7/(128*x^2) + (15/(64*x^3) + 7/(256*x^4) - errV))^2)/2)))|
      ≤ 1705/x^3 := by
    have e : (16:ℝ)/x^3 + ((56/x^3 + 8/x^3) + 1625/x^3) = 1705/x^3 := by ring
    have s1 := add_le_add hR (add_le_add (add_le_add heta hQ) hS2)
    have s2 := le_trans htri s1
    rwa [e] at s2
  exact hfin

end Aux

/-- **Logarithmic asymptotics of the square-root Poisson series.** For real $x$ let
$S(x) = \sum_{k=1}^{\infty} x^k \sqrt{k} / k!$. Then, as $x \to \infty$,
$$\log S(x) = x + \tfrac{1}{2} \log x - \frac{1}{8x} - \frac{1}{16 x^2} + O\left(x^{-3}\right).$$

Proves `Wanted` entry `ramanujan_part1_ch3_entry10_example1_sqrt_poisson_asymptotic`.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 10, Example 1, printed p.
    64 / PDF p. 74.
-/
theorem ramanujan_part1_ch3_entry10_example1_sqrt_poisson_asymptotic :
    (fun x : ℝ =>
        Real.log (∑' (j : ℕ), x ^ (j + 1) * Real.sqrt (↑(j + 1) : ℝ) /
            (↑(Nat.factorial (j + 1)) : ℝ)) - (x + (1 / 2 : ℝ) * Real.log x - 1 / (8 * x) - 1 /
                (16 * x ^ 2))) =O[Filter.atTop] (fun x : ℝ =>
            1 / x ^ 3) := by
  apply Asymptotics.IsBigO.of_bound 1705
  filter_upwards [Filter.eventually_ge_atTop 8] with x hx
  show ‖Real.log (∑' (j : ℕ), x ^ (j + 1) * Real.sqrt (↑(j + 1) : ℝ) /
      (↑(Nat.factorial (j + 1)) : ℝ))
    - (x + 1 / 2 * Real.log x - 1 / (8 * x) - 1 / (16 * x ^ 2))‖
    ≤ 1705 * ‖(1 : ℝ)/x^3‖
  obtain ⟨errV, herr, herr_nn, herr_le⟩ := Aux.errExists x (by linarith)
  have hxp : (0:ℝ) < x := by linarith
  have hS := Aux.SHasSum x hxp errV herr
  have hStsum := hS.tsum_eq
  exact Aux.finalBound x errV hx herr_nn herr_le hStsum

end Entry10Example1SqrtPoissonAsymptotic
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
