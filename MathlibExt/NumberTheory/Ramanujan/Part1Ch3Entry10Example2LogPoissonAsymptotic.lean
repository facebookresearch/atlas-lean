/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10Example2LogPoissonAsymptotic

/-- Pointwise log bound used to dominate the Poisson-log series by the exp series. -/
private theorem log_add_two_le (j : ℕ) : Real.log ((j : ℝ) + 2) ≤ ((j : ℝ) + 1) := by
  have hpos : (0 : ℝ) < (j : ℝ) + 2 := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

/-- The Poisson-log series is summable for positive `x` (comparison with the exp series). -/
private theorem summable_log_poisson {x : ℝ} (hx : 0 < x) :
    Summable (fun j : ℕ => x ^ (j + 1) * Real.log ((j : ℝ) + 2) / (Nat.factorial (j + 1) : ℝ)) := by
  have hnn : ∀ j : ℕ,
      0 ≤ x ^ (j + 1) * Real.log ((j : ℝ) + 2) / (Nat.factorial (j + 1) : ℝ) := by
    intro j
    apply div_nonneg
    · apply mul_nonneg (pow_nonneg hx.le _)
      have h2 : (2 : ℝ) ≤ (j : ℝ) + 2 := by
        have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2
      have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    · exact Nat.cast_nonneg _
  have hsum : Summable (fun j : ℕ => x ^ (j + 1) / (Nat.factorial j : ℝ)) := by
    have h := (Real.summable_pow_div_factorial x).mul_left x
    refine h.congr fun j => ?_
    rw [pow_succ]
    ring
  have hmaj : ∀ j : ℕ,
      x ^ (j + 1) * Real.log ((j : ℝ) + 2) / (Nat.factorial (j + 1) : ℝ)
        ≤ x ^ (j + 1) / (Nat.factorial j : ℝ) := by
    intro j
    have hlog := log_add_two_le j
    have hfact : (Nat.factorial (j + 1) : ℝ) = ((j : ℝ) + 1) * (Nat.factorial j : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hFpos : (0 : ℝ) < (Nat.factorial j : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos j)
    have hj1pos : (0 : ℝ) < (j : ℝ) + 1 := by
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hbase : (0 : ℝ) ≤ x ^ (j + 1) / (Nat.factorial j : ℝ) :=
      div_nonneg (pow_nonneg hx.le _) hFpos.le
    have hfrac : Real.log ((j : ℝ) + 2) / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hj1pos]
      exact hlog
    have heq : x ^ (j + 1) * Real.log ((j : ℝ) + 2) / (Nat.factorial (j + 1) : ℝ)
        = (x ^ (j + 1) / (Nat.factorial j : ℝ)) * (Real.log ((j : ℝ) + 2) / ((j : ℝ) + 1)) := by
      rw [hfact, div_mul_div_comm, mul_comm ((Nat.factorial j : ℝ)) _]
    rw [heq]
    calc (x ^ (j + 1) / (Nat.factorial j : ℝ)) * (Real.log ((j : ℝ) + 2) / ((j : ℝ) + 1))
        ≤ (x ^ (j + 1) / (Nat.factorial j : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hfrac hbase
      _ = x ^ (j + 1) / (Nat.factorial j : ℝ) := mul_one _
  exact Summable.of_nonneg_of_le hnn hmaj hsum

/-- Hence the `HasSum` witness required by the main statement exists for every `x > 0`. -/
private theorem hasSum_log_poisson {x : ℝ} (hx : 0 < x) :
    ∃ S : ℝ,
      HasSum (fun j : ℕ => x ^ (j + 1) * Real.log ((j : ℝ) + 2) / (Nat.factorial (j + 1) : ℝ)) S :=
  ⟨_, (summable_log_poisson hx).hasSum⟩

/-- Poisson normalization as a real `HasSum`: for `x ≥ 0` the Poisson weights sum to 1.
This is the probabilistic reading of the series (via `hasSum_one_poissonMeasure`); the
factorial-moment identities needed for the `O(x⁻³)` bound are obtained by shifting this. -/
private theorem poisson_hasSum_one {x : ℝ} (hx : 0 ≤ x) :
    HasSum (fun k : ℕ => Real.exp (-x) * x ^ k / (Nat.factorial k : ℝ)) 1 := by
  obtain ⟨r, rfl⟩ : ∃ r : NNReal, (r : ℝ) = x := ⟨⟨x, hx⟩, NNReal.coe_mk x hx⟩
  exact ProbabilityTheory.hasSum_one_poissonMeasure r

/-- Poisson weight: `w x M = e ^ (-x) * x ^ M / M !`. -/
private noncomputable def w (x : ℝ) (M : ℕ) : ℝ :=
  Real.exp (-x) * x ^ M / (Nat.factorial M : ℝ)

private theorem w_nonneg {x : ℝ} (hx : 0 ≤ x) (M : ℕ) : 0 ≤ w x M := by
  unfold w
  exact div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hx _)) (Nat.cast_nonneg _)

private theorem w_hasSum {x : ℝ} (hx : 0 ≤ x) : HasSum (fun M => w x M) 1 :=
  poisson_hasSum_one hx

/-- The index-shift identity for Poisson weights: `w (K+1) * (K+1) = x * w K`. -/
private theorem w_shift {x : ℝ} (hx : 0 < x) (K : ℕ) :
    w x (K + 1) * ((K : ℝ) + 1) = x * w x K := by
  have hF : (Nat.factorial K : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.factorial_pos K))
  have hK : ((K : ℝ) + 1) ≠ 0 := by
    have h0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    positivity
  have hF' : (((K : ℝ) + 1) * (Nat.factorial K : ℝ)) ≠ 0 := mul_ne_zero hK hF
  simp only [w]
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  field_simp

/-- Shift a `HasSum` over `ℕ` forward by one when the head term vanishes. -/
private theorem HasSum_shift_succ {f : ℕ → ℝ} {a : ℝ} (hf : HasSum f a)
    (h0 : f 0 = 0) : HasSum (fun K => f (K + 1)) a := by
  have h := (hasSum_nat_add_iff' (f := f) 1).mpr hf
  rwa [Finset.sum_range_one, h0, sub_zero] at h

/-- Recover a `HasSum` from its one-step shift when the head term vanishes. -/
private theorem HasSum_of_shift_succ {f : ℕ → ℝ} {b : ℝ}
    (hf : HasSum (fun K => f (K + 1)) b) (h0 : f 0 = 0) : HasSum f b := by
  have h2 : HasSum (fun K => f (K + 1)) (b - ∑ i ∈ Finset.range 1, f i) := by
    rwa [Finset.sum_range_one, h0, sub_zero]
  exact (hasSum_nat_add_iff' (f := f) 1).mp h2

/-- Raw Poisson moment 0. -/
private theorem rho0 {x : ℝ} (hx : 0 ≤ x) :
    HasSum (fun M => w x M * (M : ℝ) ^ 0) 1 :=
  (w_hasSum hx).congr_fun (fun M => by ring)

/-- Raw Poisson moment 1. -/
private theorem rho1 {x : ℝ} (hx : 0 < x) (H0 : HasSum (fun M => w x M * (M : ℝ) ^ 0) 1) :
    HasSum (fun M => w x M * (M : ℝ) ^ 1) x := by
  have hcombo : HasSum (fun K => x * (w x K * (K : ℝ) ^ 0)) (x * 1) := H0.mul_left x
  have hshift : HasSum (fun K => w x (K + 1) * (((K + 1 : ℕ)) : ℝ) ^ 1) (x * 1) := by
    apply hcombo.congr_fun
    intro K
    have e1 := w_shift hx K
    simp only [Nat.cast_add, Nat.cast_one]
    calc w x (K + 1) * ((K : ℝ) + 1) ^ 1
        = w x (K + 1) * ((K : ℝ) + 1) := by ring
      _ = x * w x K := e1
      _ = x * (w x K * (K : ℝ) ^ 0) := by ring
  have h0 : (fun M => w x M * (M : ℝ) ^ 1) 0 = 0 := by simp
  have h := HasSum_of_shift_succ (f := fun M => w x M * (M : ℝ) ^ 1) hshift h0
  have hval : x * 1 = x := by ring
  rwa [hval] at h

/-- Raw Poisson moment 2. -/
private theorem rho2 {x : ℝ} (hx : 0 < x) (H0 : HasSum (fun M => w x M * (M : ℝ) ^ 0) 1)
    (H1 : HasSum (fun M => w x M * (M : ℝ) ^ 1) x) :
    HasSum (fun M => w x M * (M : ℝ) ^ 2) (x ^ 2 + x) := by
  have hcombo : HasSum (fun K => x * (w x K * (K : ℝ) ^ 1) + x * (w x K * (K : ℝ) ^ 0))
      (x * x + x * 1) := (H1.mul_left x).add (H0.mul_left x)
  have hshift : HasSum (fun K => w x (K + 1) * (((K + 1 : ℕ)) : ℝ) ^ 2) (x * x + x * 1) := by
    apply hcombo.congr_fun
    intro K
    have e1 := w_shift hx K
    simp only [Nat.cast_add, Nat.cast_one]
    calc w x (K + 1) * ((K : ℝ) + 1) ^ 2
        = (w x (K + 1) * ((K : ℝ) + 1)) * ((K : ℝ) + 1) := by ring
      _ = (x * w x K) * ((K : ℝ) + 1) := by rw [e1]
      _ = x * (w x K * (K : ℝ) ^ 1) + x * (w x K * (K : ℝ) ^ 0) := by ring
  have h0 : (fun M => w x M * (M : ℝ) ^ 2) 0 = 0 := by simp
  have h := HasSum_of_shift_succ (f := fun M => w x M * (M : ℝ) ^ 2) hshift h0
  have hval : x * x + x * 1 = x ^ 2 + x := by ring
  rwa [hval] at h

/-- Raw Poisson moment 3. -/
private theorem rho3 {x : ℝ} (hx : 0 < x) (H0 : HasSum (fun M => w x M * (M : ℝ) ^ 0) 1)
    (H1 : HasSum (fun M => w x M * (M : ℝ) ^ 1) x)
    (H2 : HasSum (fun M => w x M * (M : ℝ) ^ 2) (x ^ 2 + x)) :
    HasSum (fun M => w x M * (M : ℝ) ^ 3) (x ^ 3 + 3 * x ^ 2 + x) := by
  have hcombo : HasSum (fun K => x * (w x K * (K : ℝ) ^ 2) + (x * 2) * (w x K * (K : ℝ) ^ 1)
      + x * (w x K * (K : ℝ) ^ 0))
      ((x * (x ^ 2 + x) + (x * 2) * x) + x * 1) :=
    ((H2.mul_left x).add (H1.mul_left (x * 2))).add (H0.mul_left x)
  have hshift : HasSum (fun K => w x (K + 1) * (((K + 1 : ℕ)) : ℝ) ^ 3)
      ((x * (x ^ 2 + x) + (x * 2) * x) + x * 1) := by
    apply hcombo.congr_fun
    intro K
    have e1 := w_shift hx K
    simp only [Nat.cast_add, Nat.cast_one]
    calc w x (K + 1) * ((K : ℝ) + 1) ^ 3
        = (w x (K + 1) * ((K : ℝ) + 1)) * ((K : ℝ) + 1) ^ 2 := by ring
      _ = (x * w x K) * ((K : ℝ) + 1) ^ 2 := by rw [e1]
      _ = x * (w x K * (K : ℝ) ^ 2) + (x * 2) * (w x K * (K : ℝ) ^ 1)
          + x * (w x K * (K : ℝ) ^ 0) := by ring
  have h0 : (fun M => w x M * (M : ℝ) ^ 3) 0 = 0 := by simp
  have h := HasSum_of_shift_succ (f := fun M => w x M * (M : ℝ) ^ 3) hshift h0
  have hval : (x * (x ^ 2 + x) + (x * 2) * x) + x * 1 = x ^ 3 + 3 * x ^ 2 + x := by ring
  rwa [hval] at h

/-- Raw Poisson moment 4. -/
private theorem rho4 {x : ℝ} (hx : 0 < x) (H0 : HasSum (fun M => w x M * (M : ℝ) ^ 0) 1)
    (H1 : HasSum (fun M => w x M * (M : ℝ) ^ 1) x)
    (H2 : HasSum (fun M => w x M * (M : ℝ) ^ 2) (x ^ 2 + x))
    (H3 : HasSum (fun M => w x M * (M : ℝ) ^ 3) (x ^ 3 + 3 * x ^ 2 + x)) :
    HasSum (fun M => w x M * (M : ℝ) ^ 4) (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x) := by
  have hcombo : HasSum (fun K => x * (w x K * (K : ℝ) ^ 3) + (x * 3) * (w x K * (K : ℝ) ^ 2)
      + (x * 3) * (w x K * (K : ℝ) ^ 1) + x * (w x K * (K : ℝ) ^ 0))
      (((x * (x ^ 3 + 3 * x ^ 2 + x) + (x * 3) * (x ^ 2 + x)) + (x * 3) * x) + x * 1) :=
    (((H3.mul_left x).add (H2.mul_left (x * 3))).add (H1.mul_left (x * 3))).add
      (H0.mul_left x)
  have hshift : HasSum (fun K => w x (K + 1) * (((K + 1 : ℕ)) : ℝ) ^ 4)
      (((x * (x ^ 3 + 3 * x ^ 2 + x) + (x * 3) * (x ^ 2 + x)) + (x * 3) * x) + x * 1) := by
    apply hcombo.congr_fun
    intro K
    have e1 := w_shift hx K
    simp only [Nat.cast_add, Nat.cast_one]
    calc w x (K + 1) * ((K : ℝ) + 1) ^ 4
        = (w x (K + 1) * ((K : ℝ) + 1)) * ((K : ℝ) + 1) ^ 3 := by ring
      _ = (x * w x K) * ((K : ℝ) + 1) ^ 3 := by rw [e1]
      _ = x * (w x K * (K : ℝ) ^ 3) + (x * 3) * (w x K * (K : ℝ) ^ 2)
          + (x * 3) * (w x K * (K : ℝ) ^ 1) + x * (w x K * (K : ℝ) ^ 0) := by ring
  have h0 : (fun M => w x M * (M : ℝ) ^ 4) 0 = 0 := by simp
  have h := HasSum_of_shift_succ (f := fun M => w x M * (M : ℝ) ^ 4) hshift h0
  have hval : ((x * (x ^ 3 + 3 * x ^ 2 + x) + (x * 3) * (x ^ 2 + x)) + (x * 3) * x) + x * 1
      = x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x := by ring
  rwa [hval] at h

/-- Raw Poisson moment 5. -/
private theorem rho5 {x : ℝ} (hx : 0 < x) (H0 : HasSum (fun M => w x M * (M : ℝ) ^ 0) 1)
    (H1 : HasSum (fun M => w x M * (M : ℝ) ^ 1) x)
    (H2 : HasSum (fun M => w x M * (M : ℝ) ^ 2) (x ^ 2 + x))
    (H3 : HasSum (fun M => w x M * (M : ℝ) ^ 3) (x ^ 3 + 3 * x ^ 2 + x))
    (H4 : HasSum (fun M => w x M * (M : ℝ) ^ 4) (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x)) :
    HasSum (fun M => w x M * (M : ℝ) ^ 5)
      (x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x) := by
  have hcombo : HasSum (fun K => x * (w x K * (K : ℝ) ^ 4) + (x * 4) * (w x K * (K : ℝ) ^ 3)
      + (x * 6) * (w x K * (K : ℝ) ^ 2) + (x * 4) * (w x K * (K : ℝ) ^ 1)
      + x * (w x K * (K : ℝ) ^ 0))
      ((((x * (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x) + (x * 4) * (x ^ 3 + 3 * x ^ 2 + x))
        + (x * 6) * (x ^ 2 + x)) + (x * 4) * x) + x * 1) :=
    ((((H4.mul_left x).add (H3.mul_left (x * 4))).add (H2.mul_left (x * 6))).add
      (H1.mul_left (x * 4))).add (H0.mul_left x)
  have hshift : HasSum (fun K => w x (K + 1) * (((K + 1 : ℕ)) : ℝ) ^ 5)
      ((((x * (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x) + (x * 4) * (x ^ 3 + 3 * x ^ 2 + x))
        + (x * 6) * (x ^ 2 + x)) + (x * 4) * x) + x * 1) := by
    apply hcombo.congr_fun
    intro K
    have e1 := w_shift hx K
    simp only [Nat.cast_add, Nat.cast_one]
    calc w x (K + 1) * ((K : ℝ) + 1) ^ 5
        = (w x (K + 1) * ((K : ℝ) + 1)) * ((K : ℝ) + 1) ^ 4 := by ring
      _ = (x * w x K) * ((K : ℝ) + 1) ^ 4 := by rw [e1]
      _ = x * (w x K * (K : ℝ) ^ 4) + (x * 4) * (w x K * (K : ℝ) ^ 3)
          + (x * 6) * (w x K * (K : ℝ) ^ 2) + (x * 4) * (w x K * (K : ℝ) ^ 1)
          + x * (w x K * (K : ℝ) ^ 0) := by ring
  have h0 : (fun M => w x M * (M : ℝ) ^ 5) 0 = 0 := by simp
  have h := HasSum_of_shift_succ (f := fun M => w x M * (M : ℝ) ^ 5) hshift h0
  have hval : ((((x * (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x) + (x * 4) * (x ^ 3 + 3 * x ^ 2 + x))
      + (x * 6) * (x ^ 2 + x)) + (x * 4) * x) + x * 1)
      = x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x := by ring
  rwa [hval] at h

/-- Raw Poisson moment 6. -/
private theorem rho6 {x : ℝ} (hx : 0 < x) (H0 : HasSum (fun M => w x M * (M : ℝ) ^ 0) 1)
    (H1 : HasSum (fun M => w x M * (M : ℝ) ^ 1) x)
    (H2 : HasSum (fun M => w x M * (M : ℝ) ^ 2) (x ^ 2 + x))
    (H3 : HasSum (fun M => w x M * (M : ℝ) ^ 3) (x ^ 3 + 3 * x ^ 2 + x))
    (H4 : HasSum (fun M => w x M * (M : ℝ) ^ 4) (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x))
    (H5 : HasSum (fun M => w x M * (M : ℝ) ^ 5)
      (x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x)) :
    HasSum (fun M => w x M * (M : ℝ) ^ 6)
      (x ^ 6 + 15 * x ^ 5 + 65 * x ^ 4 + 90 * x ^ 3 + 31 * x ^ 2 + x) := by
  have hcombo : HasSum (fun K => x * (w x K * (K : ℝ) ^ 5) + (x * 5) * (w x K * (K : ℝ) ^ 4)
      + (x * 10) * (w x K * (K : ℝ) ^ 3) + (x * 10) * (w x K * (K : ℝ) ^ 2)
      + (x * 5) * (w x K * (K : ℝ) ^ 1) + x * (w x K * (K : ℝ) ^ 0))
      (((((x * (x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x)
        + (x * 5) * (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x))
        + (x * 10) * (x ^ 3 + 3 * x ^ 2 + x)) + (x * 10) * (x ^ 2 + x)) + (x * 5) * x)
        + x * 1) :=
    (((((H5.mul_left x).add (H4.mul_left (x * 5))).add (H3.mul_left (x * 10))).add
      (H2.mul_left (x * 10))).add (H1.mul_left (x * 5))).add (H0.mul_left x)
  have hshift : HasSum (fun K => w x (K + 1) * (((K + 1 : ℕ)) : ℝ) ^ 6)
      (((((x * (x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x)
        + (x * 5) * (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x))
        + (x * 10) * (x ^ 3 + 3 * x ^ 2 + x)) + (x * 10) * (x ^ 2 + x)) + (x * 5) * x)
        + x * 1) := by
    apply hcombo.congr_fun
    intro K
    have e1 := w_shift hx K
    simp only [Nat.cast_add, Nat.cast_one]
    calc w x (K + 1) * ((K : ℝ) + 1) ^ 6
        = (w x (K + 1) * ((K : ℝ) + 1)) * ((K : ℝ) + 1) ^ 5 := by ring
      _ = (x * w x K) * ((K : ℝ) + 1) ^ 5 := by rw [e1]
      _ = x * (w x K * (K : ℝ) ^ 5) + (x * 5) * (w x K * (K : ℝ) ^ 4)
          + (x * 10) * (w x K * (K : ℝ) ^ 3) + (x * 10) * (w x K * (K : ℝ) ^ 2)
          + (x * 5) * (w x K * (K : ℝ) ^ 1) + x * (w x K * (K : ℝ) ^ 0) := by ring
  have h0 : (fun M => w x M * (M : ℝ) ^ 6) 0 = 0 := by simp
  have h := HasSum_of_shift_succ (f := fun M => w x M * (M : ℝ) ^ 6) hshift h0
  have hval : (((((x * (x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x)
      + (x * 5) * (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x))
      + (x * 10) * (x ^ 3 + 3 * x ^ 2 + x)) + (x * 10) * (x ^ 2 + x)) + (x * 5) * x)
      + x * 1)
      = x ^ 6 + 15 * x ^ 5 + 65 * x ^ 4 + 90 * x ^ 3 + 31 * x ^ 2 + x := by ring
  rwa [hval] at h

/-- Centered moment `ν₁` of `M + 1 - x`. -/
private theorem nu1 {x : ℝ} (H0 : HasSum (fun M => w x M * (M : ℝ) ^ 0) 1)
    (H1 : HasSum (fun M => w x M * (M : ℝ) ^ 1) x) :
    HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 1) 1 := by
  have hcombo : HasSum (fun M => w x M * (M : ℝ) ^ 1 + (1 - x) * (w x M * (M : ℝ) ^ 0))
      (x + (1 - x) * 1) := H1.add (H0.mul_left (1 - x))
  have h : HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 1) (x + (1 - x) * 1) :=
    hcombo.congr_fun (fun M => by ring)
  have hval : x + (1 - x) * 1 = 1 := by ring
  rwa [hval] at h

/-- Centered moment `ν₂` of `M + 1 - x`. -/
private theorem nu2 {x : ℝ} (H0 : HasSum (fun M => w x M * (M : ℝ) ^ 0) 1)
    (H1 : HasSum (fun M => w x M * (M : ℝ) ^ 1) x)
    (H2 : HasSum (fun M => w x M * (M : ℝ) ^ 2) (x ^ 2 + x)) :
    HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 2) (x + 1) := by
  have hcombo : HasSum (fun M => w x M * (M : ℝ) ^ 2 + (2 * (1 - x)) * (w x M * (M : ℝ) ^ 1)
      + (1 - x) ^ 2 * (w x M * (M : ℝ) ^ 0))
      (((x ^ 2 + x) + (2 * (1 - x)) * x) + (1 - x) ^ 2 * 1) :=
    (H2.add (H1.mul_left (2 * (1 - x)))).add (H0.mul_left ((1 - x) ^ 2))
  have h : HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 2)
      (((x ^ 2 + x) + (2 * (1 - x)) * x) + (1 - x) ^ 2 * 1) :=
    hcombo.congr_fun (fun M => by ring)
  have hval : ((x ^ 2 + x) + (2 * (1 - x)) * x) + (1 - x) ^ 2 * 1 = x + 1 := by ring
  rwa [hval] at h

/-- Centered moment `ν₃` of `M + 1 - x`. -/
private theorem nu3 {x : ℝ} (H0 : HasSum (fun M => w x M * (M : ℝ) ^ 0) 1)
    (H1 : HasSum (fun M => w x M * (M : ℝ) ^ 1) x)
    (H2 : HasSum (fun M => w x M * (M : ℝ) ^ 2) (x ^ 2 + x))
    (H3 : HasSum (fun M => w x M * (M : ℝ) ^ 3) (x ^ 3 + 3 * x ^ 2 + x)) :
    HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 3) (4 * x + 1) := by
  have hcombo : HasSum (fun M => w x M * (M : ℝ) ^ 3 + (3 * (1 - x)) * (w x M * (M : ℝ) ^ 2)
      + (3 * (1 - x) ^ 2) * (w x M * (M : ℝ) ^ 1) + (1 - x) ^ 3 * (w x M * (M : ℝ) ^ 0))
      ((((x ^ 3 + 3 * x ^ 2 + x) + (3 * (1 - x)) * (x ^ 2 + x))
        + (3 * (1 - x) ^ 2) * x) + (1 - x) ^ 3 * 1) :=
    ((H3.add (H2.mul_left (3 * (1 - x)))).add (H1.mul_left (3 * (1 - x) ^ 2))).add
      (H0.mul_left ((1 - x) ^ 3))
  have h : HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 3)
      ((((x ^ 3 + 3 * x ^ 2 + x) + (3 * (1 - x)) * (x ^ 2 + x))
        + (3 * (1 - x) ^ 2) * x) + (1 - x) ^ 3 * 1) :=
    hcombo.congr_fun (fun M => by ring)
  have hval : (((x ^ 3 + 3 * x ^ 2 + x) + (3 * (1 - x)) * (x ^ 2 + x))
      + (3 * (1 - x) ^ 2) * x) + (1 - x) ^ 3 * 1 = 4 * x + 1 := by ring
  rwa [hval] at h

/-- Centered moment `ν₄` of `M + 1 - x`. -/
private theorem nu4 {x : ℝ} (H0 : HasSum (fun M => w x M * (M : ℝ) ^ 0) 1)
    (H1 : HasSum (fun M => w x M * (M : ℝ) ^ 1) x)
    (H2 : HasSum (fun M => w x M * (M : ℝ) ^ 2) (x ^ 2 + x))
    (H3 : HasSum (fun M => w x M * (M : ℝ) ^ 3) (x ^ 3 + 3 * x ^ 2 + x))
    (H4 : HasSum (fun M => w x M * (M : ℝ) ^ 4) (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x)) :
    HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 4) (3 * x ^ 2 + 11 * x + 1) := by
  have hcombo : HasSum (fun M => w x M * (M : ℝ) ^ 4
      + (4 * (1 - x)) * (w x M * (M : ℝ) ^ 3) + (6 * (1 - x) ^ 2) * (w x M * (M : ℝ) ^ 2)
      + (4 * (1 - x) ^ 3) * (w x M * (M : ℝ) ^ 1) + (1 - x) ^ 4 * (w x M * (M : ℝ) ^ 0))
      (((((x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x) + 4 * (1 - x) * (x ^ 3 + 3 * x ^ 2 + x))
        + 6 * (1 - x) ^ 2 * (x ^ 2 + x)) + 4 * (1 - x) ^ 3 * x) + (1 - x) ^ 4 * 1) :=
    (((H4.add (H3.mul_left (4 * (1 - x)))).add (H2.mul_left (6 * (1 - x) ^ 2))).add
      (H1.mul_left (4 * (1 - x) ^ 3))).add (H0.mul_left ((1 - x) ^ 4))
  have h : HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 4)
      (((((x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x) + 4 * (1 - x) * (x ^ 3 + 3 * x ^ 2 + x))
        + 6 * (1 - x) ^ 2 * (x ^ 2 + x)) + 4 * (1 - x) ^ 3 * x) + (1 - x) ^ 4 * 1) :=
    hcombo.congr_fun (fun M => by ring)
  have hval : (((((x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x)
      + 4 * (1 - x) * (x ^ 3 + 3 * x ^ 2 + x)) + 6 * (1 - x) ^ 2 * (x ^ 2 + x))
      + 4 * (1 - x) ^ 3 * x) + (1 - x) ^ 4 * 1)
      = 3 * x ^ 2 + 11 * x + 1 := by ring
  rwa [hval] at h

/-- Centered moment `ν₅` of `M + 1 - x`. -/
private theorem nu5 {x : ℝ} (H0 : HasSum (fun M => w x M * (M : ℝ) ^ 0) 1)
    (H1 : HasSum (fun M => w x M * (M : ℝ) ^ 1) x)
    (H2 : HasSum (fun M => w x M * (M : ℝ) ^ 2) (x ^ 2 + x))
    (H3 : HasSum (fun M => w x M * (M : ℝ) ^ 3) (x ^ 3 + 3 * x ^ 2 + x))
    (H4 : HasSum (fun M => w x M * (M : ℝ) ^ 4) (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x))
    (H5 : HasSum (fun M => w x M * (M : ℝ) ^ 5)
      (x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x)) :
    HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 5) (25 * x ^ 2 + 26 * x + 1) := by
  have hcombo : HasSum (fun M => w x M * (M : ℝ) ^ 5
      + (5 * (1 - x)) * (w x M * (M : ℝ) ^ 4) + (10 * (1 - x) ^ 2) * (w x M * (M : ℝ) ^ 3)
      + (10 * (1 - x) ^ 3) * (w x M * (M : ℝ) ^ 2) + (5 * (1 - x) ^ 4) * (w x M * (M : ℝ) ^ 1)
      + (1 - x) ^ 5 * (w x M * (M : ℝ) ^ 0))
      ((((((x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x)
        + 5 * (1 - x) * (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x))
        + 10 * (1 - x) ^ 2 * (x ^ 3 + 3 * x ^ 2 + x)) + 10 * (1 - x) ^ 3 * (x ^ 2 + x))
        + 5 * (1 - x) ^ 4 * x) + (1 - x) ^ 5 * 1) :=
    ((((H5.add (H4.mul_left (5 * (1 - x)))).add (H3.mul_left (10 * (1 - x) ^ 2))).add
      (H2.mul_left (10 * (1 - x) ^ 3))).add (H1.mul_left (5 * (1 - x) ^ 4))).add
      (H0.mul_left ((1 - x) ^ 5))
  have h : HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 5)
      ((((((x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x)
        + 5 * (1 - x) * (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x))
        + 10 * (1 - x) ^ 2 * (x ^ 3 + 3 * x ^ 2 + x)) + 10 * (1 - x) ^ 3 * (x ^ 2 + x))
        + 5 * (1 - x) ^ 4 * x) + (1 - x) ^ 5 * 1) :=
    hcombo.congr_fun (fun M => by ring)
  have hval : ((((((x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x)
      + 5 * (1 - x) * (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x))
      + 10 * (1 - x) ^ 2 * (x ^ 3 + 3 * x ^ 2 + x)) + 10 * (1 - x) ^ 3 * (x ^ 2 + x))
      + 5 * (1 - x) ^ 4 * x) + (1 - x) ^ 5 * 1)
      = 25 * x ^ 2 + 26 * x + 1 := by ring
  rwa [hval] at h

/-- Centered moment `ν₆` of `M + 1 - x`. -/
private theorem nu6 {x : ℝ} (H0 : HasSum (fun M => w x M * (M : ℝ) ^ 0) 1)
    (H1 : HasSum (fun M => w x M * (M : ℝ) ^ 1) x)
    (H2 : HasSum (fun M => w x M * (M : ℝ) ^ 2) (x ^ 2 + x))
    (H3 : HasSum (fun M => w x M * (M : ℝ) ^ 3) (x ^ 3 + 3 * x ^ 2 + x))
    (H4 : HasSum (fun M => w x M * (M : ℝ) ^ 4) (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x))
    (H5 : HasSum (fun M => w x M * (M : ℝ) ^ 5)
      (x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x))
    (H6 : HasSum (fun M => w x M * (M : ℝ) ^ 6)
      (x ^ 6 + 15 * x ^ 5 + 65 * x ^ 4 + 90 * x ^ 3 + 31 * x ^ 2 + x)) :
    HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 6)
      (15 * x ^ 3 + 130 * x ^ 2 + 57 * x + 1) := by
  have hcombo : HasSum (fun M => w x M * (M : ℝ) ^ 6
      + (6 * (1 - x)) * (w x M * (M : ℝ) ^ 5) + (15 * (1 - x) ^ 2) * (w x M * (M : ℝ) ^ 4)
      + (20 * (1 - x) ^ 3) * (w x M * (M : ℝ) ^ 3)
      + (15 * (1 - x) ^ 4) * (w x M * (M : ℝ) ^ 2)
      + (6 * (1 - x) ^ 5) * (w x M * (M : ℝ) ^ 1) + (1 - x) ^ 6 * (w x M * (M : ℝ) ^ 0))
      (((((((x ^ 6 + 15 * x ^ 5 + 65 * x ^ 4 + 90 * x ^ 3 + 31 * x ^ 2 + x)
        + 6 * (1 - x) * (x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x))
        + 15 * (1 - x) ^ 2 * (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x))
        + 20 * (1 - x) ^ 3 * (x ^ 3 + 3 * x ^ 2 + x)) + 15 * (1 - x) ^ 4 * (x ^ 2 + x))
        + 6 * (1 - x) ^ 5 * x) + (1 - x) ^ 6 * 1) :=
    (((((H6.add (H5.mul_left (6 * (1 - x)))).add (H4.mul_left (15 * (1 - x) ^ 2))).add
      (H3.mul_left (20 * (1 - x) ^ 3))).add (H2.mul_left (15 * (1 - x) ^ 4))).add
      (H1.mul_left (6 * (1 - x) ^ 5))).add (H0.mul_left ((1 - x) ^ 6))
  have h : HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 6)
      (((((((x ^ 6 + 15 * x ^ 5 + 65 * x ^ 4 + 90 * x ^ 3 + 31 * x ^ 2 + x)
        + 6 * (1 - x) * (x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x))
        + 15 * (1 - x) ^ 2 * (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x))
        + 20 * (1 - x) ^ 3 * (x ^ 3 + 3 * x ^ 2 + x)) + 15 * (1 - x) ^ 4 * (x ^ 2 + x))
        + 6 * (1 - x) ^ 5 * x) + (1 - x) ^ 6 * 1) :=
    hcombo.congr_fun (fun M => by ring)
  have hval : (((((((x ^ 6 + 15 * x ^ 5 + 65 * x ^ 4 + 90 * x ^ 3 + 31 * x ^ 2 + x)
      + 6 * (1 - x) * (x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x))
      + 15 * (1 - x) ^ 2 * (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x))
      + 20 * (1 - x) ^ 3 * (x ^ 3 + 3 * x ^ 2 + x)) + 15 * (1 - x) ^ 4 * (x ^ 2 + x))
      + 6 * (1 - x) ^ 5 * x) + (1 - x) ^ 6 * 1)
      = 15 * x ^ 3 + 130 * x ^ 2 + 57 * x + 1 := by ring
  rwa [hval] at h

/-- Central sixth moment `μ₆` of `M - x`. -/
private theorem mu6 {x : ℝ} (H0 : HasSum (fun M => w x M * (M : ℝ) ^ 0) 1)
    (H1 : HasSum (fun M => w x M * (M : ℝ) ^ 1) x)
    (H2 : HasSum (fun M => w x M * (M : ℝ) ^ 2) (x ^ 2 + x))
    (H3 : HasSum (fun M => w x M * (M : ℝ) ^ 3) (x ^ 3 + 3 * x ^ 2 + x))
    (H4 : HasSum (fun M => w x M * (M : ℝ) ^ 4) (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x))
    (H5 : HasSum (fun M => w x M * (M : ℝ) ^ 5)
      (x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x))
    (H6 : HasSum (fun M => w x M * (M : ℝ) ^ 6)
      (x ^ 6 + 15 * x ^ 5 + 65 * x ^ 4 + 90 * x ^ 3 + 31 * x ^ 2 + x)) :
    HasSum (fun M => w x M * ((M : ℝ) - x) ^ 6) (15 * x ^ 3 + 25 * x ^ 2 + x) := by
  have hcombo : HasSum (fun M => w x M * (M : ℝ) ^ 6
      + (-(6 * x)) * (w x M * (M : ℝ) ^ 5) + (15 * x ^ 2) * (w x M * (M : ℝ) ^ 4)
      + (-(20 * x ^ 3)) * (w x M * (M : ℝ) ^ 3) + (15 * x ^ 4) * (w x M * (M : ℝ) ^ 2)
      + (-(6 * x ^ 5)) * (w x M * (M : ℝ) ^ 1) + x ^ 6 * (w x M * (M : ℝ) ^ 0))
      (((((((x ^ 6 + 15 * x ^ 5 + 65 * x ^ 4 + 90 * x ^ 3 + 31 * x ^ 2 + x)
        + -(6 * x) * (x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x))
        + 15 * x ^ 2 * (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x))
        + -(20 * x ^ 3) * (x ^ 3 + 3 * x ^ 2 + x)) + 15 * x ^ 4 * (x ^ 2 + x))
        + -(6 * x ^ 5) * x) + x ^ 6 * 1) :=
    (((((H6.add (H5.mul_left (-(6 * x)))).add (H4.mul_left (15 * x ^ 2))).add
      (H3.mul_left (-(20 * x ^ 3)))).add (H2.mul_left (15 * x ^ 4))).add
      (H1.mul_left (-(6 * x ^ 5)))).add (H0.mul_left (x ^ 6))
  have h : HasSum (fun M => w x M * ((M : ℝ) - x) ^ 6)
      (((((((x ^ 6 + 15 * x ^ 5 + 65 * x ^ 4 + 90 * x ^ 3 + 31 * x ^ 2 + x)
        + -(6 * x) * (x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x))
        + 15 * x ^ 2 * (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x))
        + -(20 * x ^ 3) * (x ^ 3 + 3 * x ^ 2 + x)) + 15 * x ^ 4 * (x ^ 2 + x))
        + -(6 * x ^ 5) * x) + x ^ 6 * 1) :=
    hcombo.congr_fun (fun M => by ring)
  have hval : (((((((x ^ 6 + 15 * x ^ 5 + 65 * x ^ 4 + 90 * x ^ 3 + 31 * x ^ 2 + x)
      + -(6 * x) * (x ^ 5 + 10 * x ^ 4 + 25 * x ^ 3 + 15 * x ^ 2 + x))
      + 15 * x ^ 2 * (x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + x))
      + -(20 * x ^ 3) * (x ^ 3 + 3 * x ^ 2 + x)) + 15 * x ^ 4 * (x ^ 2 + x))
      + -(6 * x ^ 5) * x) + x ^ 6 * 1)
      = 15 * x ^ 3 + 25 * x ^ 2 + x := by ring
  rwa [hval] at h

/-- The weighted sixth moment `∑ w_M v_M^6 / (M+1)` is at most `μ₆ / x`,
via `w_M / (M+1) = w_{M+1} / x`. -/
private theorem shifted_sixth_moment {x : ℝ} (hx : 0 < x)
    (Hg : HasSum (fun K => w x K * ((K : ℝ) - x) ^ 6) (15 * x ^ 3 + 25 * x ^ 2 + x)) :
    ∃ Wval : ℝ, HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 6 / ((M : ℝ) + 1)) Wval
      ∧ Wval ≤ (15 * x ^ 3 + 25 * x ^ 2 + x) / x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hcast : ∀ M : ℕ, ((M : ℝ) + 1 - x) = ((((M + 1) : ℕ)) : ℝ) - x := by
    intro M
    rw [Nat.cast_add, Nat.cast_one]
  have hterm : ∀ M : ℕ, (1 / x) * (w x (M + 1) * (((((M + 1) : ℕ)) : ℝ) - x) ^ 6)
      = w x M * ((M : ℝ) + 1 - x) ^ 6 / ((M : ℝ) + 1) := by
    intro M
    have e1 := w_shift hx M
    have hM : ((M : ℝ) + 1) ≠ 0 := by
      have h0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      positivity
    rw [hcast M]
    have e3 : w x M / ((M : ℝ) + 1) = w x (M + 1) / x := by
      field_simp
      linear_combination -e1
    calc (1 / x) * (w x (M + 1) * (((((M + 1) : ℕ)) : ℝ) - x) ^ 6)
        = (w x (M + 1) / x) * (((((M + 1) : ℕ)) : ℝ) - x) ^ 6 := by ring
      _ = (w x M / ((M : ℝ) + 1)) * (((((M + 1) : ℕ)) : ℝ) - x) ^ 6 := by rw [e3]
      _ = w x M * (((((M + 1) : ℕ)) : ℝ) - x) ^ 6 / ((M : ℝ) + 1) := by ring
  have hsh : Summable
      (fun M => (1 / x) * (w x (M + 1) * (((((M + 1) : ℕ)) : ℝ) - x) ^ 6)) :=
    ((summable_nat_add_iff 1).mpr Hg.summable).mul_left (1 / x)
  have hq : Summable (fun M => w x M * ((M : ℝ) + 1 - x) ^ 6 / ((M : ℝ) + 1)) :=
    hsh.congr hterm
  refine ⟨∑' M, w x M * ((M : ℝ) + 1 - x) ^ 6 / ((M : ℝ) + 1), hq.hasSum, ?_⟩
  have hshg : HasSum (fun K => w x (K + 1) * (((((K + 1) : ℕ)) : ℝ) - x) ^ 6)
      ((15 * x ^ 3 + 25 * x ^ 2 + x) - w x 0 * (0 - x) ^ 6) := by
    have h := (hasSum_nat_add_iff' (f := fun K => w x K * ((K : ℝ) - x) ^ 6) 1).mpr Hg
    simpa using h
  have hmul : HasSum (fun M => (1 / x) * (w x (M + 1) * (((((M + 1) : ℕ)) : ℝ) - x) ^ 6))
      ((1 / x) * ((15 * x ^ 3 + 25 * x ^ 2 + x) - w x 0 * (0 - x) ^ 6)) :=
    hshg.mul_left (1 / x)
  have hq' : HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 6 / ((M : ℝ) + 1))
      ((1 / x) * ((15 * x ^ 3 + 25 * x ^ 2 + x) - w x 0 * (0 - x) ^ 6)) :=
    hmul.congr_fun (fun M => (hterm M).symm)
  have heq : (∑' M, w x M * ((M : ℝ) + 1 - x) ^ 6 / ((M : ℝ) + 1))
      = (1 / x) * ((15 * x ^ 3 + 25 * x ^ 2 + x) - w x 0 * (0 - x) ^ 6) :=
    hq.hasSum.unique hq'
  have hg0 : (0 : ℝ) ≤ w x 0 * (0 - x) ^ 6 :=
    mul_nonneg (w_nonneg hx.le 0) (by positivity)
  rw [heq]
  have hpos : (0 : ℝ) ≤ w x 0 * (0 - x) ^ 6 / x := div_nonneg hg0 hx.le
  have e : (1 / x) * ((15 * x ^ 3 + 25 * x ^ 2 + x) - w x 0 * (0 - x) ^ 6)
      = (15 * x ^ 3 + 25 * x ^ 2 + x) / x - w x 0 * (0 - x) ^ 6 / x := by ring
  linarith

/-- Fifth-order Taylor polynomial of `log (1 + u)` at `u = 0`. -/
private noncomputable def P (u : ℝ) : ℝ := u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 + u ^ 5 / 5

/-- Taylor remainder `log y - P (y - 1)`. -/
private noncomputable def hlog (y : ℝ) : ℝ := Real.log y - P (y - 1)

/-- The Poisson-weighted log series sums to `e ^ (-x) * S`. -/
private theorem wlog_hasSum {x S : ℝ} (hx : 0 < x)
    (H1 : HasSum (fun M => w x M * (M : ℝ) ^ 1) x)
    (hS : HasSum
      (fun j : ℕ => x ^ (j + 1) * Real.log ((j : ℝ) + 2)
        / (Nat.factorial (j + 1) : ℝ)) S) :
    HasSum (fun M => w x M * Real.log ((M : ℝ) + 1)) (Real.exp (-x) * S) := by
  have hlog_le : ∀ M : ℕ, Real.log ((M : ℝ) + 1) ≤ (M : ℝ) := by
    intro M
    have hpos : (0 : ℝ) < (M : ℝ) + 1 := by
      have h0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      linarith
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have hnn : ∀ M : ℕ, 0 ≤ w x M * Real.log ((M : ℝ) + 1) := by
    intro M
    apply mul_nonneg (w_nonneg hx.le M)
    apply Real.log_nonneg
    have h0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hmaj : ∀ M : ℕ, w x M * Real.log ((M : ℝ) + 1) ≤ w x M * (M : ℝ) ^ 1 := by
    intro M
    rw [pow_one]
    exact mul_le_mul_of_nonneg_left (hlog_le M) (w_nonneg hx.le M)
  have hsum : Summable (fun M => w x M * Real.log ((M : ℝ) + 1)) :=
    Summable.of_nonneg_of_le hnn hmaj H1.summable
  have h0 : (fun M => w x M * Real.log ((M : ℝ) + 1)) 0 = 0 := by simp
  have hshift := HasSum_shift_succ
    (f := fun M => w x M * Real.log ((M : ℝ) + 1)) hsum.hasSum h0
  have hterm : ∀ j : ℕ, Real.exp (-x) * (x ^ (j + 1) * Real.log ((j : ℝ) + 2)
      / (Nat.factorial (j + 1) : ℝ))
      = w x (j + 1) * Real.log (((((j + 1) : ℕ)) : ℝ) + 1) := by
    intro j
    have e : ((j : ℝ) + 2) = ((j : ℝ) + 1) + 1 := by ring
    simp only [w, Nat.cast_add, Nat.cast_one]
    rw [e]
    ring
  have h2 : HasSum (fun j : ℕ => Real.exp (-x) * (x ^ (j + 1) * Real.log ((j : ℝ) + 2)
      / (Nat.factorial (j + 1) : ℝ))) (∑' M, w x M * Real.log ((M : ℝ) + 1)) :=
    hshift.congr_fun hterm
  have hmul : HasSum (fun j : ℕ => Real.exp (-x) * (x ^ (j + 1) * Real.log ((j : ℝ) + 2)
      / (Nat.factorial (j + 1) : ℝ))) (Real.exp (-x) * S) := hS.mul_left _
  have heq : (∑' M, w x M * Real.log ((M : ℝ) + 1)) = Real.exp (-x) * S :=
    h2.unique hmul
  have hfin := hsum.hasSum
  rwa [heq] at hfin

/-- Centering: `e ^ (-x) * S - log x` is the sum of `w_M log ((M+1)/x)`. -/
private theorem clog_hasSum {x S : ℝ} (hx : 0 < x)
    (hwlog : HasSum (fun M => w x M * Real.log ((M : ℝ) + 1)) (Real.exp (-x) * S)) :
    HasSum (fun M => w x M * Real.log (((M : ℝ) + 1) / x))
      (Real.exp (-x) * S - Real.log x) := by
  have hwc : HasSum (fun M => Real.log x * w x M) (Real.log x * 1) :=
    (w_hasSum hx.le).mul_left (Real.log x)
  have hsub : HasSum (fun M => w x M * Real.log ((M : ℝ) + 1) - Real.log x * w x M)
      (Real.exp (-x) * S - Real.log x * 1) := hwlog.sub hwc
  have hclog : HasSum (fun M => w x M * (Real.log ((M : ℝ) + 1) - Real.log x))
      (Real.exp (-x) * S - Real.log x * 1) :=
    hsub.congr_fun (fun M => by ring)
  have hval : Real.exp (-x) * S - Real.log x * 1 = Real.exp (-x) * S - Real.log x := by
    ring
  rw [hval] at hclog
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hfin : HasSum (fun M => w x M * Real.log (((M : ℝ) + 1) / x))
      (Real.exp (-x) * S - Real.log x) :=
    hclog.congr_fun (fun M => by
      have hM : ((M : ℝ) + 1) ≠ 0 := by
        have h0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
        positivity
      change w x M * Real.log (((M : ℝ) + 1) / x)
        = w x M * (Real.log ((M : ℝ) + 1) - Real.log x)
      rw [Real.log_div hM hx0])
  exact hfin

/-- The Taylor-polynomial part of the centered series. -/
private theorem pterm_hasSum {x : ℝ} (hx : 0 < x)
    (Hnu1 : HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 1) 1)
    (Hnu2 : HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 2) (x + 1))
    (Hnu3 : HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 3) (4 * x + 1))
    (Hnu4 : HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 4) (3 * x ^ 2 + 11 * x + 1))
    (Hnu5 : HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 5)
      (25 * x ^ 2 + 26 * x + 1)) :
    HasSum (fun M => w x M * P (((M : ℝ) + 1 - x) / x))
      (1 / (2 * x) + 1 / (12 * x ^ 2) + (31 / 12) / x ^ 3 + (99 / 20) / x ^ 4
        + (1 / 5) / x ^ 5) := by
  have hcombo : HasSum (fun M => (1 / x) * (w x M * ((M : ℝ) + 1 - x) ^ 1)
      + (-(1 / (2 * x ^ 2))) * (w x M * ((M : ℝ) + 1 - x) ^ 2)
      + (1 / (3 * x ^ 3)) * (w x M * ((M : ℝ) + 1 - x) ^ 3)
      + (-(1 / (4 * x ^ 4))) * (w x M * ((M : ℝ) + 1 - x) ^ 4)
      + (1 / (5 * x ^ 5)) * (w x M * ((M : ℝ) + 1 - x) ^ 5))
      (((((1 / x) * 1 + (-(1 / (2 * x ^ 2))) * (x + 1))
        + (1 / (3 * x ^ 3)) * (4 * x + 1)) + (-(1 / (4 * x ^ 4))) * (3 * x ^ 2 + 11 * x + 1))
        + (1 / (5 * x ^ 5)) * (25 * x ^ 2 + 26 * x + 1)) :=
    ((((Hnu1.mul_left (1 / x)).add (Hnu2.mul_left (-(1 / (2 * x ^ 2))))).add
      (Hnu3.mul_left (1 / (3 * x ^ 3)))).add (Hnu4.mul_left (-(1 / (4 * x ^ 4))))).add
      (Hnu5.mul_left (1 / (5 * x ^ 5)))
  have h : HasSum (fun M => w x M * P (((M : ℝ) + 1 - x) / x))
      (((((1 / x) * 1 + (-(1 / (2 * x ^ 2))) * (x + 1))
        + (1 / (3 * x ^ 3)) * (4 * x + 1)) + (-(1 / (4 * x ^ 4))) * (3 * x ^ 2 + 11 * x + 1))
        + (1 / (5 * x ^ 5)) * (25 * x ^ 2 + 26 * x + 1)) :=
    hcombo.congr_fun (fun M => by simp only [P]; ring)
  have hval : ((((1 / x) * 1 + (-(1 / (2 * x ^ 2))) * (x + 1))
      + (1 / (3 * x ^ 3)) * (4 * x + 1)) + (-(1 / (4 * x ^ 4))) * (3 * x ^ 2 + 11 * x + 1))
      + (1 / (5 * x ^ 5)) * (25 * x ^ 2 + 26 * x + 1)
      = 1 / (2 * x) + 1 / (12 * x ^ 2) + (31 / 12) / x ^ 3 + (99 / 20) / x ^ 4
        + (1 / 5) / x ^ 5 := by
    have hx0 : x ≠ 0 := ne_of_gt hx
    field_simp
    ring
  rwa [hval] at h

/-- The Taylor-remainder part: nonpositive sum, bounded by the pointwise estimate. -/
private theorem hterm_hasSum {x Wval : ℝ} (hx : 0 < x)
    (Hnu6 : HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 6)
      (15 * x ^ 3 + 130 * x ^ 2 + 57 * x + 1))
    (HW : HasSum (fun M => w x M * ((M : ℝ) + 1 - x) ^ 6 / ((M : ℝ) + 1)) Wval)
    (hbounds : ∀ y : ℝ, 0 < y →
      hlog y ≤ 0 ∧ -(((y - 1) ^ 6 / 6) * (1 + 1 / y)) ≤ hlog y) :
    ∃ Hval : ℝ, HasSum (fun M => w x M * hlog (((M : ℝ) + 1) / x)) Hval ∧ Hval ≤ 0
      ∧ -Hval ≤ (1 / (6 * x ^ 6)) * (15 * x ^ 3 + 130 * x ^ 2 + 57 * x + 1)
        + (1 / (6 * x ^ 5)) * Wval := by
  have hy : ∀ M : ℕ, (0 : ℝ) < ((M : ℝ) + 1) / x := by
    intro M
    apply div_pos _ hx
    have h0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hnn : ∀ M : ℕ, 0 ≤ -(w x M * hlog (((M : ℝ) + 1) / x)) := by
    intro M
    apply neg_nonneg.mpr
    apply mul_nonpos_of_nonneg_of_nonpos (w_nonneg hx.le M)
    exact (hbounds _ (hy M)).1
  have hmaj : ∀ M : ℕ, -(w x M * hlog (((M : ℝ) + 1) / x))
      ≤ (1 / (6 * x ^ 6)) * (w x M * ((M : ℝ) + 1 - x) ^ 6)
        + (1 / (6 * x ^ 5)) * (w x M * ((M : ℝ) + 1 - x) ^ 6 / ((M : ℝ) + 1)) := by
    intro M
    have hT := hbounds _ (hy M)
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hM : ((M : ℝ) + 1) ≠ 0 := by
      have h0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      positivity
    have hx5 : (x ^ 5 : ℝ) ≠ 0 := pow_ne_zero 5 hx0
    have hx6 : (x ^ 6 : ℝ) ≠ 0 := pow_ne_zero 6 hx0
    have h6 : (6 : ℝ) ≠ 0 := by norm_num
    have h65 : ((6 * x ^ 5 : ℝ)) ≠ 0 := mul_ne_zero h6 hx5
    have h66 : ((6 * x ^ 6 : ℝ)) ≠ 0 := mul_ne_zero h6 hx6
    have h65M : ((6 * x ^ 5 * ((M : ℝ) + 1) : ℝ)) ≠ 0 := mul_ne_zero h65 hM
    have hy0 : ((((M : ℝ) + 1) / x : ℝ)) ≠ 0 := div_ne_zero hM hx0
    have e1 : ((((M : ℝ) + 1) / x - 1) ^ 6 / 6) * (1 + 1 / (((M : ℝ) + 1) / x))
        = ((M : ℝ) + 1 - x) ^ 6 / (6 * x ^ 6)
          + ((M : ℝ) + 1 - x) ^ 6 / (6 * x ^ 5 * ((M : ℝ) + 1)) := by
      field_simp
    have hle : -(hlog (((M : ℝ) + 1) / x))
        ≤ ((M : ℝ) + 1 - x) ^ 6 / (6 * x ^ 6)
          + ((M : ℝ) + 1 - x) ^ 6 / (6 * x ^ 5 * ((M : ℝ) + 1)) := by
      rw [← e1]
      linarith [hT.2]
    calc -(w x M * hlog (((M : ℝ) + 1) / x))
        = w x M * (-(hlog (((M : ℝ) + 1) / x))) := by ring
      _ ≤ w x M * (((M : ℝ) + 1 - x) ^ 6 / (6 * x ^ 6)
          + ((M : ℝ) + 1 - x) ^ 6 / (6 * x ^ 5 * ((M : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hle (w_nonneg hx.le M)
      _ = (1 / (6 * x ^ 6)) * (w x M * ((M : ℝ) + 1 - x) ^ 6)
          + (1 / (6 * x ^ 5)) * (w x M * ((M : ℝ) + 1 - x) ^ 6 / ((M : ℝ) + 1)) := by
          field_simp
  have hAmaj : Summable (fun M => (1 / (6 * x ^ 6)) * (w x M * ((M : ℝ) + 1 - x) ^ 6)
      + (1 / (6 * x ^ 5)) * (w x M * ((M : ℝ) + 1 - x) ^ 6 / ((M : ℝ) + 1))) :=
    (Hnu6.summable.mul_left _).add (HW.summable.mul_left _)
  have hnh : Summable (fun M => -(w x M * hlog (((M : ℝ) + 1) / x))) :=
    Summable.of_nonneg_of_le hnn hmaj hAmaj
  have hneg : HasSum (fun M => -(-(w x M * hlog (((M : ℝ) + 1) / x))))
      (-(∑' M, -(w x M * hlog (((M : ℝ) + 1) / x)))) := hnh.hasSum.neg
  have hhterm : HasSum (fun M => w x M * hlog (((M : ℝ) + 1) / x))
      (-(∑' M, -(w x M * hlog (((M : ℝ) + 1) / x)))) :=
    hneg.congr_fun (fun M => by ring)
  have hAmajSum : HasSum (fun M => (1 / (6 * x ^ 6)) * (w x M * ((M : ℝ) + 1 - x) ^ 6)
      + (1 / (6 * x ^ 5)) * (w x M * ((M : ℝ) + 1 - x) ^ 6 / ((M : ℝ) + 1)))
      ((1 / (6 * x ^ 6)) * (15 * x ^ 3 + 130 * x ^ 2 + 57 * x + 1)
        + (1 / (6 * x ^ 5)) * Wval) :=
    (Hnu6.mul_left _).add (HW.mul_left _)
  have hTle : (∑' M, -(w x M * hlog (((M : ℝ) + 1) / x)))
      ≤ (1 / (6 * x ^ 6)) * (15 * x ^ 3 + 130 * x ^ 2 + 57 * x + 1)
        + (1 / (6 * x ^ 5)) * Wval :=
    hasSum_le hmaj hnh.hasSum hAmajSum
  have hTnn : (0 : ℝ) ≤ ∑' M, -(w x M * hlog (((M : ℝ) + 1) / x)) :=
    hasSum_le (fun M => hnn M) hasSum_zero hnh.hasSum
  refine ⟨_, hhterm, ?_, ?_⟩
  · linarith [hTnn]
  · rw [neg_neg]
    exact hTle

/-- Upper barrier `hlog y + (y-1)^6/6` for `y ≥ 1`. -/
private noncomputable def g2 (y : ℝ) : ℝ := hlog y + (y - 1) ^ 6 / 6

/-- Lower barrier `hlog y + (1-y)^6/(6y)` for `0 < y ≤ 1`. -/
private noncomputable def Kf (y : ℝ) : ℝ := hlog y + (1 - y) ^ 6 / (6 * y)

private theorem hasDerivAt_P (u : ℝ) :
    HasDerivAt P (1 - u + u ^ 2 - u ^ 3 + u ^ 4) u := by
  have h2 := (hasDerivAt_pow 2 u).div_const 2
  have h3 := (hasDerivAt_pow 3 u).div_const 3
  have h4 := (hasDerivAt_pow 4 u).div_const 4
  have h5 := (hasDerivAt_pow 5 u).div_const 5
  have h : HasDerivAt (fun u : ℝ => u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 + u ^ 5 / 5)
      (1 - (2 * u ^ 1) / 2 + (3 * u ^ 2) / 3 - (4 * u ^ 3) / 4 + (5 * u ^ 4) / 5) u :=
    ((((hasDerivAt_id u).sub h2).add h3).sub h4).add h5
  have e : (1 - (2 * u ^ 1) / 2 + (3 * u ^ 2) / 3 - (4 * u ^ 3) / 4 + (5 * u ^ 4) / 5)
      = 1 - u + u ^ 2 - u ^ 3 + u ^ 4 := by ring
  rw [e] at h
  exact h

private theorem hasDerivAt_hlog {y : ℝ} (hy0 : y ≠ 0) :
    HasDerivAt hlog (-(y - 1) ^ 5 / y) y := by
  have h1 : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy0
  have h2 : HasDerivAt (fun y => P (y - 1))
      ((1 - (y - 1) + (y - 1) ^ 2 - (y - 1) ^ 3 + (y - 1) ^ 4) * 1) y :=
    HasDerivAt.comp (x := y) (h := fun y => y - 1) (h₂ := P) (hasDerivAt_P (y - 1))
      (HasDerivAt.sub_const 1 (hasDerivAt_id y))
  have h : HasDerivAt (fun y => Real.log y - P (y - 1))
      (y⁻¹ - (1 - (y - 1) + (y - 1) ^ 2 - (y - 1) ^ 3 + (y - 1) ^ 4) * 1) y :=
    h1.sub h2
  have e : (y⁻¹ - (1 - (y - 1) + (y - 1) ^ 2 - (y - 1) ^ 3 + (y - 1) ^ 4) * 1)
      = -(y - 1) ^ 5 / y := by
    field_simp
    ring
  rw [e] at h
  exact h

private theorem hasDerivAt_g2 {y : ℝ} (hy0 : y ≠ 0) :
    HasDerivAt g2 ((y - 1) ^ 6 / y) y := by
  have h1 := hasDerivAt_hlog hy0
  have h2 : HasDerivAt (fun y => (y - 1) ^ 6 / 6) (((6 * (y - 1) ^ 5) * 1) / 6) y :=
    (HasDerivAt.comp (x := y) (h := fun y => y - 1) (h₂ := fun t : ℝ => t ^ 6)
      (hasDerivAt_pow 6 (y - 1)) (HasDerivAt.sub_const 1 (hasDerivAt_id y))).div_const 6
  have h : HasDerivAt (fun y => hlog y + (y - 1) ^ 6 / 6)
      ((-(y - 1) ^ 5 / y) + (((6 * (y - 1) ^ 5) * 1) / 6)) y := h1.add h2
  have e : ((-(y - 1) ^ 5 / y) + (((6 * (y - 1) ^ 5) * 1) / 6)) = (y - 1) ^ 6 / y := by
    field_simp
    ring
  rw [e] at h
  exact h

private theorem hasDerivAt_Kf {y : ℝ} (hy0 : y ≠ 0) :
    HasDerivAt Kf (-(1 - y) ^ 6 / (6 * y ^ 2)) y := by
  have h1 := hasDerivAt_hlog hy0
  have hc : HasDerivAt (fun y => (1 - y) ^ 6) ((6 * (1 - y) ^ 5) * (-1)) y :=
    HasDerivAt.comp (x := y) (h := fun y => 1 - y) (h₂ := fun t : ℝ => t ^ 6)
      (hasDerivAt_pow 6 (1 - y)) (HasDerivAt.const_sub 1 (hasDerivAt_id y))
  have hd : HasDerivAt (fun y => 6 * y) (6 * 1) y :=
    HasDerivAt.const_mul 6 (hasDerivAt_id y)
  have h6y : (6 : ℝ) * y ≠ 0 := mul_ne_zero (by norm_num) hy0
  have hq : HasDerivAt (fun y => (1 - y) ^ 6 / (6 * y))
      ((((6 * (1 - y) ^ 5) * (-1)) * (6 * y) - (1 - y) ^ 6 * (6 * 1)) / (6 * y) ^ 2) y :=
    hc.fun_div hd h6y
  have h : HasDerivAt (fun y => hlog y + (1 - y) ^ 6 / (6 * y))
      ((-(y - 1) ^ 5 / y)
        + ((((6 * (1 - y) ^ 5) * (-1)) * (6 * y) - (1 - y) ^ 6 * (6 * 1)) / (6 * y) ^ 2)) y :=
    h1.add hq
  have e : ((-(y - 1) ^ 5 / y)
        + ((((6 * (1 - y) ^ 5) * (-1)) * (6 * y) - (1 - y) ^ 6 * (6 * 1)) / (6 * y) ^ 2))
      = -(1 - y) ^ 6 / (6 * y ^ 2) := by
    field_simp
    ring
  rw [e] at h
  exact h

private theorem P_zero : P 0 = 0 := by
  simp only [P]
  ring

private theorem hlog_one : hlog 1 = 0 := by
  have e : (1 : ℝ) - 1 = 0 := by ring
  simp only [hlog]
  rw [Real.log_one, e, P_zero, sub_zero]

private theorem g2_one : g2 1 = 0 := by
  have e : (1 : ℝ) - 1 = 0 := by ring
  simp only [g2]
  rw [hlog_one, e]
  ring

private theorem Kf_one : Kf 1 = 0 := by
  have e : (1 : ℝ) - 1 = 0 := by ring
  simp only [Kf]
  rw [hlog_one, e]
  ring

private theorem hlog_contOn_Ici : ContinuousOn hlog (Set.Ici 1) := by
  have hlogc : ContinuousOn Real.log (Set.Ici 1) := by
    apply Real.continuousOn_log.mono
    intro y hy
    have hy' : (1 : ℝ) ≤ y := hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (zero_lt_one.trans_le hy')
  have hPc : Continuous fun y : ℝ => (y - 1) - (y - 1) ^ 2 / 2 + (y - 1) ^ 3 / 3
      - (y - 1) ^ 4 / 4 + (y - 1) ^ 5 / 5 := by fun_prop
  exact hlogc.sub hPc.continuousOn

private theorem g2_contOn_Ici : ContinuousOn g2 (Set.Ici 1) := by
  have h2 : Continuous fun y : ℝ => (y - 1) ^ 6 / 6 := by fun_prop
  exact hlog_contOn_Ici.add h2.continuousOn

private theorem hlog_contOn_Ioc : ContinuousOn hlog (Set.Ioc 0 1) := by
  have hlogc : ContinuousOn Real.log (Set.Ioc 0 1) := by
    apply Real.continuousOn_log.mono
    intro y hy
    have hy' : (0 : ℝ) < y := hy.1
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt hy'
  have hPc : Continuous fun y : ℝ => (y - 1) - (y - 1) ^ 2 / 2 + (y - 1) ^ 3 / 3
      - (y - 1) ^ 4 / 4 + (y - 1) ^ 5 / 5 := by fun_prop
  exact hlogc.sub hPc.continuousOn

private theorem Kf_contOn_Ioc : ContinuousOn Kf (Set.Ioc 0 1) := by
  have hnum : ContinuousOn (fun y : ℝ => (1 - y) ^ 6) (Set.Ioc 0 1) :=
    (by fun_prop : Continuous fun y : ℝ => (1 - y) ^ 6).continuousOn
  have hden : ContinuousOn (fun y : ℝ => 6 * y) (Set.Ioc 0 1) :=
    (by fun_prop : Continuous fun y : ℝ => 6 * y).continuousOn
  have hne : ∀ y ∈ Set.Ioc (0 : ℝ) 1, (6 : ℝ) * y ≠ 0 := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy.1
    exact mul_ne_zero (by norm_num) (ne_of_gt hy')
  exact hlog_contOn_Ioc.add (hnum.div hden hne)

private theorem hlog_anti_Ici : AntitoneOn hlog (Set.Ici 1) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 1) hlog_contOn_Ici
    (f' := fun y => -(y - 1) ^ 5 / y) ?_ ?_
  · intro y hy
    rw [interior_Ici] at hy
    have hy0 : y ≠ 0 := ne_of_gt (zero_lt_one.trans hy)
    exact (hasDerivAt_hlog hy0).hasDerivWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hy1 : (1 : ℝ) < y := hy
    have hy0 : (0 : ℝ) < y := zero_lt_one.trans hy1
    have h5 : (0 : ℝ) ≤ (y - 1) ^ 5 := pow_nonneg (le_of_lt (sub_pos.mpr hy1)) 5
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h5) hy0.le

private theorem g2_mono_Ici : MonotoneOn g2 (Set.Ici 1) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1) g2_contOn_Ici
    (f' := fun y => (y - 1) ^ 6 / y) ?_ ?_
  · intro y hy
    rw [interior_Ici] at hy
    have hy0 : y ≠ 0 := ne_of_gt (zero_lt_one.trans hy)
    exact (hasDerivAt_g2 hy0).hasDerivWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hy0 : (0 : ℝ) < y := zero_lt_one.trans hy
    exact div_nonneg (pow_nonneg (le_of_lt (sub_pos.mpr hy)) 6) hy0.le

private theorem hlog_mono_Ioc : MonotoneOn hlog (Set.Ioc 0 1) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 1) hlog_contOn_Ioc
    (f' := fun y => -(y - 1) ^ 5 / y) ?_ ?_
  · intro y hy
    rw [interior_Ioc] at hy
    have hy0 : y ≠ 0 := ne_of_gt hy.1
    exact (hasDerivAt_hlog hy0).hasDerivWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    have h5 : (y - 1) ^ 5 ≤ 0 := by
      have h4 : (0 : ℝ) ≤ (y - 1) ^ 4 := by positivity
      have h1 : y - 1 ≤ 0 := sub_nonpos.mpr hy.2.le
      calc (y - 1) ^ 5 = (y - 1) ^ 4 * (y - 1) := by ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h4 h1
    exact div_nonneg (neg_nonneg.mpr h5) hy.1.le

private theorem Kf_anti_Ioc : AntitoneOn Kf (Set.Ioc 0 1) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 1) Kf_contOn_Ioc
    (f' := fun y => -(1 - y) ^ 6 / (6 * y ^ 2)) ?_ ?_
  · intro y hy
    rw [interior_Ioc] at hy
    have hy0 : y ≠ 0 := ne_of_gt hy.1
    exact (hasDerivAt_Kf hy0).hasDerivWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    have h6 : (0 : ℝ) ≤ (1 - y) ^ 6 := by positivity
    have hden : (0 : ℝ) ≤ 6 * y ^ 2 := by positivity
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h6) hden

/-- Pointwise Taylor bound for `log`: the remainder is nonpositive and bounded
below by `-(y-1)^6/6 * (1+1/y)`. -/
private theorem hlog_bounds {y : ℝ} (hy : 0 < y) :
    hlog y ≤ 0 ∧ -(((y - 1) ^ 6 / 6) * (1 + 1 / y)) ≤ hlog y := by
  rcases le_total y 1 with hle | hle
  · have hym : y ∈ Set.Ioc (0 : ℝ) 1 := ⟨hy, hle⟩
    have h1m : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_rfl⟩
    have hub : hlog y ≤ 0 := by
      have h := hlog_mono_Ioc hym h1m hle
      rwa [hlog_one] at h
    have hK : (0 : ℝ) ≤ Kf y := by
      have h := Kf_anti_Ioc hym h1m hle
      rwa [Kf_one] at h
    have hlow : -(((y - 1) ^ 6 / 6) * (1 + 1 / y)) ≤ hlog y := by
      have e : (y - 1) ^ 6 = (1 - y) ^ 6 := by ring
      have hA : (0 : ℝ) ≤ (1 - y) ^ 6 / 6 := by positivity
      have hy0 : y ≠ 0 := ne_of_gt hy
      have hid : ((1 - y) ^ 6 / 6) * (1 + 1 / y)
          = (1 - y) ^ 6 / 6 + (1 - y) ^ 6 / (6 * y) := by
        field_simp
      have hK' : (0 : ℝ) ≤ hlog y + (1 - y) ^ 6 / (6 * y) := hK
      rw [e, hid]
      linarith [hA]
    exact ⟨hub, hlow⟩
  · have hym : y ∈ Set.Ici (1 : ℝ) := hle
    have h1m : (1 : ℝ) ∈ Set.Ici (1 : ℝ) := le_rfl
    have hub : hlog y ≤ 0 := by
      have h := hlog_anti_Ici h1m hym hle
      rwa [hlog_one] at h
    have hg : (0 : ℝ) ≤ g2 y := by
      have h := g2_mono_Ici h1m hym hle
      rwa [g2_one] at h
    have hlow : -(((y - 1) ^ 6 / 6) * (1 + 1 / y)) ≤ hlog y := by
      have hA : (0 : ℝ) ≤ (y - 1) ^ 6 / 6 := by positivity
      have h1y : (1 : ℝ) ≤ 1 + 1 / y := by
        have hpos : (0 : ℝ) < 1 / y := one_div_pos.mpr hy
        linarith
      have hle2 : (y - 1) ^ 6 / 6 ≤ ((y - 1) ^ 6 / 6) * (1 + 1 / y) :=
        le_mul_of_one_le_right hA h1y
      have hg' : (0 : ℝ) ≤ hlog y + (y - 1) ^ 6 / 6 := hg
      have hneg : -(((y - 1) ^ 6 / 6) * (1 + 1 / y)) ≤ -((y - 1) ^ 6 / 6) :=
        neg_le_neg hle2
      have h2 : -((y - 1) ^ 6 / 6) ≤ hlog y := by linarith [hg']
      exact le_trans hneg h2
    exact ⟨hub, hlow⟩

/-- **Asymptotics of the logarithmic Poisson series.** There are real constants $C > 0$ and
$x_0$ such that for every real $x \ge x_0$ the series $\sum_{k=1}^{\infty} x^k \log(k + 1) / k!$
has a sum $S$ satisfying
$$\left| e^{-x} S - \log x - \frac{1}{2x} - \frac{1}{12 x^2} \right| \le \frac{C}{x^3}.$$

Proves `Wanted` entry `ramanujan_part1_ch3_entry10_example2_log_poisson_asymptotic`.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 10, Example 2, printed p.
    65 / PDF p. 75.
-/
theorem ramanujan_part1_ch3_entry10_example2_log_poisson_asymptotic :
    ∃ (C : ℝ) (x₀ : ℝ), 0 < C ∧ ∀ (x : ℝ), x₀ ≤ x → ∃ (S : ℝ),
        HasSum (fun j : ℕ => x ^ (j + 1) * Real.log ((j + 2 : ℝ)) / (Nat.factorial (j + 1) : ℝ)) S ∧
            |Real.exp (-x) * S - Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2)| ≤ C / x ^ 3 := by
  refine ⟨50, 1, by norm_num, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have H0 := rho0 hx0.le
  have H1 := rho1 hx0 H0
  have H2 := rho2 hx0 H0 H1
  have H3 := rho3 hx0 H0 H1 H2
  have H4 := rho4 hx0 H0 H1 H2 H3
  have H5 := rho5 hx0 H0 H1 H2 H3 H4
  have H6 := rho6 hx0 H0 H1 H2 H3 H4 H5
  have Hn1 := nu1 H0 H1
  have Hn2 := nu2 H0 H1 H2
  have Hn3 := nu3 H0 H1 H2 H3
  have Hn4 := nu4 H0 H1 H2 H3 H4
  have Hn5 := nu5 H0 H1 H2 H3 H4 H5
  have Hn6 := nu6 H0 H1 H2 H3 H4 H5 H6
  have Hm6 := mu6 H0 H1 H2 H3 H4 H5 H6
  obtain ⟨S, hS⟩ := hasSum_log_poisson hx0
  have hwlog := wlog_hasSum hx0 H1 hS
  have hclog := clog_hasSum hx0 hwlog
  have hpterm := pterm_hasSum hx0 Hn1 Hn2 Hn3 Hn4 Hn5
  obtain ⟨Wval, hW, hWle⟩ := shifted_sixth_moment hx0 Hm6
  obtain ⟨Hval, hhterm, hHle, hHbound⟩ :=
    hterm_hasSum hx0 Hn6 hW (fun y hy => hlog_bounds hy)
  have hsplit : ∀ M : ℕ, w x M * P (((M : ℝ) + 1 - x) / x)
      + w x M * hlog (((M : ℝ) + 1) / x)
      = w x M * Real.log (((M : ℝ) + 1) / x) := by
    intro M
    have e : (((M : ℝ) + 1) / x - 1) = (((M : ℝ) + 1 - x) / x) := by
      have hx0' : x ≠ 0 := ne_of_gt hx0
      field_simp
    simp only [hlog]
    rw [e]
    ring
  have hadd : HasSum (fun M => w x M * P (((M : ℝ) + 1 - x) / x)
      + w x M * hlog (((M : ℝ) + 1) / x))
      ((1 / (2 * x) + 1 / (12 * x ^ 2) + (31 / 12) / x ^ 3 + (99 / 20) / x ^ 4
        + (1 / 5) / x ^ 5) + Hval) :=
    hpterm.add hhterm
  have hclog2 : HasSum (fun M => w x M * Real.log (((M : ℝ) + 1) / x))
      ((1 / (2 * x) + 1 / (12 * x ^ 2) + (31 / 12) / x ^ 3 + (99 / 20) / x ^ 4
        + (1 / 5) / x ^ 5) + Hval) :=
    hadd.congr_fun (fun M => (hsplit M).symm)
  have heq : Real.exp (-x) * S - Real.log x
      = (1 / (2 * x) + 1 / (12 * x ^ 2) + (31 / 12) / x ^ 3 + (99 / 20) / x ^ 4
        + (1 / 5) / x ^ 5) + Hval :=
    hclog.unique hclog2
  have hx3 : (0 : ℝ) < x ^ 3 := by positivity
  have h43 : x ^ 3 ≤ x ^ 4 := pow_le_pow_right₀ hx (by norm_num)
  have h53 : x ^ 3 ≤ x ^ 5 := pow_le_pow_right₀ hx (by norm_num)
  have e4 : (99 / 20 : ℝ) / x ^ 4 ≤ (99 / 20) / x ^ 3 := by
    have h1 : (1 : ℝ) / x ^ 4 ≤ 1 / x ^ 3 := one_div_le_one_div_of_le hx3 h43
    have h2 : (99 / 20) * (1 / x ^ 4) ≤ (99 / 20) * (1 / x ^ 3) :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    have r4 : (99 / 20 : ℝ) / x ^ 4 = (99 / 20) * (1 / x ^ 4) := by ring
    have r3 : (99 / 20 : ℝ) / x ^ 3 = (99 / 20) * (1 / x ^ 3) := by ring
    rw [r4, r3]
    exact h2
  have e5 : (1 / 5 : ℝ) / x ^ 5 ≤ (1 / 5) / x ^ 3 := by
    have h1 : (1 : ℝ) / x ^ 5 ≤ 1 / x ^ 3 := one_div_le_one_div_of_le hx3 h53
    have h2 : (1 / 5) * (1 / x ^ 5) ≤ (1 / 5) * (1 / x ^ 3) :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    have r5 : (1 / 5 : ℝ) / x ^ 5 = (1 / 5) * (1 / x ^ 5) := by ring
    have r3 : (1 / 5 : ℝ) / x ^ 3 = (1 / 5) * (1 / x ^ 3) := by ring
    rw [r5, r3]
    exact h2
  have hPnn : (0 : ℝ) ≤ (31 / 12) / x ^ 3 + (99 / 20) / x ^ 4 + (1 / 5) / x ^ 5 := by
    positivity
  have hPerr : |(31 / 12 : ℝ) / x ^ 3 + (99 / 20) / x ^ 4 + (1 / 5) / x ^ 5| ≤ 8 / x ^ 3 := by
    rw [abs_of_nonneg hPnn]
    calc (31 / 12 : ℝ) / x ^ 3 + (99 / 20) / x ^ 4 + (1 / 5) / x ^ 5
        ≤ (31 / 12) / x ^ 3 + (99 / 20) / x ^ 3 + (1 / 5) / x ^ 3 :=
          add_le_add (add_le_add le_rfl e4) e5
      _ = (116 / 15) / x ^ 3 := by ring
      _ ≤ 8 / x ^ 3 := by
          rw [div_le_div_iff₀ hx3 hx3]
          linarith [hx3]
  have hH : |Hval| ≤ 41 / x ^ 3 := by
    rw [abs_of_nonpos hHle]
    have hBnn : (0 : ℝ) ≤ 1 / (6 * x ^ 5) := by positivity
    have hWle2 : (1 / (6 * x ^ 5)) * Wval
        ≤ (1 / (6 * x ^ 5)) * ((15 * x ^ 3 + 25 * x ^ 2 + x) / x) :=
      mul_le_mul_of_nonneg_left hWle hBnn
    have hmain : (1 / (6 * x ^ 6)) * (15 * x ^ 3 + 130 * x ^ 2 + 57 * x + 1)
        + (1 / (6 * x ^ 5)) * ((15 * x ^ 3 + 25 * x ^ 2 + x) / x) ≤ 41 / x ^ 3 := by
      have eql : (1 / (6 * x ^ 6)) * (15 * x ^ 3 + 130 * x ^ 2 + 57 * x + 1)
          + (1 / (6 * x ^ 5)) * ((15 * x ^ 3 + 25 * x ^ 2 + x) / x)
          = (30 * x ^ 3 + 155 * x ^ 2 + 58 * x + 1) / (6 * x ^ 6) := by
        have hx0' : x ≠ 0 := ne_of_gt hx0
        have h6x5 : ((6 * x ^ 5 : ℝ)) ≠ 0 := by
          have hpos : (0 : ℝ) < 6 * x ^ 5 := by positivity
          exact ne_of_gt hpos
        have h6x6 : ((6 * x ^ 6 : ℝ)) ≠ 0 := by
          have hpos : (0 : ℝ) < 6 * x ^ 6 := by positivity
          exact ne_of_gt hpos
        field_simp
        ring
      rw [eql]
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 6 * x ^ 6) hx3]
      have e : (30 * x ^ 3 + 155 * x ^ 2 + 58 * x + 1) * x ^ 3
          = 30 * x ^ 6 + 155 * x ^ 5 + 58 * x ^ 4 + x ^ 3 := by ring
      rw [e]
      have h5 : x ^ 5 ≤ x ^ 6 := pow_le_pow_right₀ hx (by norm_num)
      have h4 : x ^ 4 ≤ x ^ 6 := pow_le_pow_right₀ hx (by norm_num)
      have h3 : x ^ 3 ≤ x ^ 6 := pow_le_pow_right₀ hx (by norm_num)
      have h6nn : (0 : ℝ) ≤ x ^ 6 := by positivity
      linarith [h5, h4, h3, h6nn]
    calc -Hval
        ≤ (1 / (6 * x ^ 6)) * (15 * x ^ 3 + 130 * x ^ 2 + 57 * x + 1)
          + (1 / (6 * x ^ 5)) * Wval := hHbound
      _ ≤ (1 / (6 * x ^ 6)) * (15 * x ^ 3 + 130 * x ^ 2 + 57 * x + 1)
          + (1 / (6 * x ^ 5)) * ((15 * x ^ 3 + 25 * x ^ 2 + x) / x) :=
          add_le_add le_rfl hWle2
      _ ≤ 41 / x ^ 3 := hmain
  refine ⟨S, hS, ?_⟩
  have hfin : Real.exp (-x) * S - Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2)
      = ((31 / 12) / x ^ 3 + (99 / 20) / x ^ 4 + (1 / 5) / x ^ 5) + Hval := by
    rw [heq]
    ring
  rw [hfin]
  calc |(31 / 12 : ℝ) / x ^ 3 + (99 / 20) / x ^ 4 + (1 / 5) / x ^ 5 + Hval|
      ≤ |(31 / 12 : ℝ) / x ^ 3 + (99 / 20) / x ^ 4 + (1 / 5) / x ^ 5| + |Hval| :=
        abs_add_le _ _
    _ ≤ 8 / x ^ 3 + 41 / x ^ 3 := add_le_add hPerr hH
    _ = 49 / x ^ 3 := by ring
    _ ≤ 50 / x ^ 3 := by
        rw [div_le_div_iff₀ hx3 hx3]
        linarith [hx3]

end Entry10Example2LogPoissonAsymptotic
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
