/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Schröder's exponential series

This file proves Ramanujan's corollary to Entry 13 by means of Abel polynomials, their
binomial convolution, and the tree-function inverse of `z ↦ z * exp (-z)` on the unit disk.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry13CorollarySchroder

private noncomputable def schroder_abelTerm (w : ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  if k = 0 then 1 else z * (z + (k : ℂ) * w) ^ (k - 1)

private lemma schroder_abelTerm_succ (w z : ℂ) (k : ℕ) :
    schroder_abelTerm w (k + 1) z = z * (z + ((k + 1 : ℕ) : ℂ) * w) ^ k := by
  simp [schroder_abelTerm]

private lemma schroder_abelTerm_zero_arg (w : ℂ) (k : ℕ) (hk : k ≠ 0) :
    schroder_abelTerm w k 0 = 0 := by
  simp [schroder_abelTerm, hk]

private lemma schroder_abelTerm_hasDerivAt (w z : ℂ) (k : ℕ) :
    HasDerivAt (fun x => schroder_abelTerm w k x)
      (if k = 0 then 0 else (k : ℂ) * schroder_abelTerm w (k - 1) (z + w)) z := by
  cases k with
  | zero =>
      simpa [schroder_abelTerm] using hasDerivAt_const z (1 : ℂ)
  | succ n =>
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      cases n with
      | zero =>
          have h : HasDerivAt (fun x : ℂ => x) 1 z := hasDerivAt_id z
          simpa [schroder_abelTerm] using h
      | succ m =>
          have hfun : (fun x : ℂ => schroder_abelTerm w (m + 2) x) =
              fun x : ℂ => x * (x + (((m + 2 : ℕ) : ℂ) * w)) ^ (m + 1) := by
            funext x
            rw [schroder_abelTerm_succ]
          have hbase : HasDerivAt
              (fun x : ℂ => x + (((m + 2 : ℕ) : ℂ) * w)) 1 z :=
            (hasDerivAt_id z).add_const _
          have hid : HasDerivAt (fun x : ℂ => x) 1 z := hasDerivAt_id z
          have h := hid.mul (hbase.pow (m + 1))
          rw [hfun]
          convert h using 1
          rw [show m + 1 + 1 - 1 = m + 1 by omega, schroder_abelTerm_succ]
          simp only [Pi.pow_apply, Nat.add_sub_cancel]
          push_cast
          ring

private lemma schroder_choose_succ_mul (n j : ℕ) :
    (((n + 1 : ℕ) : ℂ) * (n.choose j : ℂ)) =
      (((n + 1).choose (j + 1) : ℕ) : ℂ) * ((j + 1 : ℕ) : ℂ) := by
  exact_mod_cast Nat.add_one_mul_choose_eq n j

private theorem schroder_abel_convolution (w : ℂ) : ∀ (n : ℕ) (x y : ℂ),
    (∑ j ∈ Finset.range (n + 1),
      (n.choose j : ℂ) * schroder_abelTerm w j x * schroder_abelTerm w (n - j) y) =
      schroder_abelTerm w n (x + y) := by
  intro n
  induction n with
  | zero =>
      intro x y
      simp [schroder_abelTerm]
  | succ n ih =>
      intro x y
      let lhs : ℂ → ℂ := fun u => ∑ j ∈ Finset.range (n + 2),
        ((n + 1).choose j : ℂ) * schroder_abelTerm w j u *
          schroder_abelTerm w (n + 1 - j) y
      let rhs : ℂ → ℂ := fun u => schroder_abelTerm w (n + 1) (u + y)
      have hlhs : ∀ u : ℂ,
          HasDerivAt lhs
            (((n + 1 : ℕ) : ℂ) * schroder_abelTerm w n (u + w + y)) u := by
        intro u
        have hterm : ∀ j ∈ Finset.range (n + 2), HasDerivAt
            (fun v => ((n + 1).choose j : ℂ) * schroder_abelTerm w j v *
              schroder_abelTerm w (n + 1 - j) y)
            (((n + 1).choose j : ℂ) *
              (if j = 0 then 0
                else (j : ℂ) * schroder_abelTerm w (j - 1) (u + w)) *
              schroder_abelTerm w (n + 1 - j) y) u := by
          intro j _
          exact ((schroder_abelTerm_hasDerivAt w u j).const_mul _).mul_const _
        have hsum := HasDerivAt.sum hterm
        have hderiv : (∑ j ∈ Finset.range (n + 2),
              ((n + 1).choose j : ℂ) *
                (if j = 0 then 0
                  else (j : ℂ) * schroder_abelTerm w (j - 1) (u + w)) *
                schroder_abelTerm w (n + 1 - j) y) =
            ((n + 1 : ℕ) : ℂ) * schroder_abelTerm w n (u + w + y) := by
          rw [Finset.sum_range_succ']
          simp only [Nat.choose_zero_right, Nat.cast_one, ↓reduceIte, mul_zero, zero_mul,
            Nat.add_one_ne_zero, add_zero]
          have hnormalize : (∑ j ∈ Finset.range (n + 1),
                (((n + 1).choose (j + 1) : ℕ) : ℂ) *
                    (((j + 1 : ℕ) : ℂ) *
                      schroder_abelTerm w (j + 1 - 1) (u + w)) *
                  schroder_abelTerm w (n + 1 - (j + 1)) y) =
              ∑ j ∈ Finset.range (n + 1),
                (((n + 1).choose (j + 1) : ℕ) : ℂ) * ((j + 1 : ℕ) : ℂ) *
                  schroder_abelTerm w j (u + w) * schroder_abelTerm w (n - j) y := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
            rw [show j + 1 - 1 = j by omega]
            rw [show n + 1 - (j + 1) = n - j by omega]
            ring
          rw [hnormalize]
          calc
            (∑ j ∈ Finset.range (n + 1),
                (((n + 1).choose (j + 1) : ℕ) : ℂ) * ((j + 1 : ℕ) : ℂ) *
                  schroder_abelTerm w j (u + w) * schroder_abelTerm w (n - j) y) =
                ∑ j ∈ Finset.range (n + 1),
                  ((n + 1 : ℕ) : ℂ) * (n.choose j : ℂ) *
                    schroder_abelTerm w j (u + w) *
                    schroder_abelTerm w (n - j) y := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [← schroder_choose_succ_mul n j]
            _ = ((n + 1 : ℕ) : ℂ) *
                ∑ j ∈ Finset.range (n + 1),
                  (n.choose j : ℂ) * schroder_abelTerm w j (u + w) *
                    schroder_abelTerm w (n - j) y := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ = ((n + 1 : ℕ) : ℂ) * schroder_abelTerm w n (u + w + y) := by
              rw [ih]
        rw [hderiv] at hsum
        have hfun_eq : (∑ j ∈ Finset.range (n + 2), fun v =>
              ((n + 1).choose j : ℂ) * schroder_abelTerm w j v *
                schroder_abelTerm w (n + 1 - j) y) = lhs := by
          funext v
          simp [lhs]
        rw [hfun_eq] at hsum
        exact hsum
      have hrhs : ∀ u : ℂ,
          HasDerivAt rhs
            (((n + 1 : ℕ) : ℂ) * schroder_abelTerm w n (u + w + y)) u := by
        intro u
        have hinner : HasDerivAt (fun v : ℂ => v + y) 1 u :=
          (hasDerivAt_id u).add_const y
        have h := (schroder_abelTerm_hasDerivAt w (u + y) (n + 1)).comp u hinner
        have hfun : ((fun v => schroder_abelTerm w (n + 1) v) ∘
            fun v : ℂ => v + y) = rhs := rfl
        rw [hfun] at h
        simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, mul_one] at h
        convert h using 1
        congr 2
        ring
      have hdiff : ∀ u : ℂ, HasDerivAt (fun v => lhs v - rhs v) 0 u := by
        intro u
        have h := (hlhs u).sub (hrhs u)
        have hfun : lhs - rhs = fun v => lhs v - rhs v := by
          funext v
          rfl
        rw [hfun] at h
        simpa only [sub_self] using h
      have hconst := is_const_of_deriv_eq_zero
        (fun u => (hdiff u).differentiableAt) (fun u => (hdiff u).deriv)
      have hzero : lhs 0 = rhs 0 := by
        simp only [lhs, rhs]
        rw [Finset.sum_eq_single 0]
        · simp [schroder_abelTerm]
        · intro j hj hj0
          rw [schroder_abelTerm_zero_arg w j hj0]
          ring
        · simp
      have h := hconst x 0
      rw [hzero, sub_self] at h
      exact sub_eq_zero.mp h

/-- **Abel's binomial identity.** For a complex number $w$, let $A_0(x) = 1$ and
$A_j(x) = x (x + j w)^{j-1}$ for $j \ge 1$. Then for all complex numbers $x$, $y$ and every
natural number $n$,
$$\sum_{j=0}^{n} \binom{n}{j} A_j(x) A_{n-j}(y) = A_n(x + y).$$
-/
theorem schroder_abel_binomial (w x y : ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) *
        (if j = 0 then 1 else x * (x + (j : ℂ) * w) ^ (j - 1)) *
        (if n - j = 0 then 1
          else y * (y + ((n - j : ℕ) : ℂ) * w) ^ (n - j - 1))) =
      if n = 0 then 1 else (x + y) * (x + y + (n : ℂ) * w) ^ (n - 1) := by
  simpa only [schroder_abelTerm] using schroder_abel_convolution w n x y

private noncomputable def schroder_majorant (R : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1
  else R * (R + (k : ℝ)) ^ (k - 1) * Real.exp (-1) ^ k / (Nat.factorial k : ℝ)

private lemma schroder_exp_base_le (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (hk : 1 ≤ k) :
    (1 + R / (k : ℝ)) ^ k ≤ Real.exp R := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hbase : (1 : ℝ) + R / (k : ℝ) ≤ Real.exp (R / (k : ℝ)) := by
    simpa [add_comm] using Real.add_one_le_exp (R / (k : ℝ))
  calc
    (1 + R / (k : ℝ)) ^ k ≤ (Real.exp (R / (k : ℝ))) ^ k :=
      pow_le_pow_left₀ (add_nonneg zero_le_one (div_nonneg hR hkpos.le)) hbase k
    _ = Real.exp R := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [mul_comm, div_mul_cancel₀ _ hkpos.ne']

private lemma schroder_factorial_stirling_bound (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ^ k / (Nat.factorial k : ℝ) ≤
      Real.exp 1 ^ k / Real.sqrt (2 * Real.pi * (k : ℝ)) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hstirling := Stirling.le_factorial_stirling k
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * (k : ℝ)) := by
    apply Real.sqrt_pos.mpr
    exact mul_pos (by linarith [Real.pi_pos]) hkpos
  have hfactorial : 0 < (Nat.factorial k : ℝ) := by positivity
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  have hpow : (k : ℝ) ^ k = ((k : ℝ) / Real.exp 1) ^ k * Real.exp 1 ^ k := by
    rw [← mul_pow, div_mul_cancel₀ _ hexp.ne']
  have hmul : Real.sqrt (2 * Real.pi * (k : ℝ)) *
        ((k : ℝ) / Real.exp 1) ^ k * Real.exp 1 ^ k ≤
      (Nat.factorial k : ℝ) * Real.exp 1 ^ k :=
    mul_le_mul_of_nonneg_right hstirling (pow_nonneg hexp.le k)
  rw [div_le_iff₀ hfactorial, div_mul_eq_mul_div, le_div_iff₀ hsqrt, hpow]
  calc
    ((k : ℝ) / Real.exp 1) ^ k * Real.exp 1 ^ k *
        Real.sqrt (2 * Real.pi * (k : ℝ)) =
      Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k *
        Real.exp 1 ^ k := by ring
    _ ≤ (Nat.factorial k : ℝ) * Real.exp 1 ^ k := hmul
    _ = Real.exp 1 ^ k * (Nat.factorial k : ℝ) := by ring

private lemma schroder_rpow_three_halves (x : ℝ) (hx : 0 < x) :
    x * Real.sqrt x = x ^ (3 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring, Real.rpow_add hx, Real.rpow_one,
    Real.sqrt_eq_rpow]

private lemma schroder_majorant_summable (R : ℝ) (hR : 0 ≤ R) :
    Summable (schroder_majorant R) := by
  have hp : Summable (fun k : ℕ => ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  have hshift : Summable
      (fun j : ℕ => ((((j + 1 : ℕ)) : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
    simpa using (summable_nat_add_iff 1).mpr hp
  let C : ℝ := R * Real.exp R / Real.sqrt (2 * Real.pi)
  have hmajor : Summable
      (fun j : ℕ => C * ((((j + 1 : ℕ)) : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    hshift.mul_left C
  rw [← summable_nat_add_iff (f := schroder_majorant R) 1]
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hmajor
  · simp only [schroder_majorant, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    positivity
  · let k : ℕ := j + 1
    have hk : 1 ≤ k := by omega
    have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
    have hRk : 0 < R + (k : ℝ) := by linarith
    have hfactorial : 0 < (Nat.factorial k : ℝ) := by positivity
    have hNk : R + (k : ℝ) = (1 + R / (k : ℝ)) * (k : ℝ) := by
      field_simp
      ring
    have hRpow : (R + (k : ℝ)) ^ (k - 1) =
        (R + (k : ℝ)) ^ k / (R + (k : ℝ)) := by
      rw [eq_div_iff hRk.ne']
      have hpow := pow_succ (R + (k : ℝ)) (k - 1)
      rw [show k - 1 + 1 = k by omega] at hpow
      exact hpow.symm
    have hNkpow : (R + (k : ℝ)) ^ k =
        (1 + R / (k : ℝ)) ^ k * (k : ℝ) ^ k := by rw [hNk, mul_pow]
    have hstir := schroder_factorial_stirling_bound k hk
    have hstir' : (k : ℝ) ^ k / (Nat.factorial k : ℝ) * Real.exp (-1) ^ k ≤
        1 / Real.sqrt (2 * Real.pi * (k : ℝ)) := by
      have hnonneg : 0 ≤ Real.exp (-1) ^ k := by positivity
      calc
        (k : ℝ) ^ k / (Nat.factorial k : ℝ) * Real.exp (-1) ^ k ≤
            (Real.exp 1 ^ k / Real.sqrt (2 * Real.pi * (k : ℝ))) *
              Real.exp (-1) ^ k := mul_le_mul_of_nonneg_right hstir hnonneg
        _ = 1 / Real.sqrt (2 * Real.pi * (k : ℝ)) := by
          rw [Real.exp_neg, inv_pow]
          field_simp
    have hsqrt : Real.sqrt (2 * Real.pi * (k : ℝ)) =
        Real.sqrt (2 * Real.pi) * Real.sqrt (k : ℝ) := by
      rw [← Real.sqrt_mul (by positivity)]
    have hrpow := schroder_rpow_three_halves (k : ℝ) hkpos
    simp only [schroder_majorant, Nat.add_one_ne_zero, ↓reduceIte]
    change R * (R + (k : ℝ)) ^ (k - 1) * Real.exp (-1) ^ k /
        (Nat.factorial k : ℝ) ≤ C * ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹
    dsimp only [C]
    calc
      R * (R + (k : ℝ)) ^ (k - 1) * Real.exp (-1) ^ k /
            (Nat.factorial k : ℝ) =
          R * ((1 + R / (k : ℝ)) ^ k *
            ((k : ℝ) ^ k / (Nat.factorial k : ℝ) * Real.exp (-1) ^ k)) /
              (R + (k : ℝ)) := by
        rw [hRpow, hNkpow]
        ring
      _ ≤ R * (Real.exp R *
            (1 / Real.sqrt (2 * Real.pi * (k : ℝ)))) / (R + (k : ℝ)) := by
        apply div_le_div_of_nonneg_right _ hRk.le
        apply mul_le_mul_of_nonneg_left _ hR
        exact mul_le_mul (schroder_exp_base_le R hR k hk) hstir'
          (by positivity) (Real.exp_pos _).le
      _ ≤ R * Real.exp R / Real.sqrt (2 * Real.pi * (k : ℝ)) / (k : ℝ) := by
        have hnum : 0 ≤ R * Real.exp R / Real.sqrt (2 * Real.pi * (k : ℝ)) := by
          positivity
        calc
          R * (Real.exp R * (1 / Real.sqrt (2 * Real.pi * (k : ℝ)))) /
                (R + (k : ℝ)) =
              (R * Real.exp R / Real.sqrt (2 * Real.pi * (k : ℝ))) /
                (R + (k : ℝ)) := by ring
          _ ≤ (R * Real.exp R / Real.sqrt (2 * Real.pi * (k : ℝ))) / (k : ℝ) :=
            div_le_div_of_nonneg_left hnum hkpos (by linarith)
      _ = R * Real.exp R / Real.sqrt (2 * Real.pi) *
          ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
        rw [hsqrt, ← hrpow]
        field_simp

private lemma schroder_term_norm_le_majorant (R : ℝ) (hR : 0 ≤ R)
    (z r : ℂ) (hz : ‖z‖ ≤ R) (hr : ‖r‖ ≤ Real.exp (-1)) (k : ℕ) :
    ‖schroder_abelTerm 1 k z * r ^ k / (Nat.factorial k : ℂ)‖ ≤
      schroder_majorant R k := by
  cases k with
  | zero => simp [schroder_majorant, schroder_abelTerm]
  | succ n =>
      rw [schroder_abelTerm_succ]
      simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast, schroder_majorant,
        Nat.add_one_ne_zero, ↓reduceIte, mul_one, Nat.add_sub_cancel]
      have hbase : ‖z + ((n + 1 : ℕ) : ℂ)‖ ≤ R + ((n + 1 : ℕ) : ℝ) := by
        calc
          ‖z + ((n + 1 : ℕ) : ℂ)‖ ≤ ‖z‖ + ‖((n + 1 : ℕ) : ℂ)‖ := norm_add_le _ _
          _ = ‖z‖ + ((n + 1 : ℕ) : ℝ) := by rw [Complex.norm_natCast]
          _ ≤ R + ((n + 1 : ℕ) : ℝ) := by gcongr
      have hfactorial : 0 < (Nat.factorial (n + 1) : ℝ) := by positivity
      gcongr

private noncomputable def schroder_term (r z : ℂ) (k : ℕ) : ℂ :=
  schroder_abelTerm 1 k z * r ^ k / (Nat.factorial k : ℂ)

private lemma schroder_summable_norm (r z : ℂ) (hr : ‖r‖ ≤ Real.exp (-1)) :
    Summable (fun k => ‖schroder_term r z k‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (schroder_majorant_summable ‖z‖ (norm_nonneg z))
  exact schroder_term_norm_le_majorant ‖z‖ (norm_nonneg z) z r le_rfl hr k

private lemma schroder_summable (r z : ℂ) (hr : ‖r‖ ≤ Real.exp (-1)) :
    Summable (schroder_term r z) :=
  (schroder_summable_norm r z hr).of_norm

private noncomputable def schroder_F (r z : ℂ) : ℂ :=
  ∑' k : ℕ, schroder_term r z k

private lemma schroder_F_zero (r : ℂ) : schroder_F r 0 = 1 := by
  rw [schroder_F, tsum_eq_single 0]
  · simp [schroder_term, schroder_abelTerm]
  · intro k hk
    simp [schroder_term, schroder_abelTerm, hk]

private lemma schroder_term_mul (r x y : ℂ) (n j : ℕ) (hj : j ≤ n) :
    schroder_term r x j * schroder_term r y (n - j) =
      (n.choose j : ℂ) * schroder_abelTerm 1 j x *
        schroder_abelTerm 1 (n - j) y * r ^ n / (Nat.factorial n : ℂ) := by
  have hfactorial : (n.choose j : ℂ) * (Nat.factorial j : ℂ) *
      (Nat.factorial (n - j) : ℂ) = (Nat.factorial n : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  have hpow : r ^ j * r ^ (n - j) = r ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' hj]
  have hjf : (Nat.factorial j : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  have hnjf : (Nat.factorial (n - j) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - j)
  have hnf : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  simp only [schroder_term]
  field_simp
  linear_combination
    (schroder_abelTerm 1 j x * schroder_abelTerm 1 (n - j) y) *
      ((Nat.factorial n : ℂ) * hpow - r ^ n * hfactorial)

private lemma schroder_F_add (r x y : ℂ) (hr : ‖r‖ ≤ Real.exp (-1)) :
    schroder_F r x * schroder_F r y = schroder_F r (x + y) := by
  rw [schroder_F, schroder_F, schroder_F]
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
    (schroder_summable_norm r x hr) (schroder_summable_norm r y hr)]
  apply tsum_congr
  intro n
  calc
    (∑ j ∈ Finset.range (n + 1), schroder_term r x j * schroder_term r y (n - j)) =
        ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) *
          schroder_abelTerm 1 j x * schroder_abelTerm 1 (n - j) y * r ^ n /
            (Nat.factorial n : ℂ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact schroder_term_mul r x y n j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = schroder_term r (x + y) n := by
      rw [← Finset.sum_div, ← Finset.sum_mul, schroder_abel_convolution]
      rfl

private lemma schroder_term_hasDerivAt (r z : ℂ) (k : ℕ) :
    HasDerivAt (fun x => schroder_term r x k)
      ((if k = 0 then 0
        else (k : ℂ) * schroder_abelTerm 1 (k - 1) (z + 1)) * r ^ k /
          (Nat.factorial k : ℂ)) z := by
  simpa only [schroder_term] using
    ((schroder_abelTerm_hasDerivAt 1 z k).mul_const (r ^ k)).div_const
      (Nat.factorial k : ℂ)

private lemma schroder_term_deriv_zero (r z : ℂ) :
    deriv (fun x => schroder_term r x 0) z = 0 := by
  simpa using (schroder_term_hasDerivAt r z 0).deriv

private lemma schroder_term_deriv_succ (r z : ℂ) (n : ℕ) :
    deriv (fun x => schroder_term r x (n + 1)) z =
      r * schroder_term r (z + 1) n := by
  rw [(schroder_term_hasDerivAt r z (n + 1)).deriv]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, schroder_term,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : ((n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  field_simp

private lemma schroder_F_hasDerivAt (r z : ℂ) (hr : ‖r‖ ≤ Real.exp (-1)) :
    HasDerivAt (schroder_F r) (r * schroder_F r (z + 1)) z := by
  let R : ℝ := ‖z‖ + 1
  let U : Set ℂ := Metric.ball 0 R
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hU : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := by
    simp only [U, Metric.mem_ball, dist_zero_right]
    dsimp [R]
    linarith
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ (fun x => schroder_term r x k) U := by
    intro k x _
    exact (schroder_term_hasDerivAt r x k).differentiableAt.differentiableWithinAt
  have hbound : ∀ (k : ℕ) (x : ℂ), x ∈ U →
      ‖schroder_term r x k‖ ≤ schroder_majorant R k := by
    intro k x hx
    apply schroder_term_norm_le_majorant R hR x r
    · exact le_of_lt (by simpa [U, Metric.mem_ball, dist_zero_right] using hx)
    · exact hr
  have hseries := Complex.hasSum_deriv_of_summable_norm
    (schroder_majorant_summable R hR) hdiff hU hbound hzU
  change HasSum (fun k => deriv (fun x => schroder_term r x k) z)
    (deriv (schroder_F r) z) at hseries
  have htail : HasSum
      (fun n => deriv (fun x => schroder_term r x (n + 1)) z)
      (r * schroder_F r (z + 1)) := by
    refine ((schroder_summable r (z + 1) hr).hasSum.mul_left r).congr_fun (fun n => ?_)
    exact schroder_term_deriv_succ r z n
  have htail' := (hasSum_nat_add_iff
    (f := fun k => deriv (fun x => schroder_term r x k) z) 1).mp htail
  have hfull : HasSum (fun k => deriv (fun x => schroder_term r x k) z)
      (r * schroder_F r (z + 1)) := by
    simpa only [Finset.sum_range_one, schroder_term_deriv_zero, add_zero] using htail'
  have hd := Complex.differentiableOn_tsum_of_summable_norm
    (schroder_majorant_summable R hR) hdiff hU hbound
  change DifferentiableOn ℂ (schroder_F r) U at hd
  have hdAt := (hd.differentiableAt (hU.mem_nhds hzU)).hasDerivAt
  rw [hseries.unique hfull] at hdAt
  exact hdAt

private noncomputable def schroder_c (r : ℂ) : ℂ :=
  r * schroder_F r 1

private lemma schroder_F_hasDerivAt_c (r z : ℂ) (hr : ‖r‖ ≤ Real.exp (-1)) :
    HasDerivAt (schroder_F r) (schroder_c r * schroder_F r z) z := by
  convert schroder_F_hasDerivAt r z hr using 1
  rw [← schroder_F_add r z 1 hr]
  simp only [schroder_c]
  ring

private lemma schroder_F_eq_exp (r z : ℂ) (hr : ‖r‖ ≤ Real.exp (-1)) :
    schroder_F r z = Complex.exp (schroder_c r * z) := by
  have hzero : ∀ x : ℂ, HasDerivAt
      (fun y => schroder_F r y * Complex.exp (-(schroder_c r) * y)) 0 x := by
    intro x
    have hlin : HasDerivAt (fun y : ℂ => -(schroder_c r) * y) (-(schroder_c r)) x :=
      by simpa only [id_eq, mul_one] using
        (hasDerivAt_id x).const_mul (-(schroder_c r))
    have hexp : HasDerivAt (fun y => Complex.exp (-(schroder_c r) * y))
        (Complex.exp (-(schroder_c r) * x) * (-(schroder_c r))) x := by
      exact hlin.cexp
    convert (schroder_F_hasDerivAt_c r x hr).mul hexp using 1
    ring_nf
  have hconst := is_const_of_deriv_eq_zero
    (fun x => (hzero x).differentiableAt) (fun x => (hzero x).deriv)
  have hvalue := hconst z 0
  have hproduct : schroder_F r z * Complex.exp (-(schroder_c r) * z) = 1 := by
    simpa [schroder_F_zero] using hvalue
  calc
    schroder_F r z = schroder_F r z *
        (Complex.exp (-(schroder_c r) * z) * Complex.exp (schroder_c r * z)) := by
      rw [show -(schroder_c r) * z = -(schroder_c r * z) by ring, Complex.exp_neg]
      simp
    _ = (schroder_F r z * Complex.exp (-(schroder_c r) * z)) *
        Complex.exp (schroder_c r * z) := by ring
    _ = Complex.exp (schroder_c r * z) := by rw [hproduct, one_mul]

private lemma schroder_c_equation (r : ℂ) (hr : ‖r‖ ≤ Real.exp (-1)) :
    schroder_c r * Complex.exp (-(schroder_c r)) = r := by
  have hc := schroder_F_eq_exp r 1 hr
  simp only [mul_one] at hc
  have hcdef : schroder_c r = r * Complex.exp (schroder_c r) := by
    calc
      schroder_c r = r * schroder_F r 1 := rfl
      _ = r * Complex.exp (schroder_c r) := congrArg (fun x => r * x) hc
  calc
    schroder_c r * Complex.exp (-(schroder_c r)) =
        (r * Complex.exp (schroder_c r)) * Complex.exp (-(schroder_c r)) :=
      congrArg (fun x => x * Complex.exp (-(schroder_c r))) hcdef
    _ = r := by rw [Complex.exp_neg]; field_simp

private lemma schroder_F_parameter_continuousOn :
    ContinuousOn (fun r : ℂ => schroder_F r 1)
      (Metric.closedBall 0 (Real.exp (-1))) := by
  change ContinuousOn (fun r : ℂ => ∑' k : ℕ, schroder_term r 1 k)
    (Metric.closedBall 0 (Real.exp (-1)))
  apply continuousOn_tsum
  · intro k
    exact (continuous_const.mul (continuous_id.pow k)).div_const
      (Nat.factorial k : ℂ) |>.continuousOn
  · exact schroder_majorant_summable 1 zero_le_one
  · intro k r hr
    apply schroder_term_norm_le_majorant 1 zero_le_one 1 r
    · simp
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hr

private lemma schroder_c_continuousOn :
    ContinuousOn schroder_c (Metric.closedBall 0 (Real.exp (-1))) := by
  change ContinuousOn (fun r : ℂ => r * schroder_F r 1)
    (Metric.closedBall 0 (Real.exp (-1)))
  exact continuousOn_id.mul schroder_F_parameter_continuousOn

private lemma schroder_c_norm_le_one (r : ℂ) (hr : ‖r‖ ≤ Real.exp (-1)) :
    ‖schroder_c r‖ ≤ 1 := by
  by_contra hc
  have hcgt : 1 < ‖schroder_c r‖ := lt_of_not_ge hc
  let path : ℝ → ℂ := fun s => (s : ℂ) * r
  have hpath : Set.MapsTo path (Set.Icc (0 : ℝ) 1)
      (Metric.closedBall 0 (Real.exp (-1))) := by
    intro s hs
    simp only [path, Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc
      s * ‖r‖ ≤ s * Real.exp (-1) := mul_le_mul_of_nonneg_left hr hs.1
      _ ≤ 1 * Real.exp (-1) := mul_le_mul_of_nonneg_right hs.2 (Real.exp_pos _).le
      _ = Real.exp (-1) := one_mul _
  have hpath_cont : ContinuousOn path (Set.Icc (0 : ℝ) 1) := by
    exact (Complex.continuous_ofReal.mul continuous_const).continuousOn
  have hvcont : ContinuousOn (fun s : ℝ => ‖schroder_c (path s)‖)
      (Set.Icc (0 : ℝ) 1) :=
    (schroder_c_continuousOn.comp hpath_cont hpath).norm
  have hone_mem : (1 : ℝ) ∈ Set.Icc
      ‖schroder_c (path 0)‖ ‖schroder_c (path 1)‖ := by
    constructor
    · simp [path, schroder_c]
    · simpa [path] using le_of_lt hcgt
  obtain ⟨s, hs, hsc⟩ :=
    (intermediate_value_Icc zero_le_one hvcont hone_mem)
  have hsne : s ≠ 1 := by
    intro h
    subst s
    have : ‖schroder_c r‖ = 1 := by simpa [path] using hsc
    exact (ne_of_gt hcgt) this
  have hslt : s < 1 := lt_of_le_of_ne hs.2 hsne
  have hpath_lt : ‖path s‖ < Real.exp (-1) := by
    simp only [path, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc
      s * ‖r‖ ≤ s * Real.exp (-1) := mul_le_mul_of_nonneg_left hr hs.1
      _ < 1 * Real.exp (-1) := mul_lt_mul_of_pos_right hslt (Real.exp_pos _)
      _ = Real.exp (-1) := one_mul _
  have heq := schroder_c_equation (path s) (le_of_lt hpath_lt)
  have hnormeq := congrArg norm heq
  simp only [norm_mul, Complex.norm_exp, hsc, one_mul] at hnormeq
  have hnormeq' : Real.exp (-(schroder_c (path s)).re) = ‖path s‖ := by
    simpa using hnormeq
  have hre : (schroder_c (path s)).re ≤ 1 := by
    rw [← hsc]
    exact Complex.re_le_norm _
  have hlower : Real.exp (-1) ≤ Real.exp (-(schroder_c (path s)).re) :=
    Real.exp_le_exp.mpr (neg_le_neg hre)
  rw [hnormeq'] at hlower
  exact (not_le_of_gt hpath_lt) hlower

private lemma schroder_exp_sub_norm_le (x y : ℂ) :
    ‖Complex.exp x - Complex.exp y‖ ≤
      Real.exp (max x.re y.re) * ‖x - y‖ := by
  let S : Set ℂ := {z | z.re ≤ max x.re y.re}
  have hderiv : ∀ z ∈ S,
      HasDerivWithinAt Complex.exp (Complex.exp z) S z := by
    intro z _
    exact (Complex.hasDerivAt_exp z).hasDerivWithinAt
  have hbound : ∀ z ∈ S, ‖Complex.exp z‖ ≤ Real.exp (max x.re y.re) := by
    intro z hz
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr hz
  have hx : x ∈ S := by
    change x.re ≤ max x.re y.re
    exact le_max_left _ _
  have hy : y ∈ S := by
    change y.re ≤ max x.re y.re
    exact le_max_right _ _
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_halfSpace_re_le _) hy hx

private lemma schroder_re_lt_one_of_norm_le_one {z : ℂ}
    (hz : ‖z‖ ≤ 1) (hne : z ≠ 1) : z.re < 1 := by
  have hre : z.re ≤ 1 := (Complex.re_le_norm z).trans hz
  apply lt_of_le_of_ne hre
  intro heq
  have hre' : z.re = 1 := heq
  have hnorm : ‖z‖ = 1 := by
    apply le_antisymm hz
    rw [← hre']
    exact Complex.re_le_norm z
  have himsq : z.im ^ 2 = 0 := by
    rw [← Complex.sq_norm_sub_sq_re, hnorm, hre']
    norm_num
  have him : z.im = 0 := sq_eq_zero_iff.mp himsq
  apply hne
  apply Complex.ext
  · simpa using hre'
  · simp [him]

private lemma schroder_endpoint_unique {z : ℂ} (hz : ‖z‖ ≤ 1)
    (h : z * Complex.exp (-z) = Complex.exp (-(1 : ℂ))) : z = 1 := by
  have hfixed : z = Complex.exp (z - 1) := by
    calc
      z = (z * Complex.exp (-z)) * Complex.exp z := by
        rw [Complex.exp_neg]
        field_simp
      _ = Complex.exp (-(1 : ℂ)) * Complex.exp z := by rw [h]
      _ = Complex.exp (z - 1) := by rw [← Complex.exp_add]; congr 1; ring
  have hsub_re : (z - 1).re = z.re - 1 := by simp
  have hsub_im : (z - 1).im = z.im := by simp
  have hnorm := congrArg norm hfixed
  rw [Complex.norm_exp, hsub_re] at hnorm
  have him := congrArg Complex.im hfixed
  rw [Complex.exp_im] at him
  rw [hsub_re, hsub_im] at him
  rw [← hnorm] at him
  have himzero : z.im = 0 := by
    by_contra himne
    have hsine := Real.abs_sin_lt_abs himne
    have habs := congrArg abs him
    rw [abs_mul, abs_of_nonneg (norm_nonneg z)] at habs
    have hmul : ‖z‖ * |Real.sin z.im| ≤ |Real.sin z.im| := by
      nlinarith [abs_nonneg (Real.sin z.im)]
    have : |z.im| < |z.im| := by
      calc
        |z.im| = ‖z‖ * |Real.sin z.im| := habs
        _ ≤ |Real.sin z.im| := hmul
        _ < |z.im| := hsine
    exact (lt_irrefl _ this)
  have hre := congrArg Complex.re hfixed
  rw [Complex.exp_re] at hre
  rw [hsub_re, hsub_im, himzero, Real.cos_zero, mul_one] at hre
  have hre_eq : z.re = 1 := by
    by_contra hne
    have hstrict := Real.add_one_lt_exp (sub_ne_zero.mpr hne)
    rw [← hre] at hstrict
    linarith
  apply Complex.ext
  · simpa using hre_eq
  · simp [himzero]

private lemma schroder_g_injective_unit {r x y : ℂ} (hr : ‖r‖ ≤ Real.exp (-1))
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (hxg : x * Complex.exp (-x) = r) (hyg : y * Complex.exp (-y) = r) : x = y := by
  rcases eq_or_ne x 1 with rfl | hxne
  · symm
    apply schroder_endpoint_unique hy
    calc
      y * Complex.exp (-y) = r := hyg
      _ = Complex.exp (-(1 : ℂ)) := by simpa using hxg.symm
  rcases eq_or_ne y 1 with rfl | hyne
  · apply schroder_endpoint_unique hx
    calc
      x * Complex.exp (-x) = r := hxg
      _ = Complex.exp (-(1 : ℂ)) := by simpa using hyg.symm
  have hfixx : x = r * Complex.exp x := by
    calc
      x = (x * Complex.exp (-x)) * Complex.exp x := by
        rw [Complex.exp_neg]
        field_simp
      _ = r * Complex.exp x := by rw [hxg]
  have hfixy : y = r * Complex.exp y := by
    calc
      y = (y * Complex.exp (-y)) * Complex.exp y := by
        rw [Complex.exp_neg]
        field_simp
      _ = r * Complex.exp y := by rw [hyg]
  have hxre := schroder_re_lt_one_of_norm_le_one hx hxne
  have hyre := schroder_re_lt_one_of_norm_le_one hy hyne
  have hmax : max x.re y.re < 1 := max_lt hxre hyre
  have hcoefficient : ‖r‖ * Real.exp (max x.re y.re) < 1 := by
    calc
      ‖r‖ * Real.exp (max x.re y.re) ≤
          Real.exp (-1) * Real.exp (max x.re y.re) :=
        mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
      _ < Real.exp (-1) * Real.exp 1 :=
        mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hmax) (Real.exp_pos _)
      _ = 1 := by rw [← Real.exp_add]; norm_num
  by_contra hxy
  have hnormpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hsub : x - y = r * (Complex.exp x - Complex.exp y) := by
    calc
      x - y = r * Complex.exp x - r * Complex.exp y := congrArg₂ (· - ·) hfixx hfixy
      _ = r * (Complex.exp x - Complex.exp y) := by ring
  have hle : ‖x - y‖ ≤
      (‖r‖ * Real.exp (max x.re y.re)) * ‖x - y‖ := by
    calc
      ‖x - y‖ = ‖r‖ * ‖Complex.exp x - Complex.exp y‖ := by rw [hsub, norm_mul]
      _ ≤ ‖r‖ * (Real.exp (max x.re y.re) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (schroder_exp_sub_norm_le x y) (norm_nonneg r)
      _ = (‖r‖ * Real.exp (max x.re y.re)) * ‖x - y‖ := by ring
  have hlt : (‖r‖ * Real.exp (max x.re y.re)) * ‖x - y‖ < ‖x - y‖ := by
    calc
      (‖r‖ * Real.exp (max x.re y.re)) * ‖x - y‖ < 1 * ‖x - y‖ :=
        mul_lt_mul_of_pos_right hcoefficient hnormpos
      _ = ‖x - y‖ := one_mul _
  exact (not_lt_of_ge hle) hlt

private lemma schroder_parameter_norm_le (w : ℂ)
    (hw : ‖w‖ ≤ ‖Complex.exp (w - 1)‖) :
    ‖w * Complex.exp (-w)‖ ≤ Real.exp (-1) := by
  rw [Complex.norm_exp] at hw
  rw [norm_mul, Complex.norm_exp]
  calc
    ‖w‖ * Real.exp (-w).re ≤ Real.exp (w - 1).re * Real.exp (-w).re :=
      mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
    _ = Real.exp (-1) := by
      rw [← Real.exp_add]
      congr 1
      simp
      ring

private lemma schroder_rescale_term (z w : ℂ) (hw : w ≠ 0) (k : ℕ) :
    schroder_term (w * Complex.exp (-w)) (z / w) k =
      if k = 0 then 1 else z * (z + (k : ℂ) * w) ^ (k - 1) *
        Complex.exp (-(k : ℂ) * w) / (Nat.factorial k : ℂ) := by
  cases k with
  | zero => simp [schroder_term, schroder_abelTerm]
  | succ n =>
      simp only [Nat.add_one_ne_zero, ↓reduceIte, schroder_term, schroder_abelTerm_succ,
        Nat.add_sub_cancel, mul_pow]
      have hbase : z / w + ((n + 1 : ℕ) : ℂ) =
          (z + ((n + 1 : ℕ) : ℂ) * w) / w := by
        field_simp
      have hexp : Complex.exp (-w) ^ (n + 1) =
          Complex.exp (-((n + 1 : ℕ) : ℂ) * w) := by
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [mul_one, hbase, div_pow, hexp]
      field_simp
      rw [pow_succ]
      ring

/-- **Schröder's exponential series.** Let $z$ and $w$ be complex numbers with
$|w| \le |e^{w-1}|$ and $|w| \le 1$. Then the series
$$1 + \sum_{k=1}^{\infty} \frac{z (z + k w)^{k-1} e^{-k w}}{k!}$$
converges unconditionally, and its sum is $e^z$.

The set of complex numbers $w$ with $|w| \le |e^{w-1}|$ has a bounded lobe containing $0$ and an
unbounded lobe, which meet only at $w = 1$. The condition $|w| \le 1$ selects the bounded lobe
(given the first condition, it is equivalent to $\operatorname{Re} w \le 1$); on the unbounded
lobe the identity fails in general.

Proves `Wanted` entry `ramanujan_part1_ch3_entry13_corollary_schroder`.

Proof: Following Berndt's formula (13.8), we use Abel's binomial identity, a Cauchy product and a
holomorphic ODE; radial continuity selects the unit-disk branch of $u \mapsto u e^{-u}$.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Corollary to Entry 13, formula
    (13.8), printed p. 70 / PDF p. 80.
-/
theorem ramanujan_part1_ch3_entry13_corollary_schroder
    (z w : ℂ) (hw : ‖w‖ ≤ ‖Complex.exp (w - 1)‖) (hw1 : ‖w‖ ≤ 1) :
    HasSum (fun k : ℕ => if k = 0 then 1 else z * (z + (k : ℂ) * w) ^ (k - 1) *
        Complex.exp (-(k : ℂ) * w) / (Nat.factorial k : ℂ)) (Complex.exp z) := by
  by_cases hwzero : w = 0
  · subst w
    have hsum := NormedSpace.expSeries_div_hasSum_exp z
    rw [← Complex.exp_eq_exp_ℂ] at hsum
    refine hsum.congr_fun (fun k => ?_)
    cases k with
    | zero => simp
    | succ n =>
        simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.cast_add, Nat.cast_one, mul_zero,
          add_zero, Complex.exp_zero, mul_one, Nat.add_sub_cancel]
        rw [pow_succ]
        ring
  · let r : ℂ := w * Complex.exp (-w)
    have hr : ‖r‖ ≤ Real.exp (-1) := by
      exact schroder_parameter_norm_le w hw
    have hc_eq : schroder_c r = w := by
      apply schroder_g_injective_unit hr (schroder_c_norm_le_one r hr) hw1
      · exact schroder_c_equation r hr
      · rfl
    have hsum : HasSum
        (fun k : ℕ => if k = 0 then 1 else z * (z + (k : ℂ) * w) ^ (k - 1) *
          Complex.exp (-(k : ℂ) * w) / (Nat.factorial k : ℂ))
        (schroder_F r (z / w)) := by
      refine (schroder_summable r (z / w) hr).hasSum.congr_fun (fun k => ?_)
      simpa only [r] using (schroder_rescale_term z w hwzero k).symm
    have hvalue : schroder_F r (z / w) = Complex.exp z := by
      calc
        schroder_F r (z / w) = Complex.exp (schroder_c r * (z / w)) :=
          schroder_F_eq_exp r (z / w) hr
        _ = Complex.exp z := by
          congr 1
          rw [hc_eq]
          field_simp
    rw [hvalue] at hsum
    exact hsum

end Entry13CorollarySchroder

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
