/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# The `(p, q)`-deformed Spivey formula

This file proves Oussi's addition formula for the `(p, q)`-Bell numbers.  The proof uses
the operator calculus of the source, interpreted on formal power series so that no analytic
convergence argument is needed.
-/

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

private lemma spivey_bracket_add (p q : ℝ) (hpq : p ≠ q) (k j : ℕ) :
    (p ^ (k + j) - q ^ (k + j)) / (p - q) =
      p ^ j * ((p ^ k - q ^ k) / (p - q)) +
        q ^ k * ((p ^ j - q ^ j) / (p - q)) := by
  rw [pow_add, pow_add]
  field_simp
  ring

private lemma spivey_S_eq_zero_of_lt
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ)
    (hS0 : ∀ k, S 0 k = if k = 0 then 1 else 0)
    (hSsucc : ∀ n k, 0 < k →
      S (n + 1) k = p ^ (n + 1 - k) * q ^ (k - 1) * S n (k - 1) +
        bracket k * S n k) :
    ∀ n k, n < k → S n k = 0 := by
  intro n
  induction n with
  | zero =>
      intro k hk
      rw [hS0]
      simp [Nat.ne_of_gt hk]
  | succ n ih =>
      intro k hk
      have hk0 : 0 < k := by omega
      rw [hSsucc n k hk0, ih (k - 1) (by omega), ih k (by omega)]
      ring

private noncomputable def spivey_Xop : Module.End ℝ (PowerSeries ℝ) :=
  (Algebra.lmul ℝ (PowerSeries ℝ)) PowerSeries.X

private lemma spivey_Xop_apply (f : PowerSeries ℝ) :
    spivey_Xop f = PowerSeries.X * f := rfl

private lemma spivey_Xop_pow_apply (k : ℕ) (f : PowerSeries ℝ) :
    (spivey_Xop ^ k) f = PowerSeries.X ^ k * f := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, spivey_Xop_apply, ih, pow_succ]
      ring

private noncomputable def spivey_Nop (p : ℝ) : Module.End ℝ (PowerSeries ℝ) where
  toFun := PowerSeries.rescale p
  map_add' f g := by
    exact map_add (PowerSeries.rescale p) f g
  map_smul' c f := by
    apply PowerSeries.ext
    intro i
    simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul]
    change p ^ i * (c * PowerSeries.coeff i f) = c * (p ^ i * PowerSeries.coeff i f)
    ring

private lemma spivey_Nop_apply (p : ℝ) (f : PowerSeries ℝ) :
    spivey_Nop p f = PowerSeries.rescale p f := rfl

private lemma spivey_Nop_pow_apply (p : ℝ) (a : ℕ) (f : PowerSeries ℝ) :
    ((spivey_Nop p) ^ a) f = PowerSeries.rescale (p ^ a) f := by
  induction a generalizing f with
  | zero =>
      simp
  | succ a ih =>
      rw [pow_succ, Module.End.mul_apply, spivey_Nop_apply, ih,
        PowerSeries.rescale_rescale]
      congr 1
      rw [pow_succ]
      ring_nf

private noncomputable def spivey_Dop (bracket : ℕ → ℝ) :
    Module.End ℝ (PowerSeries ℝ) where
  toFun f := PowerSeries.mk fun i => bracket (i + 1) * PowerSeries.coeff (i + 1) f
  map_add' f g := by
    apply PowerSeries.ext
    intro i
    simp only [PowerSeries.coeff_mk, map_add]
    ring
  map_smul' c f := by
    apply PowerSeries.ext
    intro i
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_smul]
    change bracket (i + 1) * (c * PowerSeries.coeff (i + 1) f) =
      c * (bracket (i + 1) * PowerSeries.coeff (i + 1) f)
    ring

private lemma spivey_coeff_Dop (bracket : ℕ → ℝ) (f : PowerSeries ℝ) (i : ℕ) :
    PowerSeries.coeff i (spivey_Dop bracket f) =
      bracket (i + 1) * PowerSeries.coeff (i + 1) f := by
  simp [spivey_Dop, PowerSeries.coeff_mk]

private lemma spivey_Dop_Nop_pow (bracket : ℕ → ℝ) (p : ℝ) (a : ℕ) :
    spivey_Dop bracket * (spivey_Nop p) ^ a =
      p ^ a • ((spivey_Nop p) ^ a * spivey_Dop bracket) := by
  apply LinearMap.ext
  intro f
  apply PowerSeries.ext
  intro i
  simp only [Module.End.mul_apply, LinearMap.smul_apply, spivey_coeff_Dop,
    spivey_Nop_pow_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_smul]
  change bracket (i + 1) * ((p ^ a) ^ (i + 1) * PowerSeries.coeff (i + 1) f) =
    p ^ a * ((p ^ a) ^ i * (bracket (i + 1) * PowerSeries.coeff (i + 1) f))
  rw [pow_succ]
  ring

private lemma spivey_coeff_XDop (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0)
    (f : PowerSeries ℝ) (i : ℕ) :
    PowerSeries.coeff i ((spivey_Xop * spivey_Dop bracket) f) =
      bracket i * PowerSeries.coeff i f := by
  rw [Module.End.mul_apply, spivey_Xop_apply, show PowerSeries.X =
    (PowerSeries.X : PowerSeries ℝ) ^ 1 by simp, PowerSeries.coeff_X_pow_mul']
  cases i with
  | zero => simp [hbracket0]
  | succ i => simp [spivey_coeff_Dop]

private lemma spivey_Nop_commute_XDop (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0)
    (p : ℝ) : Commute (spivey_Nop p) (spivey_Xop * spivey_Dop bracket) := by
  apply LinearMap.ext
  intro f
  apply PowerSeries.ext
  intro i
  change PowerSeries.coeff i
      (spivey_Nop p ((spivey_Xop * spivey_Dop bracket) f)) =
    PowerSeries.coeff i
      ((spivey_Xop * spivey_Dop bracket) (spivey_Nop p f))
  rw [spivey_Nop_apply, PowerSeries.coeff_rescale,
    spivey_coeff_XDop bracket hbracket0,
    spivey_coeff_XDop bracket hbracket0, spivey_Nop_apply,
    PowerSeries.coeff_rescale]
  ring

private lemma spivey_XDop_Xop_pow
    (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0) (p q : ℝ)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j) (k : ℕ) :
    (spivey_Xop * spivey_Dop bracket) * spivey_Xop ^ k =
      spivey_Xop ^ k *
        (bracket k • spivey_Nop p + q ^ k • (spivey_Xop * spivey_Dop bracket)) := by
  apply LinearMap.ext
  intro f
  apply PowerSeries.ext
  intro i
  change PowerSeries.coeff i
      ((spivey_Xop * spivey_Dop bracket) ((spivey_Xop ^ k) f)) =
    PowerSeries.coeff i ((spivey_Xop ^ k)
      ((bracket k • spivey_Nop p +
        q ^ k • (spivey_Xop * spivey_Dop bracket)) f))
  rw [spivey_coeff_XDop bracket hbracket0, spivey_Xop_pow_apply,
    spivey_Xop_pow_apply, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow_mul']
  by_cases hki : k ≤ i
  · simp only [hki, ite_true]
    have hi : k + (i - k) = i := by omega
    have hb := hbracketAdd k (i - k)
    rw [hi] at hb
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_add,
      PowerSeries.coeff_smul, PowerSeries.coeff_smul, spivey_Nop_apply,
      PowerSeries.coeff_rescale, spivey_coeff_XDop bracket hbracket0, hb]
    change (p ^ (i - k) * bracket k + q ^ k * bracket (i - k)) *
        PowerSeries.coeff (i - k) f =
      bracket k * (p ^ (i - k) * PowerSeries.coeff (i - k) f) +
        q ^ k * (bracket (i - k) * PowerSeries.coeff (i - k) f)
    ring
  · simp [hki]

private lemma spivey_basis_shift (bracket : ℕ → ℝ) (p : ℝ) (k a : ℕ) :
    spivey_Xop ^ k * (spivey_Xop * spivey_Dop bracket) *
        (spivey_Nop p) ^ a * (spivey_Dop bracket) ^ k =
      p ^ a • (spivey_Xop ^ (k + 1) * (spivey_Nop p) ^ a *
        (spivey_Dop bracket) ^ (k + 1)) := by
  calc
    spivey_Xop ^ k * (spivey_Xop * spivey_Dop bracket) *
          (spivey_Nop p) ^ a * (spivey_Dop bracket) ^ k =
        (spivey_Xop ^ k * spivey_Xop) *
          (spivey_Dop bracket * (spivey_Nop p) ^ a) *
            (spivey_Dop bracket) ^ k := by noncomm_ring
    _ = (spivey_Xop ^ k * spivey_Xop) *
          (p ^ a • ((spivey_Nop p) ^ a * spivey_Dop bracket)) *
            (spivey_Dop bracket) ^ k := by rw [spivey_Dop_Nop_pow]
    _ = p ^ a • (spivey_Xop ^ (k + 1) * (spivey_Nop p) ^ a *
          (spivey_Dop bracket) ^ (k + 1)) := by
      rw [pow_succ spivey_Xop k, pow_succ' (spivey_Dop bracket) k]
      simp only [smul_mul_assoc, mul_smul_comm]
      congr 1

private lemma spivey_XDop_mul_basis
    (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0) (p q : ℝ)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j) (k a : ℕ) :
    (spivey_Xop * spivey_Dop bracket) *
        (spivey_Xop ^ k * (spivey_Nop p) ^ a * (spivey_Dop bracket) ^ k) =
      bracket k • (spivey_Xop ^ k * (spivey_Nop p) ^ (a + 1) *
        (spivey_Dop bracket) ^ k) +
      (p ^ a * q ^ k) • (spivey_Xop ^ (k + 1) * (spivey_Nop p) ^ a *
        (spivey_Dop bracket) ^ (k + 1)) := by
  calc
    (spivey_Xop * spivey_Dop bracket) *
          (spivey_Xop ^ k * (spivey_Nop p) ^ a * (spivey_Dop bracket) ^ k) =
        ((spivey_Xop * spivey_Dop bracket) * spivey_Xop ^ k) *
          (spivey_Nop p) ^ a * (spivey_Dop bracket) ^ k := by noncomm_ring
    _ = (spivey_Xop ^ k *
          (bracket k • spivey_Nop p +
            q ^ k • (spivey_Xop * spivey_Dop bracket))) *
          (spivey_Nop p) ^ a * (spivey_Dop bracket) ^ k := by
      rw [spivey_XDop_Xop_pow bracket hbracket0 p q hbracketAdd]
    _ = bracket k • (spivey_Xop ^ k * (spivey_Nop p) ^ (a + 1) *
          (spivey_Dop bracket) ^ k) +
        q ^ k • (spivey_Xop ^ k * (spivey_Xop * spivey_Dop bracket) *
          (spivey_Nop p) ^ a * (spivey_Dop bracket) ^ k) := by
      rw [pow_succ' (spivey_Nop p) a]
      simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
      congr 1
    _ = bracket k • (spivey_Xop ^ k * (spivey_Nop p) ^ (a + 1) *
          (spivey_Dop bracket) ^ k) +
        q ^ k • (p ^ a • (spivey_Xop ^ (k + 1) * (spivey_Nop p) ^ a *
          (spivey_Dop bracket) ^ (k + 1))) := by rw [spivey_basis_shift]
    _ = bracket k • (spivey_Xop ^ k * (spivey_Nop p) ^ (a + 1) *
          (spivey_Dop bracket) ^ k) +
        (p ^ a * q ^ k) • (spivey_Xop ^ (k + 1) * (spivey_Nop p) ^ a *
          (spivey_Dop bracket) ^ (k + 1)) := by
      rw [smul_smul]
      congr 2
      ring

private noncomputable def spivey_basis (p : ℝ) (bracket : ℕ → ℝ) (n k : ℕ) :
    Module.End ℝ (PowerSeries ℝ) :=
  spivey_Xop ^ k * (spivey_Nop p) ^ (n - k) * (spivey_Dop bracket) ^ k

private lemma spivey_XDop_mul_basis_of_le
    (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0) (p q : ℝ)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j) (n k : ℕ) (hkn : k ≤ n) :
    (spivey_Xop * spivey_Dop bracket) * spivey_basis p bracket n k =
      bracket k • spivey_basis p bracket (n + 1) k +
        (p ^ (n - k) * q ^ k) • spivey_basis p bracket (n + 1) (k + 1) := by
  unfold spivey_basis
  rw [spivey_XDop_mul_basis bracket hbracket0 p q hbracketAdd k (n - k)]
  have h₁ : n - k + 1 = n + 1 - k := by omega
  have h₂ : n + 1 - (k + 1) = n - k := by omega
  rw [h₁, h₂]

private lemma spivey_recurrence_sum
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (n : ℕ) (S Snext b c : ℕ → ℝ) (T : ℕ → V)
    (hzero : Snext 0 = 0)
    (hrec : ∀ k, Snext (k + 1) = c k * S k + b (k + 1) * S (k + 1))
    (hbzero : b 0 = 0) (htop : S (n + 1) = 0) :
    (∑ k ∈ Finset.range (n + 2), Snext k • T k) =
      ∑ k ∈ Finset.range (n + 1),
        ((c k * S k) • T (k + 1) + (b k * S k) • T k) := by
  have hshift :
      (∑ k ∈ Finset.range (n + 1), (b (k + 1) * S (k + 1)) • T (k + 1)) =
        ∑ k ∈ Finset.range (n + 1), (b k * S k) • T k := by
    let g : ℕ → V := fun k => (b k * S k) • T k
    have hfirst := Finset.sum_range_succ' g (n + 1)
    have hlast := Finset.sum_range_succ g (n + 1)
    have hgzero : g 0 = 0 := by simp [g, hbzero]
    have hgtop : g (n + 1) = 0 := by simp [g, htop]
    rw [hgzero, add_zero] at hfirst
    rw [hgtop, add_zero] at hlast
    change (∑ k ∈ Finset.range (n + 1), g (k + 1)) =
      ∑ k ∈ Finset.range (n + 1), g k
    rw [← hfirst, hlast]
  rw [Finset.sum_range_succ']
  simp only [hzero, zero_smul, add_zero]
  calc
    (∑ k ∈ Finset.range (n + 1), Snext (k + 1) • T (k + 1)) =
        (∑ k ∈ Finset.range (n + 1), (c k * S k) • T (k + 1)) +
          ∑ k ∈ Finset.range (n + 1), (b (k + 1) * S (k + 1)) • T (k + 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [hrec, add_smul]
    _ = (∑ k ∈ Finset.range (n + 1), (c k * S k) • T (k + 1)) +
          ∑ k ∈ Finset.range (n + 1), (b k * S k) • T k := by rw [hshift]
    _ = ∑ k ∈ Finset.range (n + 1),
          ((c k * S k) • T (k + 1) + (b k * S k) • T k) := by
      rw [Finset.sum_add_distrib]

private theorem spivey_stirling_expansion
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ)
    (hbracket0 : bracket 0 = 0)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j)
    (hS0 : ∀ k, S 0 k = if k = 0 then 1 else 0)
    (hSsucc0 : ∀ n, S (n + 1) 0 = 0)
    (hSsucc : ∀ n k, 0 < k →
      S (n + 1) k = p ^ (n + 1 - k) * q ^ (k - 1) * S n (k - 1) +
        bracket k * S n k) (n : ℕ) :
    (spivey_Xop * spivey_Dop bracket) ^ n =
      ∑ k ∈ Finset.range (n + 1), S n k • spivey_basis p bracket n k := by
  induction n with
  | zero =>
      simp [hS0, spivey_basis]
  | succ n ih =>
      have htop : S n (n + 1) = 0 :=
        spivey_S_eq_zero_of_lt p q bracket S hS0 hSsucc n (n + 1) (by omega)
      have hrec : ∀ k, S (n + 1) (k + 1) =
          (p ^ (n + 1 - (k + 1)) * q ^ k) * S n k +
            bracket (k + 1) * S n (k + 1) := by
        intro k
        rw [hSsucc n (k + 1) (by omega)]
        simp only [Nat.add_sub_cancel]
      have hcollect := spivey_recurrence_sum n (fun k => S n k)
        (fun k => S (n + 1) k) bracket
        (fun k => p ^ (n + 1 - (k + 1)) * q ^ k)
        (fun k => spivey_basis p bracket (n + 1) k)
        (hSsucc0 n) hrec hbracket0 htop
      rw [pow_succ', ih, Finset.mul_sum]
      calc
        (∑ k ∈ Finset.range (n + 1),
            (spivey_Xop * spivey_Dop bracket) *
              (S n k • spivey_basis p bracket n k)) =
            ∑ k ∈ Finset.range (n + 1),
              (((p ^ (n + 1 - (k + 1)) * q ^ k) * S n k) •
                  spivey_basis p bracket (n + 1) (k + 1) +
                (bracket k * S n k) • spivey_basis p bracket (n + 1) k) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkn : k ≤ n := by
            simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
          have hexp : n + 1 - (k + 1) = n - k := by omega
          rw [mul_smul_comm,
            spivey_XDop_mul_basis_of_le bracket hbracket0 p q hbracketAdd n k hkn,
            smul_add, smul_smul, smul_smul, hexp]
          conv_lhs => rw [add_comm]
          congr 1 <;> ring_nf
        _ = ∑ k ∈ Finset.range (n + 2),
              S (n + 1) k • spivey_basis p bracket (n + 1) k := hcollect.symm

private lemma spivey_XDop_pow_Xop_pow
    (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0) (p q : ℝ)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j) (n k : ℕ) :
    (spivey_Xop * spivey_Dop bracket) ^ n * spivey_Xop ^ k =
      spivey_Xop ^ k *
        (bracket k • spivey_Nop p +
          q ^ k • (spivey_Xop * spivey_Dop bracket)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      let A := spivey_Xop * spivey_Dop bracket
      let C := bracket k • spivey_Nop p + q ^ k • A
      calc
        A ^ (n + 1) * spivey_Xop ^ k = A * (A ^ n * spivey_Xop ^ k) := by
          rw [pow_succ']
          noncomm_ring
        _ = A * (spivey_Xop ^ k * C ^ n) := by rw [ih]
        _ = (spivey_Xop ^ k * C) * C ^ n := by
          rw [← mul_assoc, spivey_XDop_Xop_pow bracket hbracket0 p q hbracketAdd]
        _ = spivey_Xop ^ k * C ^ (n + 1) := by
          rw [pow_succ']
          noncomm_ring

private lemma spivey_coeff_XDop_pow (bracket : ℕ → ℝ)
    (hbracket0 : bracket 0 = 0) (j : ℕ) (f : PowerSeries ℝ) (i : ℕ) :
    PowerSeries.coeff i (((spivey_Xop * spivey_Dop bracket) ^ j) f) =
      bracket i ^ j * PowerSeries.coeff i f := by
  induction j generalizing f with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, Module.End.mul_apply, ih,
        spivey_coeff_XDop bracket hbracket0, pow_succ]
      ring

private lemma spivey_coeff_binomial_base
    (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0) (p q : ℝ)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j) (k : ℕ)
    (f : PowerSeries ℝ) (i : ℕ) :
    PowerSeries.coeff i
        ((bracket k • spivey_Nop p +
          q ^ k • (spivey_Xop * spivey_Dop bracket)) f) =
      bracket (k + i) * PowerSeries.coeff i f := by
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_add,
    PowerSeries.coeff_smul, PowerSeries.coeff_smul, spivey_Nop_apply,
    PowerSeries.coeff_rescale, spivey_coeff_XDop bracket hbracket0,
    hbracketAdd]
  change bracket k * (p ^ i * PowerSeries.coeff i f) +
      q ^ k * (bracket i * PowerSeries.coeff i f) =
    (p ^ i * bracket k + q ^ k * bracket i) * PowerSeries.coeff i f
  ring

private lemma spivey_coeff_binomial_base_pow
    (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0) (p q : ℝ)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j) (n k : ℕ)
    (f : PowerSeries ℝ) (i : ℕ) :
    PowerSeries.coeff i
        (((bracket k • spivey_Nop p +
          q ^ k • (spivey_Xop * spivey_Dop bracket)) ^ n) f) =
      bracket (k + i) ^ n * PowerSeries.coeff i f := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, ih,
        spivey_coeff_binomial_base bracket hbracket0 p q hbracketAdd,
        pow_succ]
      ring

private lemma spivey_binomial_expansion
    (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0) (p q : ℝ)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j) (n k : ℕ) :
    (bracket k • spivey_Nop p +
        q ^ k • (spivey_Xop * spivey_Dop bracket)) ^ n =
      ∑ j ∈ Finset.range (n + 1),
        ((Nat.choose n j : ℝ) * bracket k ^ (n - j) * q ^ (j * k)) •
          ((spivey_Nop p) ^ (n - j) *
            (spivey_Xop * spivey_Dop bracket) ^ j) := by
  apply LinearMap.ext
  intro f
  apply PowerSeries.ext
  intro i
  rw [spivey_coeff_binomial_base_pow bracket hbracket0 p q hbracketAdd,
    LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smul_apply, PowerSeries.coeff_smul, Module.End.mul_apply,
    spivey_Nop_pow_apply, PowerSeries.coeff_rescale,
    spivey_coeff_XDop_pow bracket hbracket0]
  rw [hbracketAdd, add_comm, add_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_pow]
  rw [← pow_mul, ← pow_mul, ← pow_mul]
  rw [Nat.mul_comm k j, Nat.mul_comm i (n - j)]
  ring

private lemma spivey_push_Xop
    (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0) (p q : ℝ)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j) (n k : ℕ) :
    (spivey_Xop * spivey_Dop bracket) ^ n * spivey_Xop ^ k =
      spivey_Xop ^ k *
        (∑ j ∈ Finset.range (n + 1),
          ((Nat.choose n j : ℝ) * bracket k ^ (n - j) * q ^ (j * k)) •
            ((spivey_Nop p) ^ (n - j) *
              (spivey_Xop * spivey_Dop bracket) ^ j)) := by
  rw [spivey_XDop_pow_Xop_pow bracket hbracket0 p q hbracketAdd,
    spivey_binomial_expansion bracket hbracket0 p q hbracketAdd]

private lemma spivey_bracket_pos (p q : ℝ) (hq0 : 0 < q) (hqp : q < p)
    (k : ℕ) (hk : 0 < k) : 0 < (p ^ k - q ^ k) / (p - q) := by
  have hpows : q ^ k < p ^ k :=
    pow_lt_pow_left₀ hqp hq0.le (Nat.ne_of_gt hk)
  exact div_pos (sub_pos.mpr hpows) (sub_pos.mpr hqp)

private noncomputable def spivey_ecoeff (p : ℝ) (bracket : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | i + 1 => p ^ i / bracket (i + 1) * spivey_ecoeff p bracket i

private noncomputable def spivey_E (p : ℝ) (bracket : ℕ → ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (spivey_ecoeff p bracket)

private lemma spivey_coeff_E (p : ℝ) (bracket : ℕ → ℝ) (i : ℕ) :
    PowerSeries.coeff i (spivey_E p bracket) = spivey_ecoeff p bracket i := by
  simp [spivey_E, PowerSeries.coeff_mk]

private lemma spivey_ecoeff_succ (p : ℝ) (bracket : ℕ → ℝ)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0) (i : ℕ) :
    bracket (i + 1) * spivey_ecoeff p bracket (i + 1) =
      p ^ i * spivey_ecoeff p bracket i := by
  simp only [spivey_ecoeff]
  field_simp [hbracket_ne (i + 1) (by omega)]

private lemma spivey_Dop_E (p : ℝ) (bracket : ℕ → ℝ)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0) :
    spivey_Dop bracket (spivey_E p bracket) =
      spivey_Nop p (spivey_E p bracket) := by
  apply PowerSeries.ext
  intro i
  rw [spivey_coeff_Dop, spivey_coeff_E, spivey_Nop_apply,
    PowerSeries.coeff_rescale, spivey_coeff_E]
  exact spivey_ecoeff_succ p bracket hbracket_ne i

private lemma spivey_Dop_pow_E (p : ℝ) (bracket : ℕ → ℝ)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0) (k : ℕ) :
    ((spivey_Dop bracket) ^ k) (spivey_E p bracket) =
      p ^ Nat.choose k 2 • ((spivey_Nop p) ^ k) (spivey_E p bracket) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hDN : spivey_Dop bracket
          (((spivey_Nop p) ^ k) (spivey_E p bracket)) =
          p ^ k • ((spivey_Nop p) ^ k)
            (spivey_Dop bracket (spivey_E p bracket)) := by
        have h := congrArg
          (fun T : Module.End ℝ (PowerSeries ℝ) => T (spivey_E p bracket))
          (spivey_Dop_Nop_pow bracket p k)
        simpa only [Module.End.mul_apply, LinearMap.smul_apply] using h
      have hchoose : Nat.choose (k + 1) 2 = Nat.choose k 2 + k := by
        rw [show 2 = 1 + 1 by rfl, Nat.choose_succ_succ, Nat.choose_one_right]
        exact Nat.add_comm _ _
      calc
        ((spivey_Dop bracket) ^ (k + 1)) (spivey_E p bracket) =
            spivey_Dop bracket
              (((spivey_Dop bracket) ^ k) (spivey_E p bracket)) := by
          rw [pow_succ', Module.End.mul_apply]
        _ = spivey_Dop bracket
              (p ^ Nat.choose k 2 •
                ((spivey_Nop p) ^ k) (spivey_E p bracket)) := by rw [ih]
        _ = p ^ Nat.choose k 2 • spivey_Dop bracket
              (((spivey_Nop p) ^ k) (spivey_E p bracket)) := by rw [map_smul]
        _ = p ^ Nat.choose k 2 •
              (p ^ k • ((spivey_Nop p) ^ k)
                (spivey_Dop bracket (spivey_E p bracket))) := by rw [hDN]
        _ = (p ^ Nat.choose k 2 * p ^ k) •
              ((spivey_Nop p) ^ k)
                (spivey_Nop p (spivey_E p bracket)) := by
          rw [spivey_Dop_E p bracket hbracket_ne, smul_smul]
        _ = p ^ Nat.choose (k + 1) 2 •
              ((spivey_Nop p) ^ (k + 1)) (spivey_E p bracket) := by
          rw [hchoose, pow_add, pow_succ, Module.End.mul_apply]

private lemma spivey_Nop_pow_E_ne_zero (p : ℝ) (bracket : ℕ → ℝ) (a : ℕ) :
    ((spivey_Nop p) ^ a) (spivey_E p bracket) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (PowerSeries.coeff 0) hzero
  rw [spivey_Nop_pow_apply, PowerSeries.coeff_rescale, spivey_coeff_E] at hcoeff
  simp [spivey_ecoeff] at hcoeff

private noncomputable def spivey_Bpoly (p : ℝ) (S : ℕ → ℕ → ℝ) (n : ℕ) :
    Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (p ^ Nat.choose k 2 * S n k) * Polynomial.X ^ k

private lemma spivey_Bpoly_eval (p x : ℝ) (S : ℕ → ℕ → ℝ) (n : ℕ) :
    Polynomial.eval x (spivey_Bpoly p S n) =
      ∑ k ∈ Finset.range (n + 1), (p ^ Nat.choose k 2 * S n k) * x ^ k := by
  simp [spivey_Bpoly, Polynomial.eval_finsetSum]

private lemma spivey_coe_Bpoly (p : ℝ) (S : ℕ → ℕ → ℝ) (n : ℕ) :
    ((spivey_Bpoly p S n : Polynomial ℝ) : PowerSeries ℝ) =
      ∑ k ∈ Finset.range (n + 1),
        (p ^ Nat.choose k 2 * S n k) • PowerSeries.X ^ k := by
  change Polynomial.coeToPowerSeries.ringHom (spivey_Bpoly p S n) = _
  rw [show spivey_Bpoly p S n = ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (p ^ Nat.choose k 2 * S n k) * Polynomial.X ^ k by rfl, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
    Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_pow, Algebra.smul_def]

private noncomputable def spivey_BpolyScale
    (p : ℝ) (S : ℕ → ℕ → ℝ) (n : ℕ) (a : ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C ((p ^ Nat.choose k 2 * S n k) * a ^ k) * Polynomial.X ^ k

private lemma spivey_BpolyScale_eval_one (p a : ℝ) (S : ℕ → ℕ → ℝ) (n : ℕ) :
    Polynomial.eval 1 (spivey_BpolyScale p S n a) =
      Polynomial.eval a (spivey_Bpoly p S n) := by
  rw [spivey_Bpoly_eval]
  simp [spivey_BpolyScale, Polynomial.eval_finsetSum]

private lemma spivey_coe_BpolyScale (p a : ℝ) (S : ℕ → ℕ → ℝ) (n : ℕ) :
    ((spivey_BpolyScale p S n a : Polynomial ℝ) : PowerSeries ℝ) =
      ∑ k ∈ Finset.range (n + 1),
        ((p ^ Nat.choose k 2 * S n k) * a ^ k) • PowerSeries.X ^ k := by
  change Polynomial.coeToPowerSeries.ringHom (spivey_BpolyScale p S n a) = _
  rw [show spivey_BpolyScale p S n a = ∑ k ∈ Finset.range (n + 1),
    Polynomial.C ((p ^ Nat.choose k 2 * S n k) * a ^ k) * Polynomial.X ^ k by rfl,
    map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
    Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_pow, Algebra.smul_def]

private lemma spivey_rescale_monomial (a c : ℝ) (k : ℕ) :
    PowerSeries.rescale a (c • (PowerSeries.X : PowerSeries ℝ) ^ k) =
      (c * a ^ k) • PowerSeries.X ^ k := by
  apply PowerSeries.ext
  intro i
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_smul,
    PowerSeries.coeff_smul, PowerSeries.coeff_X_pow]
  by_cases hik : i = k
  · subst i
    simp
    ring
  · simp [hik]

private lemma spivey_rescale_Bpoly (p a : ℝ) (S : ℕ → ℕ → ℝ) (n : ℕ) :
    PowerSeries.rescale a
        ((spivey_Bpoly p S n : Polynomial ℝ) : PowerSeries ℝ) =
      ((spivey_BpolyScale p S n a : Polynomial ℝ) : PowerSeries ℝ) := by
  rw [spivey_coe_Bpoly, map_sum, spivey_coe_BpolyScale]
  apply Finset.sum_congr rfl
  intro k _
  exact spivey_rescale_monomial a (p ^ Nat.choose k 2 * S n k) k

private lemma spivey_Nop_pow_Bpoly_mul
    (p : ℝ) (S : ℕ → ℕ → ℝ) (n a : ℕ) (f : PowerSeries ℝ) :
    ((spivey_Nop p) ^ a)
        (((spivey_Bpoly p S n : Polynomial ℝ) : PowerSeries ℝ) * f) =
      ((spivey_BpolyScale p S n (p ^ a) : Polynomial ℝ) : PowerSeries ℝ) *
        ((spivey_Nop p) ^ a) f := by
  rw [spivey_Nop_pow_apply, spivey_Nop_pow_apply, map_mul,
    spivey_rescale_Bpoly]

private lemma spivey_basis_E
    (p : ℝ) (bracket : ℕ → ℝ)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0)
    (n k : ℕ) (hkn : k ≤ n) :
    spivey_basis p bracket n k (spivey_E p bracket) =
      p ^ Nat.choose k 2 •
        (PowerSeries.X ^ k * ((spivey_Nop p) ^ n) (spivey_E p bracket)) := by
  change (spivey_Xop ^ k)
    (((spivey_Nop p) ^ (n - k))
      (((spivey_Dop bracket) ^ k) (spivey_E p bracket))) = _
  rw [spivey_Dop_pow_E p bracket hbracket_ne, map_smul, map_smul,
    spivey_Xop_pow_apply]
  congr 1
  rw [← Module.End.mul_apply, ← pow_add, Nat.sub_add_cancel hkn]

private lemma spivey_bell_action
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ)
    (hbracket0 : bracket 0 = 0)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0)
    (hS0 : ∀ k, S 0 k = if k = 0 then 1 else 0)
    (hSsucc0 : ∀ n, S (n + 1) 0 = 0)
    (hSsucc : ∀ n k, 0 < k →
      S (n + 1) k = p ^ (n + 1 - k) * q ^ (k - 1) * S n (k - 1) +
        bracket k * S n k) (n : ℕ) :
    ((spivey_Xop * spivey_Dop bracket) ^ n) (spivey_E p bracket) =
      ((spivey_Bpoly p S n : Polynomial ℝ) : PowerSeries ℝ) *
        ((spivey_Nop p) ^ n) (spivey_E p bracket) := by
  have hexp := congrArg
    (fun T : Module.End ℝ (PowerSeries ℝ) => T (spivey_E p bracket))
    (spivey_stirling_expansion p q bracket S hbracket0 hbracketAdd
      hS0 hSsucc0 hSsucc n)
  rw [LinearMap.sum_apply] at hexp
  calc
    ((spivey_Xop * spivey_Dop bracket) ^ n) (spivey_E p bracket) =
        ∑ k ∈ Finset.range (n + 1),
          (S n k • spivey_basis p bracket n k) (spivey_E p bracket) := hexp
    _ = ∑ k ∈ Finset.range (n + 1),
          (p ^ Nat.choose k 2 * S n k) •
            (PowerSeries.X ^ k *
              ((spivey_Nop p) ^ n) (spivey_E p bracket)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := by
        simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
      rw [LinearMap.smul_apply, spivey_basis_E p bracket hbracket_ne n k hkn,
        smul_smul]
      congr 1
      ring
    _ = ((spivey_Bpoly p S n : Polynomial ℝ) : PowerSeries ℝ) *
          ((spivey_Nop p) ^ n) (spivey_E p bracket) := by
      rw [spivey_coe_Bpoly, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [smul_mul_assoc]

private lemma spivey_middle_E
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ)
    (hbracket0 : bracket 0 = 0)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0)
    (hS0 : ∀ k, S 0 k = if k = 0 then 1 else 0)
    (hSsucc0 : ∀ n, S (n + 1) 0 = 0)
    (hSsucc : ∀ n k, 0 < k →
      S (n + 1) k = p ^ (n + 1 - k) * q ^ (k - 1) * S n (k - 1) +
        bracket k * S n k)
    (m n k j : ℕ) (hkm : k ≤ m) (hjn : j ≤ n) :
    ((spivey_Nop p) ^ (n - j) *
        (spivey_Xop * spivey_Dop bracket) ^ j *
        (spivey_Nop p) ^ (m - k) * (spivey_Dop bracket) ^ k)
        (spivey_E p bracket) =
      p ^ Nat.choose k 2 •
        (((spivey_BpolyScale p S j (p ^ (n + m - j)) : Polynomial ℝ) :
            PowerSeries ℝ) *
          ((spivey_Nop p) ^ (n + m)) (spivey_E p bracket)) := by
  change ((spivey_Nop p) ^ (n - j))
    (((spivey_Xop * spivey_Dop bracket) ^ j)
      (((spivey_Nop p) ^ (m - k))
        (((spivey_Dop bracket) ^ k) (spivey_E p bracket)))) = _
  rw [spivey_Dop_pow_E p bracket hbracket_ne]
  simp only [map_smul]
  congr 1
  have hNm : ((spivey_Nop p) ^ (m - k))
      (((spivey_Nop p) ^ k) (spivey_E p bracket)) =
      ((spivey_Nop p) ^ m) (spivey_E p bracket) := by
    rw [← Module.End.mul_apply, ← pow_add, Nat.sub_add_cancel hkm]
  rw [hNm]
  have hcomm := (spivey_Nop_commute_XDop bracket hbracket0 p).pow_pow m j
  have hcomm_apply :
      ((spivey_Xop * spivey_Dop bracket) ^ j)
          (((spivey_Nop p) ^ m) (spivey_E p bracket)) =
        ((spivey_Nop p) ^ m)
          (((spivey_Xop * spivey_Dop bracket) ^ j) (spivey_E p bracket)) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← hcomm.eq]
  rw [hcomm_apply, ← Module.End.mul_apply, ← pow_add,
    show n - j + m = n + m - j by omega,
    spivey_bell_action p q bracket S hbracket0 hbracketAdd hbracket_ne
      hS0 hSsucc0 hSsucc j,
    spivey_Nop_pow_Bpoly_mul]
  congr 1
  rw [← Module.End.mul_apply, ← pow_add,
    show n + m - j + j = n + m by omega]

private lemma spivey_main_term_E
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ)
    (hbracket0 : bracket 0 = 0)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0)
    (hS0 : ∀ k, S 0 k = if k = 0 then 1 else 0)
    (hSsucc0 : ∀ n, S (n + 1) 0 = 0)
    (hSsucc : ∀ n k, 0 < k →
      S (n + 1) k = p ^ (n + 1 - k) * q ^ (k - 1) * S n (k - 1) +
        bracket k * S n k)
    (m n k j : ℕ) (hkm : k ≤ m) (hjn : j ≤ n) :
    (spivey_Xop ^ k * (spivey_Nop p) ^ (n - j) *
        (spivey_Xop * spivey_Dop bracket) ^ j *
        (spivey_Nop p) ^ (m - k) * (spivey_Dop bracket) ^ k)
        (spivey_E p bracket) =
      p ^ Nat.choose k 2 •
        ((PowerSeries.X ^ k *
            ((spivey_BpolyScale p S j (p ^ (n + m - j)) : Polynomial ℝ) :
              PowerSeries ℝ)) *
          ((spivey_Nop p) ^ (n + m)) (spivey_E p bracket)) := by
  change (spivey_Xop ^ k)
    (((spivey_Nop p) ^ (n - j) *
      (spivey_Xop * spivey_Dop bracket) ^ j *
      (spivey_Nop p) ^ (m - k) * (spivey_Dop bracket) ^ k)
      (spivey_E p bracket)) = _
  rw [spivey_middle_E p q bracket S hbracket0 hbracketAdd hbracket_ne
    hS0 hSsucc0 hSsucc m n k j hkm hjn, map_smul, spivey_Xop_pow_apply]
  congr 1
  ring

private lemma spivey_expand_term_E
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ)
    (hbracket0 : bracket 0 = 0)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0)
    (hS0 : ∀ k, S 0 k = if k = 0 then 1 else 0)
    (hSsucc0 : ∀ n, S (n + 1) 0 = 0)
    (hSsucc : ∀ n k, 0 < k →
      S (n + 1) k = p ^ (n + 1 - k) * q ^ (k - 1) * S n (k - 1) +
        bracket k * S n k)
    (m n k : ℕ) (hkm : k ≤ m) :
    ((spivey_Xop * spivey_Dop bracket) ^ n * spivey_basis p bracket m k)
        (spivey_E p bracket) =
      ∑ j ∈ Finset.range (n + 1),
        (((Nat.choose n j : ℝ) * bracket k ^ (n - j) * q ^ (j * k)) *
          p ^ Nat.choose k 2) •
          ((PowerSeries.X ^ k *
              ((spivey_BpolyScale p S j (p ^ (n + m - j)) : Polynomial ℝ) :
                PowerSeries ℝ)) *
            ((spivey_Nop p) ^ (n + m)) (spivey_E p bracket)) := by
  unfold spivey_basis
  rw [show (spivey_Xop * spivey_Dop bracket) ^ n *
      (spivey_Xop ^ k * (spivey_Nop p) ^ (m - k) *
        (spivey_Dop bracket) ^ k) =
      (((spivey_Xop * spivey_Dop bracket) ^ n * spivey_Xop ^ k) *
        (spivey_Nop p) ^ (m - k) * (spivey_Dop bracket) ^ k) by noncomm_ring,
    spivey_push_Xop bracket hbracket0 p q hbracketAdd,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  have hdist :
      (∑ j ∈ Finset.range (n + 1),
          spivey_Xop ^ k *
            (((Nat.choose n j : ℝ) * bracket k ^ (n - j) * q ^ (j * k)) •
              ((spivey_Nop p) ^ (n - j) *
                (spivey_Xop * spivey_Dop bracket) ^ j)) *
            (spivey_Nop p) ^ (m - k) * (spivey_Dop bracket) ^ k) =
        ∑ j ∈ Finset.range (n + 1),
          ((Nat.choose n j : ℝ) * bracket k ^ (n - j) * q ^ (j * k)) •
            (spivey_Xop ^ k * (spivey_Nop p) ^ (n - j) *
              (spivey_Xop * spivey_Dop bracket) ^ j *
              (spivey_Nop p) ^ (m - k) * (spivey_Dop bracket) ^ k) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [mul_smul_comm, smul_mul_assoc]
    congr 1
  rw [hdist, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hj
  rw [LinearMap.smul_apply,
    spivey_main_term_E p q bracket S hbracket0 hbracketAdd hbracket_ne
      hS0 hSsucc0 hSsucc m n k j hkm hjn, smul_smul]

private noncomputable def spivey_Rpoly
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ) (m n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
    Polynomial.C ((Nat.choose n j : ℝ) * (p ^ Nat.choose k 2 * S m k) *
      bracket k ^ (n - j) * q ^ (j * k)) *
      Polynomial.X ^ k * spivey_BpolyScale p S j (p ^ (n + m - j))

private lemma spivey_Rpoly_eval_one
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ) (m n : ℕ) :
    Polynomial.eval 1 (spivey_Rpoly p q bracket S m n) =
      ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n j : ℝ) * (p ^ Nat.choose k 2 * S m k) *
          bracket k ^ (n - j) * q ^ (j * k) *
            Polynomial.eval (p ^ (n + m - j)) (spivey_Bpoly p S j) := by
  unfold spivey_Rpoly
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, one_pow,
    spivey_BpolyScale_eval_one]
  ring

private lemma spivey_coe_Rpoly
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ) (m n : ℕ) :
    ((spivey_Rpoly p q bracket S m n : Polynomial ℝ) : PowerSeries ℝ) =
      ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        PowerSeries.C ((Nat.choose n j : ℝ) * (p ^ Nat.choose k 2 * S m k) *
          bracket k ^ (n - j) * q ^ (j * k)) *
            (PowerSeries.X ^ k *
              ((spivey_BpolyScale p S j (p ^ (n + m - j)) : Polynomial ℝ) :
                PowerSeries ℝ)) := by
  change Polynomial.coeToPowerSeries.ringHom (spivey_Rpoly p q bracket S m n) = _
  rw [show spivey_Rpoly p q bracket S m n =
    ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      Polynomial.C ((Nat.choose n j : ℝ) * (p ^ Nat.choose k 2 * S m k) *
        bracket k ^ (n - j) * q ^ (j * k)) *
        Polynomial.X ^ k * spivey_BpolyScale p S j (p ^ (n + m - j)) by rfl,
    map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X,
    Polynomial.coeToPowerSeries.ringHom_apply]
  ring

private theorem spivey_generic
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ)
    (hbracket0 : bracket 0 = 0)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0)
    (hS0 : ∀ k, S 0 k = if k = 0 then 1 else 0)
    (hSsucc0 : ∀ n, S (n + 1) 0 = 0)
    (hSsucc : ∀ n k, 0 < k →
      S (n + 1) k = p ^ (n + 1 - k) * q ^ (k - 1) * S n (k - 1) +
        bracket k * S n k) (m n : ℕ) :
    Polynomial.eval 1 (spivey_Bpoly p S (n + m)) =
      ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n j : ℝ) * (p ^ Nat.choose k 2 * S m k) *
          bracket k ^ (n - j) * q ^ (j * k) *
            Polynomial.eval (p ^ (n + m - j)) (spivey_Bpoly p S j) := by
  let A := spivey_Xop * spivey_Dop bracket
  let E := spivey_E p bracket
  let F := ((spivey_Nop p) ^ (n + m)) E
  have hleft := spivey_bell_action p q bracket S hbracket0 hbracketAdd
    hbracket_ne hS0 hSsucc0 hSsucc (n + m)
  have hmexp := spivey_stirling_expansion p q bracket S hbracket0 hbracketAdd
    hS0 hSsucc0 hSsucc m
  have hprod :
      ((spivey_Bpoly p S (n + m) : Polynomial ℝ) : PowerSeries ℝ) * F =
        ((spivey_Rpoly p q bracket S m n : Polynomial ℝ) : PowerSeries ℝ) * F := by
    calc
      ((spivey_Bpoly p S (n + m) : Polynomial ℝ) : PowerSeries ℝ) * F =
          (A ^ (n + m)) E := hleft.symm
      _ = (A ^ n * A ^ m) E := by rw [pow_add]
      _ = (A ^ n *
          (∑ k ∈ Finset.range (m + 1),
            S m k • spivey_basis p bracket m k)) E := by rw [hmexp]
      _ = (∑ k ∈ Finset.range (m + 1),
          S m k • (A ^ n * spivey_basis p bracket m k)) E := by
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_smul_comm]
      _ = ∑ k ∈ Finset.range (m + 1),
          S m k • ((A ^ n * spivey_basis p bracket m k) E) := by
        rw [LinearMap.sum_apply]
        apply Finset.sum_congr rfl
        intro k _
        rw [LinearMap.smul_apply]
      _ = ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
          ((Nat.choose n j : ℝ) * (p ^ Nat.choose k 2 * S m k) *
            bracket k ^ (n - j) * q ^ (j * k)) •
              ((PowerSeries.X ^ k *
                  ((spivey_BpolyScale p S j (p ^ (n + m - j)) : Polynomial ℝ) :
                    PowerSeries ℝ)) * F) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkm : k ≤ m := by
          simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
        rw [spivey_expand_term_E p q bracket S hbracket0 hbracketAdd
          hbracket_ne hS0 hSsucc0 hSsucc m n k hkm, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_smul]
        congr 1
        ring
      _ = ((spivey_Rpoly p q bracket S m n : Polynomial ℝ) : PowerSeries ℝ) * F := by
        rw [spivey_coe_Rpoly, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [PowerSeries.smul_eq_C_mul]
        ring
  have hF : F ≠ 0 := spivey_Nop_pow_E_ne_zero p bracket (n + m)
  have hcoe :
      ((spivey_Bpoly p S (n + m) : Polynomial ℝ) : PowerSeries ℝ) =
        ((spivey_Rpoly p q bracket S m n : Polynomial ℝ) : PowerSeries ℝ) :=
    mul_right_cancel₀ hF hprod
  have hpoly : spivey_Bpoly p S (n + m) = spivey_Rpoly p q bracket S m n :=
    Polynomial.coe_injective ℝ hcoe
  have heval := congrArg (Polynomial.eval 1) hpoly
  rw [spivey_Rpoly_eval_one] at heval
  exact heval

private theorem spivey_generic_sum
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ)
    (hbracket0 : bracket 0 = 0)
    (hbracketAdd : ∀ k j, bracket (k + j) = p ^ j * bracket k + q ^ k * bracket j)
    (hbracket_ne : ∀ k, 0 < k → bracket k ≠ 0)
    (hS0 : ∀ k, S 0 k = if k = 0 then 1 else 0)
    (hSsucc0 : ∀ a, S (a + 1) 0 = 0)
    (hSsucc : ∀ a k, 0 < k →
      S (a + 1) k = p ^ (a + 1 - k) * q ^ (k - 1) * S a (k - 1) +
        bracket k * S a k)
    (m n : ℕ) :
    (∑ k ∈ Finset.range (n + m + 1),
        (p ^ Nat.choose k 2 * S (n + m) k) * 1 ^ k) =
      ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n j : ℝ) * (p ^ Nat.choose k 2 * S m k) * bracket k ^ (n - j)
          * q ^ (j * k) *
            ∑ ell ∈ Finset.range (j + 1),
              (p ^ Nat.choose ell 2 * S j ell) * (p ^ (n + m - j)) ^ ell := by
  simpa [spivey_Bpoly_eval] using
    spivey_generic p q bracket S hbracket0 hbracketAdd hbracket_ne hS0 hSsucc0 hSsucc m n

/- Lean lifts the recursive `let` in the public theorem's signature after elaborating its proof.
This helper constructs the application to `spivey_generic_sum` using that pending declaration. -/
private def spivey_finish_public : Lean.Elab.Tactic.TacticM Unit := do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    let target ← Lean.instantiateMVars (← goal.getType)
    let recs ← Lean.Elab.Term.getLetRecsToLift
    let mut rec? := none
    for mvarId in (← Lean.Meta.getMVars target) do
      let root ← Lean.getDelayedMVarRoot mvarId
      if let some rec := recs.find? (fun rec => rec.mvarId == root) then
        rec? := some rec
    let some rec := rec? | throwError "recursive declaration `S` not found"
    let lctx ← Lean.getLCtx
    let getLocal (name : Lean.Name) : Lean.Meta.MetaM Lean.Expr := do
      let some decl := lctx.findFromUserName? name | throwError "local `{name}` not found"
      return decl.toExpr
    let p ← getLocal `p
    let q ← getLocal `q
    let bracket ← getLocal `bracket
    let hbracket0 ← getLocal `hbracket0
    let hbracketAdd ← getLocal `hbracketAdd
    let hbracket_ne ← getLocal `hbracket_ne
    let m ← getLocal `m
    let n ← getLocal `n
    let S := Lean.mkAppN (.const rec.declName []) #[p, q, bracket]
    let generic := Lean.mkConst ``spivey_generic_sum
    let mut genericType ← Lean.Meta.inferType generic
    for arg in #[p, q, bracket, S, hbracket0, hbracketAdd, hbracket_ne] do
      genericType := genericType.bindingBody!.instantiate1 arg
    let hS0Type := genericType.bindingDomain!
    let hS0 ← Lean.Meta.forallTelescopeReducing hS0Type fun xs body => do
      let some (_, _, rhs) := body.eq? | throwError "initial equation expected"
      let refl ← Lean.Meta.mkAppM ``Eq.refl #[rhs]
      Lean.Meta.mkLambdaFVars xs refl
    genericType := genericType.bindingBody!.instantiate1 hS0
    let hSsucc0Type := genericType.bindingDomain!
    let (hSsucc0, realZero) ← Lean.Meta.forallTelescopeReducing hSsucc0Type fun xs body => do
      let some (_, _, rhs) := body.eq? | throwError "zero equation expected"
      let refl ← Lean.Meta.mkAppM ``Eq.refl #[rhs]
      return (← Lean.Meta.mkLambdaFVars xs refl, rhs)
    genericType := genericType.bindingBody!.instantiate1 hSsucc0
    let hSsuccType := genericType.bindingDomain!
    let hSsucc ← Lean.Meta.forallTelescopeReducing hSsuccType fun xs body => do
      let some (_, _, rhs) := body.eq? | throwError "successor equation expected"
      let k := xs[1]!
      let hk := xs[2]!
      let natZero := Lean.mkNatLit 0
      let hne ← Lean.Meta.mkAppM ``Nat.ne_of_gt #[hk]
      let condition := Lean.mkAppN (Lean.mkConst ``Eq [.succ .zero])
        #[Lean.mkConst ``Nat, k, natZero]
      let decision := Lean.mkApp2 (Lean.mkConst ``Nat.decEq) k natZero
      let proof := Lean.mkAppN (Lean.mkConst ``if_neg [.succ .zero])
        #[condition, decision, hne, Lean.mkConst ``Real, realZero, rhs]
      Lean.Meta.mkLambdaFVars xs proof
    let proof := Lean.mkAppN generic
      #[p, q, bracket, S, hbracket0, hbracketAdd, hbracket_ne,
        hS0, hSsucc0, hSsucc, m, n]
    goal.assign proof
    Lean.Elab.Tactic.replaceMainGoal []

/-- **The (p, q)-deformed Spivey formula.** Let $p$ and $q$ be real numbers with
$0 < q < p \le 1$, and for $k \in \mathbb{N}$ put $[k] = (p^k - q^k)/(p - q)$. Define real numbers
$S(n, k)$ for $n, k \in \mathbb{N}$ by $S(0, 0) = 1$, $S(0, k) = 0$ for $k \ge 1$,
$S(n + 1, 0) = 0$, and, for $k \ge 1$,
$S(n + 1, k) = p^{n + 1 - k} q^{k - 1} S(n, k - 1) + [k] \, S(n, k)$, where the exponent
$n + 1 - k$ is read as $0$ when $k > n + 1$. Put $\tilde S(n, k) = p^{\binom{k}{2}} S(n, k)$ and
$\tilde B_n(x) = \sum_{k=0}^{n} \tilde S(n, k) \, x^k$ for real $x$. Then for all
$m, n \in \mathbb{N}$,

$$\tilde B_{n+m}(1) = \sum_{k=0}^{m} \sum_{j=0}^{n} \binom{n}{j} \tilde S(m, k) \, [k]^{n-j} \,
q^{jk} \, \tilde B_j\bigl(p^{n+m-j}\bigr),$$

with $0^0 = 1$.

Proof: We formalize the operator proof around equations `eq1`, `eq2'`, `eq4`, `meq`,
`pqexpn`, and `lasteq` in Oussi's paper, using formal power series in place of convergent series.

Source: L. Oussi, *A (p,q)-Deformed Recurrence for the Bell Numbers*, Journal of
Integer Sequences 23 (2020), Article 20.5.2, main theorem equation `lasteq`,
lines 214-220, <https://cs.uwaterloo.ca/journals/JIS/VOL23/Oussi/oussi5.tex>.

Proves `Wanted` entry `spivey_pq_bell`.
-/
public theorem spivey_pq_bell :
  ∀ (p q : ℝ) (hq0 : 0 < q) (hqp : q < p) (hp1 : p ≤ 1),
    let bracket : ℕ → ℝ := fun k => (p ^ k - q ^ k) / (p - q);
    let rec S : ℕ → ℕ → ℝ
      | 0 => fun k => if k = 0 then 1 else 0
      | (n + 1) => fun k => if k = 0 then 0
        else p ^ (n + 1 - k) * q ^ (k - 1) * S n (k - 1) + bracket k * S n k;
    let tildeS : ℕ → ℕ → ℝ := fun n k => p ^ Nat.choose k 2 * S n k;
    let tildeB : ℕ → ℝ → ℝ :=
      fun n x => ∑ k ∈ Finset.range (n + 1), tildeS n k * x ^ k;
    ∀ (m n : ℕ),
      tildeB (n + m) 1
        = ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
          (Nat.choose n j : ℝ) * tildeS m k * bracket k ^ (n - j)
            * q ^ (j * k) * tildeB j (p ^ (n + m - j)) := by
  intro p q hq0 hqp hp1 bracket tildeS tildeB m n
  have hpq : p ≠ q := ne_of_gt hqp
  have hbracket0 : bracket 0 = 0 := by simp [bracket]
  have hbracketAdd : ∀ k j, bracket (k + j) = p ^ j * bracket k + q ^ k * bracket j := by
    exact spivey_bracket_add p q hpq
  have hbracket_ne : ∀ k, 0 < k → bracket k ≠ 0 := by
    intro k hk
    exact ne_of_gt (spivey_bracket_pos p q hq0 hqp k hk)
  dsimp only [tildeB, tildeS]
  run_tac spivey_finish_public

end MetaMathlibExt
