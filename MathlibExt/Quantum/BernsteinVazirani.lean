/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

/-!
# Bernstein-Vazirani amplitude identity

For bitvectors, the character `(-1)^{x·s}` summed over all
inputs is `2^n` when the two characters agree and `0`
otherwise. Applied to the phase oracle of an affine function
with hidden string `s`, the final Hadamard amplitude of the
Bernstein-Vazirani algorithm is concentrated on `s`.
-/

@[expose] public section

/-- Character `(-1)^{x·s}` for bitvectors (BV core of QCI-14). -/
def chi {n : ℕ} (x s : Fin n → Bool) : ℂ :=
  ∏ i, (if s i then (if x i then -1 else 1) else 1)

/-- Character orthogonality: summing over all inputs gives
`2^n` when the characters agree and `0` otherwise. -/
theorem chi_sum {n : ℕ} (s t : Fin n → Bool) :
    ∑ x : Fin n → Bool, chi x s * chi x t
      = if s = t then (2 : ℂ) ^ n else 0 := by
  have hfactor : ∀ (a b : Bool),
      (∑ y : Bool, (if a then (if y then (-1 : ℂ) else 1) else 1) *
        (if b then (if y then (-1 : ℂ) else 1) else 1))
        = if a = b then 2 else 0 := by
    intro a b
    cases a <;> cases b <;> norm_num [Fintype.univ_bool, Finset.sum_insert, Finset.sum_singleton]
  have hprod : ∀ x : Fin n → Bool, chi x s * chi x t
      = ∏ i, ((if s i then (if x i then (-1 : ℂ) else 1) else 1) *
        (if t i then (if x i then (-1 : ℂ) else 1) else 1)) := by
    intro x
    unfold chi
    rw [← Finset.prod_mul_distrib]
  calc (∑ x : Fin n → Bool, chi x s * chi x t)
      = ∑ x, ∏ i, ((if s i then (if x i then (-1 : ℂ) else 1) else 1) *
        (if t i then (if x i then (-1 : ℂ) else 1) else 1)) :=
        Finset.sum_congr rfl (fun x _ => hprod x)
    _ = ∏ i, ∑ y : Bool, ((if s i then (if y then (-1 : ℂ) else 1) else 1) *
        (if t i then (if y then (-1 : ℂ) else 1) else 1)) :=
        (Fintype.prod_sum (fun (i : Fin n) (y : Bool) =>
          ((if s i then (if y then (-1 : ℂ) else 1) else 1) *
            (if t i then (if y then (-1 : ℂ) else 1) else 1)))).symm
    _ = ∏ i, (if s i = t i then (2 : ℂ) else 0) :=
        Finset.prod_congr rfl (fun i _ => hfactor (s i) (t i))
    _ = if s = t then (2 : ℂ) ^ n else 0 := by
        by_cases h : s = t
        · subst h
          simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        · rw [ite_eq_right h]
          obtain ⟨i, hi⟩ := Function.ne_iff.mp h
          exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Phase of an affine function `f x = (x·s) XOR β`, as a sign. -/
def affinePhase {n : ℕ} (s : Fin n → Bool) (β : Bool) (x : Fin n → Bool) : ℂ :=
  (if β then -1 else 1) * chi x s

/-- Bernstein-Vazirani amplitude: with the phase oracle for
the affine function with hidden string `s`, the final
Hadamard amplitude at `t` is a sign when `t = s` and `0`
otherwise. -/
theorem bv_amplitude {n : ℕ} (s t : Fin n → Bool) (β : Bool) :
    ((2 : ℂ) ^ n)⁻¹ * ∑ x : Fin n → Bool, chi x t * affinePhase s β x
      = if t = s then (if β then -1 else 1) else 0 := by
  have hfactor : ∀ x : Fin n → Bool, chi x t * affinePhase s β x
      = (if β then (-1 : ℂ) else 1) * (chi x t * chi x s) := by
    intro x
    unfold affinePhase
    ring
  have hsum : (∑ x : Fin n → Bool, chi x t * affinePhase s β x)
      = (if β then (-1 : ℂ) else 1) * (∑ x : Fin n → Bool, chi x t * chi x s) := by
    rw [Finset.sum_congr rfl (fun x _ => hfactor x)]
    rw [← Finset.mul_sum]
  rw [hsum, chi_sum]
  by_cases h : t = s
  · simp only [ite_eq_left h]
    have h2 : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
    field_simp
  · simp only [ite_eq_right h, mul_zero]

end
