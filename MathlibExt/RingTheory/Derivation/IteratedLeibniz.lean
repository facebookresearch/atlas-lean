/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Adapted from https://github.com/anthropics/formal-math
at commit 16a5ce41304fcdaea4e0be7c132e1c361dc26da5,
eth/proof/rates/GeneralPieces/GenF/Taylor.lean.
-/

/- Modifications copyright (c) Meta Platforms, Inc. and affiliates. -/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Iterated Leibniz rule

This file gives the product rule for an iterated `Derivation`, with its natural binomial
weights. For rational algebras it also gives the factorial-normalized source formula.
-/

@[expose] public section

namespace Derivation

variable {R B : Type*} [CommSemiring R] [CommRing B] [Algebra R B]

/-- Leibniz's rule for an iterated derivation. The natural weights are not cancelled, so the
identity remains valid in positive characteristic. -/
theorem iterate_mul (D : Derivation R B B) (n : ℕ) (a b : B) :
    (D : B → B)^[n] (a * b) =
      ∑ p ∈ Finset.antidiagonal n,
        n.choose p.1 • ((D : B → B)^[p.1] a * (D : B → B)^[p.2] b) := by
  have hD : ∀ x y : B, D (x * y) = x * D y + D x * y := by
    intro x y
    rw [D.leibniz]
    simp [smul_eq_mul, mul_comm]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i j => (D : B → B)^[i] a * (D : B → B)^[j] b) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, hD, nsmul_add,
      Finset.sum_add_distrib, add_right_inj]
    refine Finset.sum_congr rfl fun ⟨i, j⟩ hij => ?_
    rw [n.choose_symm_of_eq_add (Finset.mem_antidiagonal.mp hij).symm]

variable [Algebra ℚ B]

/-- The factorial-normalized iterated Leibniz rule for a rational derivation. -/
theorem iterate_mul_div (D : Derivation ℚ B B) (n : ℕ) (a b : B) :
    ((n.factorial : ℚ)⁻¹) • (D : B → B)^[n] (a * b) =
      ∑ p ∈ Finset.antidiagonal n,
        ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) •
          ((D : B → B)^[p.1] a * (D : B → B)^[p.2] b) := by
  rw [D.iterate_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hn := Finset.mem_antidiagonal.mp hp
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  have h := Nat.add_choose_mul_factorial_mul_factorial p.1 p.2
  rw [hn, ← Nat.choose_symm_of_eq_add hn.symm] at h
  have h' : ((n.choose p.1 : ℕ) : ℚ) * p.1.factorial * p.2.factorial = n.factorial := by
    exact_mod_cast h
  have h3 : (n.factorial : ℚ) ≠ 0 := by positivity
  have hc : ((n.choose p.1 : ℕ) : ℚ) ≠ 0 := by
    intro hc
    rw [hc] at h'
    simp only [zero_mul] at h'
    exact h3 h'.symm
  rw [← h']
  simp [mul_inv_rev, hc, mul_assoc, mul_comm]

end Derivation
