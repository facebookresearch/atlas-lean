/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Adapted from eth/proof/networks/Groundwork/Net/Colouring.lean in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
generalize the source's finite-type moment bounds to arbitrary finite sets.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

/-!
# Finite count bounds from moments

Denominator-cleared first- and second-moment identities bound the number of
elements of a finite set on which a function meets or exceeds a threshold. All forms
remain valid when the finite set or any denominator-clearing factor is zero.
-/

@[expose] public section

namespace Finset

/-- The number of points where a function is at least a nonnegative threshold,
times the threshold squared, is at most the sum of squares. -/
theorem card_filter_mul_sq_le_sum_sq {Ω : Type*} (S : Finset Ω) (f : Ω → ℤ)
    (s : ℤ) (hs : 0 ≤ s) :
    ((S.filter fun x => s ≤ f x).card : ℤ) * s ^ 2 ≤ ∑ x ∈ S, f x ^ 2 := by
  calc
    ((S.filter fun x => s ≤ f x).card : ℤ) * s ^ 2 =
        ∑ x ∈ S with s ≤ f x, s ^ 2 := by
      simp [sum_const]
    _ ≤ ∑ x ∈ S with s ≤ f x, f x ^ 2 :=
      sum_le_sum fun x hx => pow_le_pow_left₀ hs (mem_filter.1 hx).2 2
    _ ≤ ∑ x ∈ S, f x ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _

/-- A denominator-cleared finite count bound from first and second moments.

Neither the finite set nor `A`, `t`, or `s` is required to be nonzero. -/
theorem card_filter_mul_sq_le_of_moments {Ω : Type*} (S : Finset Ω) (Y : Ω → ℕ)
    (A m V t s : ℕ)
    (S1 : (∑ x ∈ S, Y x) * A = S.card * m)
    (S2 : (∑ x ∈ S, Y x ^ 2) * A ^ 2 ≤ S.card * m ^ 2 + V) :
    (S.filter fun x => t * m + s ≤ t * (A * Y x)).card * s ^ 2 ≤ t ^ 2 * V := by
  have hc := card_filter_mul_sq_le_sum_sq S
    (fun x => (t : ℤ) * ((A : ℤ) * Y x - m)) s (by positivity)
  have hsub : (S.filter fun x => t * m + s ≤ t * (A * Y x)).card ≤
      (S.filter fun x => (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * Y x - m)).card := by
    refine card_le_card fun x hx => ?_
    simp only [mem_filter] at hx ⊢
    exact ⟨hx.1, by zify at hx; linarith⟩
  have key : ∀ B : ℕ,
      B ≤ (S.filter fun x => (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * Y x - m)).card →
        B * s ^ 2 ≤ t ^ 2 * V := by
    intro B hB
    have hB' : (B : ℤ) ≤
        ((S.filter fun x => (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * Y x - m)).card : ℤ) :=
      Nat.cast_le.2 hB
    zify at S1 S2
    have hsum : ∑ x ∈ S, ((t : ℤ) * ((A : ℤ) * Y x - m)) ^ 2 =
        (t : ℤ) ^ 2 * ((∑ x ∈ S, (Y x : ℤ) ^ 2) * A ^ 2 -
          2 * m * ((∑ x ∈ S, (Y x : ℤ)) * A) + (S.card : ℤ) * m ^ 2) := by
      have hterm : ∀ x : Ω, ((t : ℤ) * ((A : ℤ) * Y x - m)) ^ 2 =
          (t : ℤ) ^ 2 * ((Y x : ℤ) ^ 2 * A ^ 2 -
            2 * m * ((Y x : ℤ) * A) + (m : ℤ) ^ 2) := by
        intro x
        ring
      simp only [hterm, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum,
        sum_const, nsmul_eq_mul]
    rw [hsum, S1] at hc
    have hcount : (B : ℤ) * (s : ℤ) ^ 2 ≤
        ((S.filter fun x => (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * Y x - m)).card : ℤ) *
          (s : ℤ) ^ 2 :=
      mul_le_mul_of_nonneg_right hB' (sq_nonneg _)
    have hmoment : (t : ℤ) ^ 2 *
        ((∑ x ∈ S, (Y x : ℤ) ^ 2) * A ^ 2 -
          2 * m * ((S.card : ℤ) * m) + (S.card : ℤ) * m ^ 2) ≤
        (t : ℤ) ^ 2 * V :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    have hfinal : (B : ℤ) * (s : ℤ) ^ 2 ≤ (t : ℤ) ^ 2 * V :=
      hcount.trans (hc.trans hmoment)
    exact_mod_cast hfinal
  exact key _ hsub

/-- `card_filter_mul_sq_le_sum_sq` specialized to the universal finset. -/
theorem card_filter_mul_sq_le_sum_sq_univ {Ω : Type*} [Fintype Ω]
    (f : Ω → ℤ) (s : ℤ) (hs : 0 ≤ s) :
    (#{x : Ω | s ≤ f x} : ℤ) * s ^ 2 ≤ ∑ x, f x ^ 2 := by
  simpa only using card_filter_mul_sq_le_sum_sq (univ : Finset Ω) f s hs

/-- `card_filter_mul_sq_le_of_moments` specialized to the universal finset. -/
theorem card_filter_mul_sq_le_of_moments_univ {Ω : Type*} [Fintype Ω]
    (Y : Ω → ℕ) (A m V t s : ℕ)
    (S1 : (∑ x, Y x) * A = Fintype.card Ω * m)
    (S2 : (∑ x, Y x ^ 2) * A ^ 2 ≤ Fintype.card Ω * m ^ 2 + V) :
    #{x : Ω | t * m + s ≤ t * (A * Y x)} * s ^ 2 ≤ t ^ 2 * V := by
  simpa only [card_univ] using
    card_filter_mul_sq_le_of_moments (univ : Finset Ω) Y A m V t s S1 S2

end Finset
