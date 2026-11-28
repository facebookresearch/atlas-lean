/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Filter.AtTopBot.Basic
import MathlibExt.NumberTheory.ZeckendorfVariationOne

open Filter MetaMathlibExt

private def evenCylinder (i : ℕ) : Bool := decide (i = 3 ∨ i = 6)
private def oddCylinder (i : ℕ) : Bool := decide (i = 2 ∨ i = 4 ∨ i = 7)

private theorem evenCylinder_mem : evenCylinder ∈ zeckAdic := by
  refine mem_zeckAdic_iff.mpr ⟨by decide, by decide, ?_⟩
  intro i _ hi
  simp [evenCylinder] at hi ⊢
  omega

private theorem oddCylinder_mem : oddCylinder ∈ zeckAdic := by
  refine mem_zeckAdic_iff.mpr ⟨by decide, by decide, ?_⟩
  intro i _ hi
  simp [oddCylinder] at hi ⊢
  omega

private theorem stable_from {x : ℕ → Bool} {j : ℕ} (hj : 1 ≤ j)
    (hT : ∀ i > j, zeckOdometer x i = x i) :
    ∀ k ≥ j, zeckAdicTruncVariation 1 k x = zeckAdicTruncVariation 1 j x := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    simpa only [Function.iterate_one, hT (k + 1) (by omega), add_sub_cancel_right, ih] using
      zeckAdicTruncVariation_succ 1 x (hj.trans hk)

-- The lower pair (x₃,x₂) is (1,0), the first 00 is (x₅,x₄), and the one at x₆ survives.
example : evenCylinder 5 = false ∧ evenCylinder 4 = false ∧
    evenCylinder 3 = true ∧ evenCylinder 2 = false ∧
    zeckOdometer evenCylinder 6 = true ∧
    ∀ k ≥ 4, zeckAdicTruncVariation 1 k evenCylinder = zeckAdicTruncVariation 1 4 evenCylinder := by
  have hT (i : ℕ) (hi : 4 < i) : zeckOdometer evenCylinder i = evenCylinder i := by
    simpa only [Function.iterate_one] using
      zeckOdometer_iterate_high_digits evenCylinder_mem (ℓ := 2) (r := 1)
        (by decide) (by decide) (by decide) (by decide) i (by omega)
  exact ⟨by decide, by decide, by decide, by decide, (hT 6 (by decide)).trans (by decide),
    stable_from (by decide) hT⟩

-- The lower digits (x₄,x₃,x₂) are (1,0,1), and the first 00 is (x₆,x₅).
example : oddCylinder 6 = false ∧ oddCylinder 5 = false ∧ oddCylinder 4 = true ∧
    oddCylinder 3 = false ∧ oddCylinder 2 = true ∧
    zeckOdometer oddCylinder 7 = true ∧
    ∀ k ≥ 5, zeckAdicTruncVariation 1 k oddCylinder = zeckAdicTruncVariation 1 5 oddCylinder := by
  have hT (i : ℕ) (hi : 5 < i) : zeckOdometer oddCylinder i = oddCylinder i := by
    simpa only [Function.iterate_one] using
      zeckOdometer_iterate_high_digits oddCylinder_mem (ℓ := 3) (r := 1)
        (by decide) (by decide) (by decide) (by decide) i (by omega)
  exact ⟨by decide, by decide, by decide, by decide, by decide,
    (hT 7 (by decide)).trans (by decide), stable_from (by decide) hT⟩

-- At the empty alternating prefix (d = 0), the first zero pair is at digit 2 or 3.
example : zeckAdicTruncVariation 1 2 (fun _ => false) =
    zeckAdicTruncVariation 1 1 (fun _ => false) + 1 := by
  have hT : zeckOdometer (fun _ => false) 2 = true :=
    zeckOdometer_apply_eq_true_iff.mpr (Or.inl ⟨by decide, fun i hi h => by omega⟩)
  simpa [Function.iterate_one, hT] using
    zeckAdicTruncVariation_succ 1 (fun _ => false) (k := 1) le_rfl

example :
    zeckAdicTruncVariation 1 3 (fun i => decide (i = 2)) =
      zeckAdicTruncVariation 1 2 (fun i => decide (i = 2)) + 1 := by
  let x : ℕ → Bool := fun i => decide (i = 2)
  have hT : zeckOdometer x 3 = true := by
    refine zeckOdometer_apply_eq_true_iff.mpr (Or.inl ⟨by decide, ?_⟩)
    rintro i hi ⟨hi', h, -⟩
    obtain rfl : i = 2 := by omega
    simp [x] at h
  have hx : x 3 = false := by decide
  simpa only [Function.iterate_one, hT, hx, Bool.toNat_true, Bool.toNat_false, Nat.cast_one,
    Nat.cast_zero, sub_zero] using zeckAdicTruncVariation_succ 1 x (k := 2) (by decide)

private def alternating (p i : ℕ) : Bool := decide (2 ≤ i ∧ i % 2 = p)

-- For each phase (even or odd ones), no consecutive zeros occur above the unit digit,
-- and the truncated variation strictly decreases at arbitrarily large indices.
example (p : ℕ) (hp : p ≤ 1) : alternating p ∈ zeckAdic ∧
    (∀ i ≥ 2, alternating p i = true ∨ alternating p (i + 1) = true) ∧
    ¬ (∃ d, ∀ᶠ k in atTop, zeckAdicTruncVariation 1 k (alternating p) = d) := by
  have hmem : alternating p ∈ zeckAdic := by
    refine mem_zeckAdic_iff.mpr ⟨by simp [alternating], by simp [alternating], ?_⟩
    intro i _ hi
    simp [alternating] at hi ⊢
    omega
  have halt (i : ℕ) (hi : 2 ≤ i) : alternating p i = true ∨ alternating p (i + 1) = true := by
    simp [alternating, hi, show 2 ≤ i + 1 by omega]
    omega
  refine ⟨hmem, halt, ?_⟩
  rintro ⟨d, hd⟩
  obtain ⟨n, hn⟩ := eventually_atTop.mp hd
  let k := 2 * n + 3 + p
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hbit : alternating p (k + 1) = true := by
    simp only [alternating, decide_eq_true_eq]
    dsimp [k]
    omega
  have hno (i : ℕ) : ¬(2 ≤ i ∧ alternating p i = false ∧ alternating p (i + 1) = false) := by
    rintro ⟨hi, h₀, h₁⟩
    simpa [h₀, h₁] using halt i hi
  have hT : zeckOdometer (alternating p) (k + 1) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    rcases zeckOdometer_apply_eq_true_iff.mp ht with ⟨hs, -⟩ | ⟨-, i, -, hs⟩
    · exact hno (k + 1) hs
    · exact hno i hs
  have hstep := zeckAdicTruncVariation_succ 1 (alternating p) hk
  rw [Function.iterate_one, hT, hbit, hn (k + 1) (by dsimp [k]; omega),
    hn k (by dsimp [k]; omega)] at hstep
  simp at hstep
  omega

-- A concrete client of each cylinder-to-stabilization implication.
example : ∃ d, ∀ᶠ k in atTop, zeckAdicTruncVariation 1 k evenCylinder = d :=
  (zeckAdicVariation_one_exists_iff evenCylinder_mem).mpr ⟨1, Or.inl
    ⟨by decide, by decide, fun i hi hi' => by
      obtain rfl : i = 1 := by omega
      decide⟩⟩

example : ∃ d, ∀ᶠ k in atTop, zeckAdicTruncVariation 1 k oddCylinder = d :=
  (zeckAdicVariation_one_exists_iff oddCylinder_mem).mpr ⟨1, Or.inr
    ⟨by decide, by decide, by decide, fun i hi hi' => by
      obtain rfl : i = 1 := by omega
      decide⟩⟩
