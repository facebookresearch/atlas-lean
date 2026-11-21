/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

namespace Polynomial

/-!
# The p-adic valuation of an integer polynomial

For a nonzero polynomial over the integers, this file defines its `p`-adic valuation as the
minimum of the `p`-adic valuations of its nonzero coefficients.

The definition follows Itamar Nir, arXiv:2608.00668v1, line 419.
-/

/-- The minimum `p`-adic valuation of the nonzero coefficients of `f`. -/
@[nolint unusedArguments]
noncomputable def padicValuation (p : ℕ) (_hp : Nat.Prime p) (f : Polynomial ℤ) (hf : f ≠ 0) : ℕ :=
  (f.support.image (fun n => padicValInt p (f.coeff n))).min'
    ((support_nonempty.mpr hf).image fun n => padicValInt p (f.coeff n))

/-- The polynomial valuation is at most the valuation of every nonzero coefficient. -/
theorem padicValuation_le_coeff {p : ℕ} {hp : Nat.Prime p} {f : Polynomial ℤ} {hf : f ≠ 0}
    {n : ℕ} (hn : n ∈ f.support) :
    padicValuation p hp f hf ≤ padicValInt p (f.coeff n) := by
  unfold padicValuation
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem (fun n => padicValInt p (f.coeff n)) hn)

/-- Every common lower bound of the coefficient valuations bounds the polynomial valuation. -/
theorem le_padicValuation {p : ℕ} {hp : Nat.Prime p} {f : Polynomial ℤ} {hf : f ≠ 0}
    {k : ℕ} (hk : ∀ n ∈ f.support, k ≤ padicValInt p (f.coeff n)) :
    k ≤ padicValuation p hp f hf := by
  unfold padicValuation
  apply Finset.le_min'
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨n, hn, rfl⟩ := hy
  exact hk n hn

/-- The polynomial valuation of a nonzero constant is its integer valuation. -/
@[simp]
theorem padicValuation_C (p : ℕ) (hp : Nat.Prime p) (a : ℤ) (ha : a ≠ 0) :
    padicValuation p hp (C a) (C_ne_zero.mpr ha) = padicValInt p a := by
  apply le_antisymm
  · have h0 : 0 ∈ (C a : Polynomial ℤ).support := by
      rw [support_C ha]
      exact Finset.mem_singleton_self 0
    calc
      padicValuation p hp (C a) (C_ne_zero.mpr ha) ≤ padicValInt p ((C a).coeff 0) :=
        padicValuation_le_coeff h0
      _ = padicValInt p a := by rw [coeff_C_zero]
  · apply le_padicValuation
    intro n hn
    rw [support_C ha] at hn
    rw [Finset.mem_singleton.mp hn, coeff_C_zero]

end Polynomial
