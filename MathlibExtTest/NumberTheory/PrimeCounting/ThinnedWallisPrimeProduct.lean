/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.ThinnedWallisPrimeProduct

/-!
# Tests for the convergence of thinned Wallis-type prime products

Each example applies `MetaMathlibExt.thinned_wallis_prime_product_tendsto_pos_iff` to an explicit
set of residues modulo `4` or `8`, in both directions of the criterion.
-/

open Filter Topology MetaMathlibExt

/-- Modulo `4`, the classes `1` and `3` have `μ(S) = 1 - 1 = 0`: the Wallis-type product over all
odd primes converges to a positive limit. -/
example : ∃ L : ℝ, 0 < L ∧
    Tendsto (fun x : ℝ =>
        ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
            (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ 2)) ∈ ({1, 3} : Finset (ZMod (2 ^ 2)))),
          ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)))
      atTop (𝓝 L) :=
  (thinned_wallis_prime_product_tendsto_pos_iff 2 le_rfl {1, 3} (by decide)).mpr (by decide)

/-- The empty set of residues gives the empty product, with `μ(∅) = 0`. -/
example : ∃ L : ℝ, 0 < L ∧
    Tendsto (fun x : ℝ =>
        ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
            (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ 3)) ∈ (∅ : Finset (ZMod (2 ^ 3)))),
          ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)))
      atTop (𝓝 L) :=
  (thinned_wallis_prime_product_tendsto_pos_iff 3 (by decide) ∅ (by decide)).mpr (by decide)

/-- Modulo `4`, the class `1` alone has `μ(S) = 1 ≠ 0`: the product of `(p - 1) / (p + 1)` over
the primes `p ≡ 1 (mod 4)` has no positive limit. -/
example : ¬ ∃ L : ℝ, 0 < L ∧
    Tendsto (fun x : ℝ =>
        ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
            (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ 2)) ∈ ({1} : Finset (ZMod (2 ^ 2)))),
          ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)))
      atTop (𝓝 L) := by
  rw [thinned_wallis_prime_product_tendsto_pos_iff 2 le_rfl {1} (by decide)]
  decide

/-- Modulo `4`, the class `3` alone has `μ(S) = -1 ≠ 0`: the product of `(p + 1) / (p - 1)` over
the primes `p ≡ 3 (mod 4)` has no positive limit. -/
example : ¬ ∃ L : ℝ, 0 < L ∧
    Tendsto (fun x : ℝ =>
        ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
            (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ 2)) ∈ ({3} : Finset (ZMod (2 ^ 2)))),
          ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)))
      atTop (𝓝 L) := by
  rw [thinned_wallis_prime_product_tendsto_pos_iff 2 le_rfl {3} (by decide)]
  decide

/-- Modulo `8`, the classes `1` and `3` have `μ(S) = 0`, so the thinned product converges to a
positive limit. -/
example : ∃ L : ℝ, 0 < L ∧
    Tendsto (fun x : ℝ =>
        ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
            (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ 3)) ∈ ({1, 3} : Finset (ZMod (2 ^ 3)))),
          ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)))
      atTop (𝓝 L) :=
  (thinned_wallis_prime_product_tendsto_pos_iff 3 (by decide) {1, 3} (by decide)).mpr
    (by decide)

/-- Modulo `8`, the classes `1` and `5` are both `1` modulo `4`, so `μ(S) = 2 ≠ 0` and the
thinned product has no positive limit. -/
example : ¬ ∃ L : ℝ, 0 < L ∧
    Tendsto (fun x : ℝ =>
        ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
            (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ 3)) ∈ ({1, 5} : Finset (ZMod (2 ^ 3)))),
          ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)))
      atTop (𝓝 L) := by
  rw [thinned_wallis_prime_product_tendsto_pos_iff 3 (by decide) {1, 5} (by decide)]
  decide
