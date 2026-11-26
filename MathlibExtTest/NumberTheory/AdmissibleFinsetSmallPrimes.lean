/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.AdmissibleFinsetSmallPrimes

/-!
# Tests for the small-prime criterion for admissibility
-/

namespace MetaMathlibExt.Test.AdmissibleFinsetSmallPrimes

open MetaMathlibExt

/-- Maynard's admissible 5-tuple `{0, 2, 6, 8, 12}` (arXiv:1311.4600v3, Section 4). -/
example : IsAdmissibleFinset ({0, 2, 6, 8, 12} : Finset ℤ) := by decide

/-- The GPY 6-tuple `{0, 4, 6, 10, 12, 16}` (arXiv:math/0508185v1, after Theorem 1). -/
example : IsAdmissibleFinset ({0, 4, 6, 10, 12, 16} : Finset ℤ) := by decide

/-- Maynard's admissible 105-tuple of diameter 600 (arXiv:1311.4600v3, footnote 2 in Section 4,
taken there from Sutherland's tables). Only the primes `p ≤ 105` are checked. -/
example : IsAdmissibleFinset ({
    0, 10, 12, 24, 28, 30, 34, 42, 48, 52, 54, 64, 70, 72, 78, 82, 90, 94, 100, 112, 114, 118,
    120, 124, 132, 138, 148, 154, 168, 174, 178, 180, 184, 190, 192, 202, 204, 208, 220, 222,
    232, 234, 250, 252, 258, 262, 264, 268, 280, 288, 294, 300, 310, 322, 324, 328, 330, 334,
    342, 352, 358, 360, 364, 372, 378, 384, 390, 394, 400, 402, 408, 412, 418, 420, 430, 432,
    442, 444, 450, 454, 462, 468, 472, 478, 484, 490, 492, 498, 504, 510, 528, 532, 534, 538,
    544, 558, 562, 570, 574, 580, 582, 588, 594, 598, 600} : Finset ℤ) := by
  decide +kernel

/-- `{0, 2, 4}` covers every class modulo 3, so it is not admissible. -/
example : ¬ IsAdmissibleFinset ({0, 2, 4} : Finset ℤ) := by decide

/-- `{0, 1}` covers both classes modulo 2. -/
example : ¬ IsAdmissibleFinset ({0, 1} : Finset ℤ) := by decide

/-- Degenerate cases: the empty set and singletons are admissible. -/
example : IsAdmissibleFinset (∅ : Finset ℤ) := by decide
example : IsAdmissibleFinset ({7} : Finset ℤ) := by decide

/-- The criterion only asks about primes up to the size of the set. -/
example (H : Finset ℤ) (hH : ∀ p : ℕ, p.Prime → p ≤ H.card →
    ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r) : IsAdmissibleFinset H :=
  (isAdmissibleFinset_iff_forall_prime_le_card H).mpr hH

end MetaMathlibExt.Test.AdmissibleFinsetSmallPrimes
