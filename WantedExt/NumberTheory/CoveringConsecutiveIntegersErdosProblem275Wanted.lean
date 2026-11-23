/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Covering `2^r` consecutive integers (Erdős Problem 275)

Erdős Problem 275: if a finite system of `r` congruences `a_i (mod n_i)` (the `n_i` not necessarily
distinct) covers `2^r` consecutive integers, then it covers all integers.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.ModEq

@[expose] public section

namespace MathlibExt.NumberTheory.CoveringConsecutiveIntegersErdosProblem275Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #275, https://www.erdosproblems.com/275 (status PROVED
(LEAN)). UnsolvedMath record UM-30006801 (`EP-275`), dataset ulamai/UnsolvedMath v1.8.0.

The moduli are positive integers (a congruence modulo `0` is not a congruence class).
formal-conjectures `ErdosProblems/275.lean` omits positivity, a stronger form; this module keeps the
hypothesis of the source (no code imported).
-/

/-- Erdős Problem 275: if `r` congruences `x ≡ a i (mod n i)` (moduli positive, not necessarily
distinct) cover `2 ^ r` consecutive integers, then they cover all integers. -/
def coveringConsecutiveCoversAll : Prop :=
  ∀ (r : ℕ) (a : Fin r → ℤ) (n : Fin r → ℕ), (∀ i, 0 < n i) →
    (∃ k : ℤ, ∀ x : ℤ, k ≤ x → x < k + 2 ^ r → ∃ i, x ≡ a i [ZMOD n i]) →
      ∀ x : ℤ, ∃ i, x ≡ a i [ZMOD n i]

/--
Resolved true: Crittenden and Vanden Eynden (and independently Selfridge) proved that `r` arithmetic
progressions covering `2^r` consecutive integers cover all integers. erdosproblems.com/275 lists the
problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #275,
https://www.erdosproblems.com/275 (status PROVED (LEAN)); resolution: R. B. Crittenden and C. L.
Vanden Eynden, Any n arithmetic progressions covering the first 2^n integers cover all integers,
Proc. Amer. Math. Soc. (1970), 475-481, main theorem (the title); erdosproblems.com/275: proved
independently by Selfridge and by Crittenden and Vanden Eynden, best possible by 2^{i-1} (mod 2^i);
simpler proof by Balister, Bollobás, Morris, Sahasrabudhe and Tiba, Acta Math. Hungar. (2020),
197-200, https://www.erdosproblems.com/275.
-/
public theorem_wanted coveringConsecutiveCoversAll_holds : coveringConsecutiveCoversAll

end MathlibExt.NumberTheory.CoveringConsecutiveIntegersErdosProblem275Wanted
