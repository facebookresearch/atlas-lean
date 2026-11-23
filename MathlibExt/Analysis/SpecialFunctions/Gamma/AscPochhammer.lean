/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Provenance: `Real.Gamma_add_nat_eq` is adapted from `ProbabilityTheory.Gamma_add_nat_eq`, which
Adam Kiezun added to `MathlibExt/Probability/Distributions/Gamma.lean` in
`facebookresearch/atlas-lean` PR #765 (commit `ab014778cafb7560f58a16350a29f0ca8daabb9b`), as of
immutable atlas-lean commit `18d1aa399b6ebaa8cd9c4a48795b43f6734c3785`. Adaptations: it lives in
the `Real` namespace, the step count `k` comes first, and the hypothesis `0 < a` is weakened to
`∀ j < k, a + j ≠ 0`. The Meta Platforms notice above is that source file's header, preserved
verbatim.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The real Gamma function at natural shifts

`Real.Gamma_add_nat_eq`: `Γ(a + k) = a⁽ᵏ⁾ Γ(a)`, where `a⁽ᵏ⁾ = a (a + 1) ⋯ (a + k - 1)` is the
ascending Pochhammer symbol, whenever no `a + j` with `j < k` is zero. This is the real
counterpart of Mathlib's `Complex.Gamma_add_nat_div_Gamma_eq`.
-/

@[expose] public section

namespace Real

/-- `Γ(a + k) = a⁽ᵏ⁾ Γ(a)`, with `a⁽ᵏ⁾ = a (a + 1) ⋯ (a + k - 1)` the ascending Pochhammer
symbol, provided `a + j ≠ 0` for every natural `j < k` (for instance when `0 < a`). Only the
shifts `a, a + 1, …, a + k - 1` that the recursion passes through are constrained, so `a` may
be a nonpositive integer as long as `a + k ≤ 0`. -/
theorem Gamma_add_nat_eq {a : ℝ} (k : ℕ) (ha : ∀ j < k, a + j ≠ 0) :
    Gamma (a + k) = (ascPochhammer ℝ k).eval a * Gamma a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, Gamma_add_one (ha k k.lt_succ_self),
      ih fun j hj => ha j (Nat.lt_succ_of_lt hj), ascPochhammer_succ_eval]
    ring

end Real
