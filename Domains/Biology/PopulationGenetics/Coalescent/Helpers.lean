/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Consistency and complete monotonicity of merger rates

For an array `r b k` satisfying Pitman's consistency relation
`r b k = r (b + 1) k + r (b + 1) (k + 1)` for `2 ≤ k ≤ b`, write `m i = r (i + 2) (i + 2)` and
let `E` be the shift `(E g) i = g (i + 1)`. Then `r (i + 2 + c) (i + 2) = ((I - E) ^ c m) i`; if
moreover `r ≥ 0` on `2 ≤ k ≤ b`, the sequence `m` is completely monotone: `(-1) ^ c Δ^c m ≥ 0`,
with `Δ` the forward difference `fwdDiff 1`.

## References

* J. Pitman, "Coalescents with multiple collisions", *Annals of Probability* 27 (1999),
  1870–1902.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent

/-- `I - E` is `-Δ`, so `(I - E) ^ c = (-1) ^ c Δ ^ c` (Mathlib's `fwdDiff 1`). -/
theorem iterate_sub_shift_eq_neg_one_pow_mul_fwdDiff_iter (m : ℕ → ℝ) (c i : ℕ) :
    (fun g : ℕ → ℝ => fun j => g j - g (j + 1))^[c] m i =
      (-1) ^ c * (fwdDiff 1)^[c] m i := by
  induction c generalizing i with
  | zero => simp
  | succ c ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [ih i, ih (i + 1)]
    simp only [fwdDiff]
    ring

/-- **Consistency unrolls along a row**: for an array `r` satisfying Pitman's consistency
relation for `2 ≤ k ≤ b`, `r (i + 2 + c) (i + 2) = ((I - E) ^ c m) i` with
`m j = r (j + 2) (j + 2)`. -/
theorem consistent_eq_iterate_sub_shift (r : ℕ → ℕ → ℝ)
    (hcons : ∀ b k, 2 ≤ k → k ≤ b → r b k = r (b + 1) k + r (b + 1) (k + 1)) (i c : ℕ) :
    r (i + 2 + c) (i + 2) =
      (fun g : ℕ → ℝ => fun j => g j - g (j + 1))^[c] (fun j => r (j + 2) (j + 2)) i := by
  induction c generalizing i with
  | zero => simp
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    rw [← ih i, ← ih (i + 1)]
    have h := hcons (i + 2 + c) (i + 2) (by omega) (by omega)
    rw [show i + 1 + 2 + c = i + 2 + c + 1 by omega, show i + 1 + 2 = i + 2 + 1 by omega,
      show i + 2 + (c + 1) = i + 2 + c + 1 by omega]
    linarith

/-- **Complete monotonicity of the diagonal rates**: nonnegative consistent rates have
`(-1) ^ c Δ ^ c m ≥ 0` for every `c` and `i`, where `m j = r (j + 2) (j + 2)`. -/
theorem completelyMonotone_diag_of_consistent (r : ℕ → ℕ → ℝ)
    (hnn : ∀ b k, 2 ≤ k → k ≤ b → 0 ≤ r b k)
    (hcons : ∀ b k, 2 ≤ k → k ≤ b → r b k = r (b + 1) k + r (b + 1) (k + 1)) (i c : ℕ) :
    0 ≤ (-1) ^ c * (fwdDiff 1)^[c] (fun j => r (j + 2) (j + 2)) i := by
  rw [← iterate_sub_shift_eq_neg_one_pow_mul_fwdDiff_iter,
    ← consistent_eq_iterate_sub_shift r hcons]
  exact hnn _ _ (by omega) (by omega)

end MathlibExt.Biology.PopulationGenetics.Coalescent
