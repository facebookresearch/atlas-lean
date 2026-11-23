/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.GreensOperator
import Mathlib.Tactic.Ring

/-!
# Tail bound for finite sums in the sine Hilbert basis

For the sine Hilbert basis of `L²([0, 1])`
(`MathlibExt.Analysis.ODE.GreensOperator.sineHilbertBasis`, indexed
by positive mode number), the squared norm of a tail of a finite
modal sum is at most the squared norm of the full sum: with
zero-based coefficient indices the full sum runs over
`k ∈ Finset.Ico 0 K` (modes `1 .. K`, coefficient `c k` on mode
`k + 1`) and the tail over `k ∈ Finset.Ico N K` (modes
`N + 1 .. K`). The finite Parseval identity behind this is
Mathlib's `Orthonormal.inner_sum`; each modal contribution is
`(c k)^2 ≥ 0`. This is the displacement-tail bound used by
finite-mode beam truncation consumers, whose fixed-time modal
coefficients already contain the initial-velocity contribution
divided by the modal frequency.

## Main results

* `MathlibExt.Analysis.ODE.SineBasisTail.sineBasis_tail_norm_sq_le`:
  the tail bound above.
-/

@[expose] public section

namespace MathlibExt.Analysis.ODE.SineBasisTail

/-- Tail bound for the sine Hilbert basis on `L²([0, 1])`: the
squared norm of the tail modes `N + 1 .. K` of a finite modal sum
is at most that of the full sum over modes `1 .. K`. -/
theorem sineBasis_tail_norm_sq_le (c : ℕ → ℝ) {N K : ℕ} (hNK : N ≤ K) :
    ‖∑ k ∈ Finset.Ico N K,
        c k • MathlibExt.Analysis.ODE.GreensOperator.sineHilbertBasis
          ⟨k + 1, Nat.succ_pos k⟩‖ ^ 2 ≤
      ‖∑ k ∈ Finset.Ico 0 K,
        c k • MathlibExt.Analysis.ODE.GreensOperator.sineHilbertBasis
          ⟨k + 1, Nat.succ_pos k⟩‖ ^ 2 := by
  have he : Orthonormal ℝ (fun k : ℕ =>
      MathlibExt.Analysis.ODE.GreensOperator.sineHilbertBasis
        ⟨k + 1, Nat.succ_pos k⟩) :=
    MathlibExt.Analysis.ODE.GreensOperator.sineHilbertBasis.orthonormal.comp
      (fun n : ℕ => (⟨n + 1, Nat.succ_pos n⟩ : ℕ+))
      (fun a b h => by
        simpa using congrArg (fun p : ℕ+ => (p : ℕ)) h)
  have key : ∀ s : Finset ℕ,
      ‖∑ k ∈ s, c k • MathlibExt.Analysis.ODE.GreensOperator.sineHilbertBasis
        ⟨k + 1, Nat.succ_pos k⟩‖ ^ 2 = ∑ k ∈ s, c k ^ 2 := by
    intro s
    have h := Orthonormal.inner_sum he c c s
    rw [real_inner_self_eq_norm_sq] at h
    refine h.trans ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [RCLike.conj_to_real, pow_two]
  rw [key, key]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ico_subset_Ico (Nat.zero_le N) le_rfl) (fun k _ _ => sq_nonneg _)

end MathlibExt.Analysis.ODE.SineBasisTail
