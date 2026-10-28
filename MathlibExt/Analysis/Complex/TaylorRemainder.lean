/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Taylor expansion with a holomorphic remainder

If `f` is complex differentiable on a neighbourhood `U` of `a` (not necessarily open), then for
every `n` it can be written as `f s = ∑_{j < n} b j (s - a) ^ j + (s - a) ^ n g s` on `U`, with
`g` complex differentiable on `U`. The remainder comes from iterating `dslope`.

## Main statements

* `DifferentiableOn.exists_eq_sum_add_pow_mul`: the expansion above.
-/

@[expose] public section

/-- **Taylor expansion with a holomorphic remainder.** If `f` is complex differentiable on a
neighbourhood `U` of `a`, then for every `n` there are coefficients `b 0, …, b (n - 1)` and a
function `g` complex differentiable on `U` with
`f s = ∑_{j < n} b j * (s - a) ^ j + (s - a) ^ n * g s` for all `s ∈ U`. -/
theorem DifferentiableOn.exists_eq_sum_add_pow_mul {U : Set ℂ} {a : ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : U ∈ nhds a) (n : ℕ) :
    ∃ b : ℕ → ℂ, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      ∀ s ∈ U, f s = (∑ j ∈ Finset.range n, b j * (s - a) ^ j) + (s - a) ^ n * g s := by
  induction n with
  | zero => exact ⟨fun _ => 0, f, hf, fun s _ => by simp⟩
  | succ n ih =>
    obtain ⟨b, g, hg, hfg⟩ := ih
    refine ⟨Function.update b n (g a), dslope g a,
      (Complex.differentiableOn_dslope hU).mpr hg, fun s hs => ?_⟩
    have h : (s - a) * dslope g a s = g s - g a := by
      simpa using sub_smul_dslope g a s
    have hsum : ∑ j ∈ Finset.range (n + 1), (Function.update b n (g a)) j * (s - a) ^ j
        = (∑ j ∈ Finset.range n, b j * (s - a) ^ j) + g a * (s - a) ^ n := by
      rw [Finset.sum_range_succ, Function.update_self]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.mem_range.mp hj).ne]
    rw [hsum, hfg s hs]
    linear_combination (-((s - a) ^ n)) * h
