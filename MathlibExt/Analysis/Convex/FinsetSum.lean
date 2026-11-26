/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Basic.Real.Basic

/-!
# Finite sums of convex functions are convex

Pinned Mathlib has `ConvexOn.add` but no lemma for a sum over a `Finset`; this file provides it.
It is the simplest of the operations that preserve convexity (Boyd–Vandenberghe §3.2.1), and it is
used for Lagrangians, empirical risks and regularized losses.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.FinsetSum

/-- **Finite sums of convex functions are convex.** If `s` is convex and every `g i`, `i ∈ t`, is
convex on `s`, then `x ↦ ∑ i ∈ t, g i x` is convex on `s` (the empty sum is the constant `0`).

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§3.2.1 ("Nonnegative weighted sums"). -/
theorem convexOn_finset_sum {E κ : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E}
    (hs : Convex ℝ s) {g : κ → E → ℝ} (t : Finset κ) (hg : ∀ i ∈ t, ConvexOn ℝ s (g i)) :
    ConvexOn ℝ s (fun x => ∑ i ∈ t, g i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using convexOn_const (0 : ℝ) hs
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self a t)).add
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

end MathlibExt.Analysis.Convex.FinsetSum
