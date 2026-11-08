/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Data.Set.Piecewise

@[expose] public section

open Set

namespace MathlibExt.Analysis.Calculus.PiecewiseContDiffWanted

/-- Gluing lemma for piecewise `C^n` functions on adjacent closed intervals: if
`f` is `C^n` on `[a, b]`, `g` is `C^n` on `[b, c]`, and all iterated derivatives
up to order `n` agree at the junction point `b`, then the piecewise function
(equal to `f` on `[a, b]` and to `g` elsewhere) is `C^n` on `[a, c]`. Mathlib
only has gluing over open unions (`ContDiffOn.union_of_isOpen`).

Sources:
- Mathlib `docs/undergrad.yaml`, section "Single Variable Real Analysis /
  Differentiability", entry "piecewise $C^k$ functions" (currently missing:
  external URL, no Mathlib declaration).
- https://en.wikipedia.org/wiki/Piecewise#Continuity_and_differentiability_of_piecewise_functions
-/
public theorem_wanted contDiffOn_piecewise_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    {f g : ℝ → E}
    (hf : ContDiffOn ℝ n f (Icc a b)) (hg : ContDiffOn ℝ n g (Icc b c))
    (hjets : ∀ k : ℕ, (k : ℕ∞) ≤ n →
      iteratedDerivWithin k f (Icc a b) b =
        iteratedDerivWithin k g (Icc b c) b) :
    ContDiffOn ℝ n (Set.piecewise (Icc a b) f g) (Icc a c)

end MathlibExt.Analysis.Calculus.PiecewiseContDiffWanted
