/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.RandomTranspositionLower

open MathlibExt.Probability.MarkovMixing (tvDist)
open MathlibExt.Probability.RandomWalkFiniteGroup (uniform)
open MathlibExt.Probability.RandomWalkFiniteGroupWanted (diaconis_shahshahani_lower)
open MathlibExt.RepresentationTheory.FourierTransformFiniteGroup (convPow)

/- At zero steps the walk is concentrated at the identity, and the inner
exponential in the lower bound simplifies exactly to the number of positions. -/
example (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ [NeZero n],
      2 * (Real.exp (-1) - Real.exp (-(n : ℝ))) - ε ≤
        2 * tvDist (fun σ : Equiv.Perm (Fin n) => if σ = 1 then 1 else 0) (uniform _) := by
  filter_upwards [diaconis_shahshahani_lower (fun _ => 0) ε hε] with n hn
  intro inst
  have hlog : -2 * (((0 : ℝ) - n * Real.log n / 2) / n) = Real.log n := by
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    field_simp
    ring
  simpa only [Nat.cast_zero, hlog, Real.exp_log (Nat.cast_pos.mpr (NeZero.pos n)), convPow] using hn
