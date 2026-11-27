/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Fourier.HomogeneousSobolevHolderEmbedding

/-!
# Tests for the homogeneous Sobolev embedding

At order zero the seminorm recovers the ordinary square-integral norm.
At the included endpoint the Hölder denominator is the square root of the distance.
-/

open MathlibExt.Analysis.Fourier.HomogeneousSobolevHolderEmbeddingWanted
open scoped FourierTransform

example (f : SchwartzMap ℝ ℂ) :
    dotHSeminorm 0 f = Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := by
  simp [dotHSeminorm, SchwartzMap.integral_norm_sq_fourier]

example : ∃ C > 0, ∀ f : SchwartzMap ℝ ℂ,
    sSup (Set.range (fun p : {xy : ℝ × ℝ // xy.1 ≠ xy.2} =>
      ‖f p.1.1 - f p.1.2‖ / Real.sqrt ‖p.1.1 - p.1.2‖)) ≤ C * dotHSeminorm 1 f := by
  simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.rpow_eq_pow] using
    exists_holderSeminorm_le_mul_dotHSeminorm 1 (by norm_num [Set.mem_Ioc])
