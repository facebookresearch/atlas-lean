/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.SquareTriangularSmallSquares
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

open ArithmeticFunction

-- The first nontrivial square needs the positive-index observation 1² + t₂ = 4.
example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ u v : ℕ, 0 < u → 0 < v →
      f (u ^ 2 + v * (v + 1) / 2) = f (u ^ 2) + f (v * (v + 1) / 2))
    (hlt : ∀ n : ℕ, 1 ≤ n → n ≤ 3 → f n = n) : f 4 = 4 := by
  have h := multiplicative_sq_triangular_additive_sq f hf hadd 4 (by decide) hlt 2
    (by decide) (by decide)
  norm_num at h ⊢
  exact h

-- The upper endpoint m = N - 2 is included, even when m² exceeds the known prefix.
example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ u v : ℕ, 0 < u → 0 < v →
      f (u ^ 2 + v * (v + 1) / 2) = f (u ^ 2) + f (v * (v + 1) / 2))
    (hlt : ∀ n : ℕ, 1 ≤ n → n ≤ 5 → f n = n) : f 16 = 16 := by
  have h := multiplicative_sq_triangular_additive_sq f hf hadd 6 (by decide) hlt 4
    (by decide) (by decide)
  norm_num at h ⊢
  exact h

end MetaMathlibExt
