/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GeneralizedLeonardoLogBehaviorGenLeonardoPowSelfLogConvex
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for log-convexity of the self-powers of generalized Leonardo numbers

Concrete instances of `genLeonardo_pow_self_logConvex` at small parameters.
-/

namespace MathlibExtTest.Combinatorics.Enumerative.GeneralizedLeonardoLogBehaviorGenLeonardoPowSelfLogConvex

-- At k = 1, n = 4 the three values are 5, 9 and 15.
example : (9 : ℤ) ^ 8 ≤ 5 ^ 3 * 15 ^ 5 := by
  have h := MetaMathlibExt.genLeonardo_pow_self_logConvex 1 (by decide) 4 (by decide)
  have e34 : 4 - 1 = 3 := rfl
  have e41 : 4 + 1 = 5 := rfl
  have e24 : 2 * 4 = 8 := rfl
  have e3 : MetaMathlibExt.genLeonardo ((1 : ℕ) : ℤ) 3 = 5 := by decide
  have e4 : MetaMathlibExt.genLeonardo ((1 : ℕ) : ℤ) 4 = 9 := by decide
  have e5 : MetaMathlibExt.genLeonardo ((1 : ℕ) : ℤ) 5 = 15 := by decide
  rw [e24, e34, e41, e3, e4, e5] at h
  exact h

-- At n = 4 the inequality reads (4k+5)^8 ≤ (2k+3)^3 (7k+8)^5.
example (k : ℕ) (hk : 1 ≤ k) :
    (4 * (k : ℤ) + 5) ^ 8 ≤ (2 * (k : ℤ) + 3) ^ 3 * (7 * (k : ℤ) + 8) ^ 5 := by
  have h := MetaMathlibExt.genLeonardo_pow_self_logConvex k hk 4 (by decide)
  have e34 : 4 - 1 = 3 := rfl
  have e41 : 4 + 1 = 5 := rfl
  have e24 : 2 * 4 = 8 := rfl
  rw [e24, e34, e41] at h
  have h3 : MetaMathlibExt.genLeonardo (k : ℤ) 3 = 2 * (k : ℤ) + 3 := by
    have h2 : MetaMathlibExt.genLeonardo (k : ℤ) 2 = 2 + (k : ℤ) := rfl
    have h1 : MetaMathlibExt.genLeonardo (k : ℤ) 1 = 1 := rfl
    have hh3 : MetaMathlibExt.genLeonardo (k : ℤ) 3
        = MetaMathlibExt.genLeonardo (k : ℤ) 2 + MetaMathlibExt.genLeonardo (k : ℤ) 1 + (k : ℤ) := rfl
    rw [hh3, h2, h1]; ring
  have h4 : MetaMathlibExt.genLeonardo (k : ℤ) 4 = 4 * (k : ℤ) + 5 := by
    have h2 : MetaMathlibExt.genLeonardo (k : ℤ) 2 = 2 + (k : ℤ) := rfl
    have hh4 : MetaMathlibExt.genLeonardo (k : ℤ) 4
        = MetaMathlibExt.genLeonardo (k : ℤ) 3 + MetaMathlibExt.genLeonardo (k : ℤ) 2 + (k : ℤ) := rfl
    rw [hh4, h3, h2]; ring
  have h5 : MetaMathlibExt.genLeonardo (k : ℤ) 5 = 7 * (k : ℤ) + 8 := by
    have hh5 : MetaMathlibExt.genLeonardo (k : ℤ) 5
        = MetaMathlibExt.genLeonardo (k : ℤ) 4 + MetaMathlibExt.genLeonardo (k : ℤ) 3 + (k : ℤ) := rfl
    rw [hh5, h4, h3]; ring
  rw [h3, h4, h5] at h
  exact h

-- At k = 2, n = 5 the three values are 13, 22 and 37, with defect 22^2 - 13 * 37 = 3 > 0.
example : (22 : ℤ) ^ 10 ≤ 13 ^ 4 * 37 ^ 6 := by
  have h := MetaMathlibExt.genLeonardo_pow_self_logConvex 2 (by decide) 5 (by decide)
  have e54 : 5 - 1 = 4 := rfl
  have e56 : 5 + 1 = 6 := rfl
  have e25 : 2 * 5 = 10 := rfl
  have e4 : MetaMathlibExt.genLeonardo ((2 : ℕ) : ℤ) 4 = 13 := by decide
  have e5 : MetaMathlibExt.genLeonardo ((2 : ℕ) : ℤ) 5 = 22 := by decide
  have e6 : MetaMathlibExt.genLeonardo ((2 : ℕ) : ℤ) 6 = 37 := by decide
  rw [e25, e54, e56, e4, e5, e6] at h
  exact h

end MathlibExtTest.Combinatorics.Enumerative.GeneralizedLeonardoLogBehaviorGenLeonardoPowSelfLogConvex
