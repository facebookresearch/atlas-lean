/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ThreePrimeDCarmichaelDivisibility
import Mathlib.Tactic.NormNum.LegendreSymbol

open MetaMathlibExt

-- The opposite-sign branch with D = 76 and q = 5 singles out 3 · 5 · 13.
example {r : ℕ} (hr : r.Prime) (hqr : 5 < r) (h : IsDCarmichael 76 (3 * 5 * r))
    (hs : jacobiSym 76 r = -1) : r = 13 := by
  have heq := (threeQR_isDCarmichael_divisibility (by decide) hr (by decide) hqr h).2.2.1
  norm_num [hs] at heq
  omega

-- For D = 1 all signs agree, so q = 11 forces the largest prime of 561.
example {r : ℕ} (hr : r.Prime) (hqr : 11 < r) (h : IsDCarmichael 1 (3 * 11 * r)) :
    r = 17 := by
  have heq := (threeQR_isDCarmichael_divisibility (by decide) hr (by decide) hqr h).2.2.2
  simp at heq
  omega
