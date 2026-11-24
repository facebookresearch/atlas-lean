/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ThreePrimeDCarmichael
import Mathlib.Tactic.NormNum.LegendreSymbol

open MetaMathlibExt

-- The largest listed product occurs, while the product for the next prime after 53 does not.
example : ∃ D : ℤ, IsDCarmichael D (3 * 17 * 53) :=
  (threeQR_isDCarmichael_iff (by decide) (by decide) (by decide) (by decide)).1.mpr (by decide)

example : ¬ ∃ D : ℤ, IsDCarmichael D (3 * 17 * 59) := by
  rw [(threeQR_isDCarmichael_iff (q := 17) (r := 59) (by decide) (by decide)
    (by decide) (by decide)).1]
  decide

-- The discriminant 1 fails the local condition at 7 for the listed number 105.
example : ¬ IsDCarmichael 1 105 := by
  intro h
  have hd := threeQR_isDCarmichael_iff.cofactor_dvd (m := 15) (p := 7)
    (by decide) (by decide) h
  norm_num at hd

-- Two discriminants for 105 must agree even at the smallest prime factor.
example {D D' : ℤ} (h : IsDCarmichael D (3 * 5 * 7)) (h' : IsDCarmichael D' (3 * 5 * 7)) :
    jacobiSym D 3 = jacobiSym D' 3 :=
  ((threeQR_isDCarmichael_iff (q := 5) (r := 7) (by decide) (by decide) (by decide)
    (by decide)).2 D D' h h').1
