/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.RamanujanFiveDissection

open MetaMathlibExt MetaMathlibExt.QPochhammer

-- At the origin the two theta functions have the same arguments and the correction terms vanish.
example : qPochhammerInfRaw 0 0 = qPochhammerInfRaw 0 0 *
    ((ramanujanThetaRaw 0 0 / ramanujanThetaRaw 0 0)⁻¹) := by
  simpa only [zero_pow (by decide : (25 : ℕ) ≠ 0), zero_pow (by decide : (5 : ℕ) ≠ 0),
    zero_pow (by decide : (4 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow two_ne_zero,
    neg_zero, zero_mul, sub_zero] using qPochhammerInf_five_dissection 0 (by simp)

-- At a nonreal nome, check the orientation of the two ratios and the signs of the corrections.
example :
    let q : ℂ := Complex.I / 2
    let Q := q ^ 5
    let A := ramanujanThetaRaw (-Q) (-Q ^ 4)
    let B := ramanujanThetaRaw (-Q ^ 2) (-Q ^ 3)
    qPochhammerInfRaw q q = qPochhammerInfRaw (q ^ 25) (q ^ 25) *
      (B / A - q - q ^ 2 * (A / B)) := by
  simpa only [inv_div] using
    qPochhammerInf_five_dissection (Complex.I / 2) (by norm_num [norm_div])
