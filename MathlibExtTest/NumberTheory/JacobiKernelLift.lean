/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.IsSquare
import MathlibExt.NumberTheory.JacobiKernelLift

open MetaMathlibExt

-- The class of 3 has negative Jacobi symbol modulo 7, and 45 has a repeated prime factor.
example : ∃ x : ZMod 315, IsUnit x ∧ jacobiSym x.val 315 = 1 ∧
    ZMod.castHom (by decide : 7 ∣ 315) (ZMod 7) x = 3 := by
  obtain ⟨x, hx, hred⟩ := units_subset_image_jacobi_kernel 45 7 (by decide) (by norm_num)
    (by decide) 3 ((ZMod.isUnit_iff_coprime 3 7).mpr (by decide))
  exact ⟨x, hx.1, hx.2, hred⟩

-- The unique residue modulo 1 is also a unit and has a lift in the kernel.
example : ∃ x : ZMod 3, IsUnit x ∧ jacobiSym x.val 3 = 1 ∧
    ZMod.castHom (one_dvd 3) (ZMod 1) x = 0 := by
  obtain ⟨x, hx, hred⟩ := units_subset_image_jacobi_kernel 3 1 (by decide) (by norm_num)
    (by decide) 0 ((ZMod.isUnit_iff_coprime 0 1).mpr (by decide))
  exact ⟨x, hx.1, hx.2, hred⟩
