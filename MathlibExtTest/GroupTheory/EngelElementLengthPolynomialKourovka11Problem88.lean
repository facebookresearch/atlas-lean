/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.EngelElementLengthPolynomialKourovka11Problem88
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace MathlibExtTest.GroupTheory.EngelElementLengthPolynomialKourovka11Problem88

open MathlibExt.GroupTheory.EngelElementLengthPolynomialKourovka11Problem88Wanted

example (h g : DihedralGroup 4) : engelComm h g 0 = h :=
  rfl

example (h g : DihedralGroup 4) : engelComm h g 1 = kcomm h g :=
  rfl

example : kcomm (DihedralGroup.sr (0 : ZMod 4)) (DihedralGroup.r 1) =
    DihedralGroup.r 2 := by
  decide

example : IsEngel (1 : DihedralGroup 4) :=
  ⟨1, le_refl 1, fun h => by simp [engelComm, kcomm]⟩

example : engelLength (1 : DihedralGroup 4) = 1 := by
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨le_refl 1, fun h => by simp [engelComm, kcomm]⟩
  · have hne : {l | 1 ≤ l ∧ ∀ h : DihedralGroup 4, engelComm h 1 l = 1}.Nonempty :=
      ⟨1, le_refl 1, fun h => by simp [engelComm, kcomm]⟩
    exact (Nat.sInf_mem hne).1

example : ¬ engelLengthPolynomialBound :=
  engelLengthPolynomialBound_refuted

end MathlibExtTest.GroupTheory.EngelElementLengthPolynomialKourovka11Problem88
