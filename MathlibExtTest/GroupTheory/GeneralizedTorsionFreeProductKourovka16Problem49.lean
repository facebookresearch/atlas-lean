/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.GeneralizedTorsionFreeProductKourovka16Problem49
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Int.Basic

/-!
# Examples of generalized torsion

Apply the free product theorem to countably many infinite cyclic groups. Translation on the integers
also tests how conjugation by a reflection gives generalized torsion in the permutation group.
-/

namespace MathlibExtTest.GroupTheory.GeneralizedTorsionFreeProductKourovka16Problem49

open MathlibExt.GroupTheory.GeneralizedTorsionFreeProductKourovka16Problem49Wanted

example (g : Monoid.CoprodI fun _ : ℕ => Multiplicative ℤ) : ¬ IsGeneralizedTorsion g := by
  apply freeProductNoGeneralizedTorsion_holds ℕ (fun _ => Multiplicative ℤ) _ g
  rintro _ a ⟨ha, l, hl, hp⟩
  have hc (x : Multiplicative ℤ) : x⁻¹ * a * x = a := by simp [mul_comm, mul_left_comm]
  simp only [hc, List.map_const', List.prod_replicate] at hp
  have h := congrArg Multiplicative.toAdd hp
  have hmul : (l.length : ℤ) * a.toAdd = 0 := by simpa using h
  have hn : (l.length : ℤ) ≠ 0 := by simpa using hl
  have ha0 : a.toAdd = 0 := (Int.mul_eq_zero.mp hmul).resolve_left hn
  exact ha (Multiplicative.toAdd.injective ha0)

example : IsGeneralizedTorsion (Equiv.addRight (1 : ℤ)) := by
  let r := Equiv.neg ℤ
  refine ⟨fun h => ?_, [1, r], by decide, ?_⟩
  · have := Equiv.congr_fun h 0
    simp at this
  · ext x
    simp [r, Equiv.Perm.mul_apply]

end MathlibExtTest.GroupTheory.GeneralizedTorsionFreeProductKourovka16Problem49
