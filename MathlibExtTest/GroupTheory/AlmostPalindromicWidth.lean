/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.AlmostPalindromicWidth

open MathlibExt.GroupTheory.AlmostPalindromicWidthKourovka19Problem8Wanted

example : IsAlmostPalindrome 0 [] := ⟨[], rfl, rfl, by decide⟩

-- The word x x⁻¹ represents the identity, but its two signs differ. It needs one edit.
example : FreeGroup.mk [((0 : Fin 2), true), (0, false)] = 1 :=
  Quot.sound FreeGroup.Red.Step.cons_not

example : IsAlmostPalindrome 1 [(0, true), (0, false)] :=
  ⟨[(0, true), (0, true)], rfl, rfl, by decide⟩

example : ¬ IsAlmostPalindrome 0 [(0, true), (0, false)] := by
  rintro ⟨p, hlen, hpal, hcount⟩
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  have hab : b = a := (List.cons.inj hpal).1
  subst b
  by_cases ha : (0, true) = a
  · subst a
    contradiction
  · simp [List.countP_cons, ha] at hcount
