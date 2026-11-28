/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ExactCoveringSystemDigraphEcsdTwoNegTwoDescendants
import Mathlib.Tactic.NormNum

/-!
# Tests for descendants in `G(2n, -2n + a)`

Concrete walks of length three exercise both extreme coefficients, both interior signs,
an excluded endpoint, and an even offset.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Proposition 1.
-/

namespace MathlibExtTest.NumberTheory.Digits.ExactCoveringSystemDigraphEcsdTwoNegTwoDescendants

open MetaMathlibExt

example : IsKDescendant (ecsdAdj ![2, -2] ![0, 3]) 3 2 16 := by
  apply (ecsd_two_neg_two_descendants 3 2 16 3 (by decide)).mpr
  exact Or.inl (by norm_num)

example : IsKDescendant (ecsdAdj ![2, -2] ![0, 3]) 3 2 10 := by
  apply (ecsd_two_neg_two_descendants 3 2 10 3 (by decide)).mpr
  exact Or.inr (Or.inl ⟨2, by decide, by decide, Or.inl (by norm_num)⟩)

example : IsKDescendant (ecsdAdj ![2, -2] ![0, 3]) 3 2 (-10) := by
  apply (ecsd_two_neg_two_descendants 3 2 (-10) 3 (by decide)).mpr
  exact Or.inr (Or.inl ⟨2, by decide, by decide, Or.inr (by norm_num)⟩)

example : IsKDescendant (ecsdAdj ![2, -2] ![0, 3]) 3 2 (-4) := by
  apply (ecsd_two_neg_two_descendants 3 2 (-4) 3 (by decide)).mpr
  exact Or.inr (Or.inr (by norm_num))

example : ¬ IsKDescendant (ecsdAdj ![2, -2] ![0, 3]) 3 2 (-16) := by
  intro h
  obtain h | ⟨b, hb, hb', h | h⟩ | h :=
    (ecsd_two_neg_two_descendants 3 2 (-16) 3 (by decide)).mp h
  · norm_num at h
  · norm_num at hb' h
    omega
  · norm_num at h
    omega
  · norm_num at h

example : IsKDescendant (ecsdAdj ![2, -2] ![0, 2]) 3 3 (-20) := by
  apply (ecsd_two_neg_two_descendants 2 3 (-20) 3 (by decide)).mpr
  exact Or.inr (Or.inl ⟨2, by decide, by decide, Or.inr (by norm_num)⟩)

end MathlibExtTest.NumberTheory.Digits.ExactCoveringSystemDigraphEcsdTwoNegTwoDescendants
