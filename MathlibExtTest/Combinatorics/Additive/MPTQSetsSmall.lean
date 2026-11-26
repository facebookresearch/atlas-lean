/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.MPTQSetsSmall
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

open MetaMathlibExt
open scoped Pointwise

/-- The four-element bound holds for any four real numbers, with no condition on their signs
and without assuming that they are distinct. -/
example (a b c d : ℝ) : ¬ IsMPTQSet {a, b, c, d} :=
  not_isMPTQSet_of_card_le_four Finset.card_le_four

/-- A set with two negative elements and the product coincidence `(-1) · 6 = (-2) · 3` is not an
MPTQ set. -/
example : ¬ IsMPTQSet ({-2, -1, 3, 6} : Finset ℝ) :=
  not_isMPTQSet_of_card_le_four Finset.card_le_four

/-- The hypotheses of the bound for sets with a negative element are satisfiable: the signed set
of Shetty and Shankar's Example 2 is an MPTQ set, with `|A · A| = 52` and `|A / A| = 51` counted
over the rationals. -/
example : 5 ≤ (({-1944, -864, -648, -162, -96, 12, 27, 36, 108, 144, 243} : Finset ℚ).image
    ((↑) : ℚ → ℝ)).card := by
  set S : Finset ℚ := {-1944, -864, -648, -162, -96, 12, 27, 36, 108, 144, 243} with hS
  have hm : (S * S).image ((↑) : ℚ → ℝ) = S.image (↑) * S.image (↑) :=
    Finset.image_image₂_distrib fun a b => Rat.cast_mul a b
  have hd : (S / S).image ((↑) : ℚ → ℝ) = S.image (↑) / S.image (↑) :=
    Finset.image_image₂_distrib fun a b => Rat.cast_div a b
  refine five_le_card_of_isMPTQSet_of_neg ⟨by simp [hS], ?_⟩ ⟨-1944, by simp [hS], by norm_num⟩
  rw [← hm, ← hd, Finset.card_image_of_injective _ Rat.cast_injective,
    Finset.card_image_of_injective _ Rat.cast_injective, hS]
  decide +kernel
