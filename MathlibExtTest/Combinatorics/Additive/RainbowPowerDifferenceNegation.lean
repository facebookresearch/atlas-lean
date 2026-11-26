/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.RainbowPowerDifferenceNegation

open MetaMathlibExt

private def sampleColor (x : ZMod 7) : Fin 3 :=
  if x = 0 then 0 else if x = 1 ∨ x = -1 then 1 else 2

private theorem sampleColor_surjective : Function.Surjective sampleColor := by
  intro i
  fin_cases i
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩

private theorem sampleColor_rainbowFree_even :
    ∀ x y z : ZMod 7, x - y = z ^ (2 : ℕ) →
      ¬ (sampleColor x ≠ sampleColor y ∧ sampleColor y ≠ sampleColor z ∧
        sampleColor x ≠ sampleColor z) := by decide

private theorem sampleColor_rainbowFree_odd :
    ∀ x y z : ZMod 7, x - y = z ^ (1 : ℕ) →
      ¬ (sampleColor x ≠ sampleColor y ∧ sampleColor y ≠ sampleColor z ∧
        sampleColor x ≠ sampleColor z) := by decide

-- With an even exponent both third entries use the same orientation of the edge.
example : sampleColor (-2) = sampleColor 2 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact color_neg_eq_of_rainbowFree_powDiff 7 2 sampleColor sampleColor_surjective
    sampleColor_rainbowFree_even 2

-- With an odd exponent the two third entries use opposite orientations.
example : sampleColor (-1) = sampleColor 1 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact color_neg_eq_of_rainbowFree_powDiff 7 1 sampleColor sampleColor_surjective
    sampleColor_rainbowFree_odd 1

example : sampleColor (-0) = sampleColor 0 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact color_neg_eq_of_rainbowFree_powDiff 7 2 sampleColor sampleColor_surjective
    sampleColor_rainbowFree_even 0
