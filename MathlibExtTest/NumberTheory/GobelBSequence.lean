/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GobelBSequence

open MetaMathlibExt

-- With period one, normalization determines even the value on the zero residue.
example {b : ℤ → ℤ} (hb : IsGobelBSequence 0 0 b) : b = fun _ => 1 := by
  have h := existsUnique_gobelBSequence 0 0 (by decide) (by decide) (by decide)
  apply h.unique hb
  refine ⟨fun _ => Or.inl rfl, fun _ => rfl, rfl, fun n hn => ?_, fun _ => rfl⟩
  exact (hn (Int.emod_one n)).elim

-- At the upper endpoint s = l = 2, both the zero and negative-one indices carry a minus sign.
example : ∃! b : ℤ → ℤ, IsGobelBSequence 2 2 b ∧ b 0 = -1 ∧ b (-1) = -1 := by
  obtain ⟨b, hb, hu⟩ := existsUnique_gobelBSequence 2 2 (by decide) (by decide) (by decide)
  have h₂ : b 2 = -1 := by
    have h := hb.2.2.2.1 1 (by decide)
    rw [hb.2.2.1] at h
    change 1 = -b 2 at h
    omega
  have h₀ : b 0 = b 2 :=
    (hb.2.2.2.2 2).trans (hb.2.1 2)
  exact ⟨b, ⟨hb, h₀.trans h₂, (hb.2.1 (-1)).symm.trans h₂⟩, fun c hc => hu c hc.1⟩

-- At the minimum allowed l, the two endpoint sequences agree at -1 and have opposite signs at -3.
example {b₁ b₂ : ℤ → ℤ} (hb₁ : IsGobelBSequence 2 2 b₁) (hb₂ : IsGobelBSequence 2 0 b₂) :
    b₁ (-1) = b₂ (-1) ∧ b₁ (-3) = -b₂ (-3) := by
  have h := gobelBSequence_complement 2 2 (by decide) (by decide) (by decide) (by decide)
    b₁ b₂ hb₁ hb₂
  exact ⟨(h (-1)).1 (by decide), (h (-3)).2 (by decide)⟩

-- For the interior pair s = 1 and l - s = 3, a positive nonmultiple agrees and zero flips sign.
example {b₁ b₂ : ℤ → ℤ} (hb₁ : IsGobelBSequence 4 1 b₁) (hb₂ : IsGobelBSequence 4 3 b₂) :
    b₁ 2 = b₂ 2 ∧ b₁ 0 = -b₂ 0 := by
  have h := gobelBSequence_complement 4 1 (by decide) (by decide) (by decide) (by decide)
    b₁ b₂ hb₁ hb₂
  exact ⟨(h 2).1 (by decide), (h 0).2 (by decide)⟩
