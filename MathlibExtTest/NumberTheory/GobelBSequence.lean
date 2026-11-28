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

-- A sign table for (l, s) = (4, 1), with period 5 and complementary shift 2.
private def b41 (n : ℤ) : ℤ := if n % 5 = 1 ∨ n % 5 = 2 then 1 else -1

private theorem b41_spec : IsGobelBSequence 4 1 b41 := by
  apply isGobelBSequence_iff.mpr
  refine ⟨fun n => ?_, fun n => ?_, by decide, fun n hn => ?_, fun n => ?_⟩
  · unfold b41
    split <;> simp
  · change b41 (n + 5) = b41 n
    simp [b41]
  · change ¬ (5 : ℤ) ∣ n at hn
    have hmod := Int.dvd_iff_emod_eq_zero.not.mp hn
    simp only [b41]
    split <;> split <;> omega
  · change b41 (n + 3) = b41 (-n)
    simp only [b41]
    split <;> split <;> omega

-- Compute all three identities on a complete set of residue representatives.
example : ∀ r : Fin 5, let n : ℤ := r.val
    (n % 5 ≠ 0 → (n + 3) % 5 ≠ 0 → b41 n = -b41 (n + 3)) ∧
    (n % 5 ≠ 0 → (n + 2) % 5 ≠ 0 → b41 n = -b41 (n + 2)) ∧
    ((1 - n) % 5 ≠ 0 → (1 + n) % 5 ≠ 0 → b41 (1 - n) = b41 (1 + n)) := by
  decide

-- Each unconditional version fails when a displayed index is a multiple of the period.
example : b41 0 ≠ -b41 3 ∧ b41 3 ≠ -b41 5 ∧ b41 0 ≠ b41 2 := by
  decide

-- Exercise the public theorem at indices that include negative arguments.
example : b41 (-4) = -b41 (-1) ∧ b41 (-3) = -b41 (-1) ∧ b41 (-1) = b41 3 := by
  obtain ⟨h₁, h₂, h₃⟩ := gobelBSequence_translation_identities 4 1
    (by decide) (by decide) (by decide) (by decide) b41 b41_spec
  exact ⟨h₁ (-4) (by decide) (by decide), h₂ (by decide) (-3) (by decide) (by decide),
    h₃ (by decide) 2 (by decide) (by decide)⟩
