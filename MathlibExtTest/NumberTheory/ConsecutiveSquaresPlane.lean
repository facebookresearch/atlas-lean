/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ConsecutiveSquaresPlane

open MetaMathlibExt

-- The odd-span family in the plane of the 3-4-5 solution.
example :
    ∃ f : ℕ → ℤ × ℤ × ℤ, Function.Injective f ∧
      ∀ n, SoCSEq (f n).1 (f n).2.1 (f n).2.2 ∧
        -(f n).1 + 3 * (f n).2.1 - 2 * (f n).2.2 = 0 ∧ Odd ((f n).2.2 - (f n).1) := by
  obtain ⟨f, hinj, hf⟩ := soCS_infinite_family_plane 2 4 5 isSoCSSolution_two_four_five
  refine ⟨f, hinj, fun n => ?_⟩
  obtain ⟨heq, hplane, hparity⟩ := hf n
  refine ⟨heq, ?_, ?_⟩
  · linear_combination hplane
  · simpa [Int.odd_iff, Int.ModEq] using hparity

-- A solution of span 52 exercises the even-span case.
example :
    ∃ f : ℕ → ℤ × ℤ × ℤ, Function.Injective f ∧
      ∀ n, Even ((f n).2.2 - (f n).1) := by
  have h : IsSoCSSolution 11 50 63 := by norm_num [IsSoCSSolution, SoCSEq]
  obtain ⟨f, hinj, hf⟩ := soCS_infinite_family_plane 11 50 63 h
  refine ⟨f, hinj, fun n => ?_⟩
  simpa [Int.even_iff, Int.ModEq] using (hf n).2.2

-- The plane of the span-52 solution also holds triples off the diagonal: (24, -15, -28)
-- satisfies the three conditions of the theorem and has x ≠ z.
example :
    ∃ t : ℤ × ℤ × ℤ, t.1 ≠ t.2.2 ∧ SoCSEq t.1 t.2.1 t.2.2 ∧
      (50 - 63) * t.1 + (63 - 11) * t.2.1 + (11 - 50) * t.2.2 = 0 ∧
      t.2.2 - t.1 ≡ 63 - 11 [ZMOD 2] :=
  ⟨(24, -15, -28), by norm_num [SoCSEq, Int.ModEq]⟩
