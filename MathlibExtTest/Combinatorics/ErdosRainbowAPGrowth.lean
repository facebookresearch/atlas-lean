/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ErdosRainbowAPGrowth
import Mathlib.Tactic.FinCases

open MathlibExt.Combinatorics.ErdosRainbowAPGrowthWanted

-- Even the empty progression requires its starting point to lie below the bound.
example : H 0 = 1 := by
  classical
  have one (f : ℕ → ℕ) : HasGoodAP f 1 0 :=
    ⟨0, 1, by decide, by decide, Or.inl fun i => Fin.elim0 i⟩
  unfold H
  rw [dite_eq_left (show ∃ N, ∀ f : ℕ → ℕ, HasGoodAP f N 0 from ⟨1, one⟩)]
  apply le_antisymm (Nat.find_min' _ one)
  have ⟨a, d, _, h, _⟩ := Nat.find_spec (p := fun N => ∀ f : ℕ → ℕ, HasGoodAP f N 0)
    ⟨1, one⟩ (fun _ => 0)
  omega

-- Two points suffice for every colouring, whether their colours agree or differ.
example : H 2 = 2 := by
  classical
  have two (f : ℕ → ℕ) : HasGoodAP f 2 2 := by
    refine ⟨0, 1, by decide, by decide, ?_⟩
    by_cases heq : f 0 = f 1
    · left
      intro i j
      fin_cases i <;> fin_cases j <;> simp_all
    · right
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [ne_comm]
  unfold H
  rw [dite_eq_left (show ∃ N, ∀ f : ℕ → ℕ, HasGoodAP f N 2 from ⟨2, two⟩)]
  apply le_antisymm (Nat.find_min' _ two)
  have ⟨a, d, hd, h, _⟩ := Nat.find_spec (p := fun N => ∀ f : ℕ → ℕ, HasGoodAP f N 2)
    ⟨2, two⟩ (fun _ => 0)
  simp only [Nat.reduceSub, Nat.mul_one] at h
  omega

-- A repeated colour and a different colour on the unique three-term progression.
example : ¬ HasGoodAP (fun n => n / 2) 3 3 := by
  rintro ⟨a, d, hd, h, hmono | hrain⟩ <;> norm_num at h
  · obtain rfl : a = 0 := by omega
    obtain rfl : d = 1 := by omega
    exact absurd (hmono 0 2) (by decide)
  · obtain rfl : a = 0 := by omega
    obtain rfl : d = 1 := by omega
    exact hrain 0 1 (by decide) rfl
