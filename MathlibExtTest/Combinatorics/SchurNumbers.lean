/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SchurNumbers

/-! # Tests for `MathlibExt.Combinatorics.SchurNumbers` -/

namespace MathlibExtTest.SchurNumbers

open MathlibExt.Combinatorics.SchurNumbersWanted

-- Edge case: with no colours there is no colouring at all, so every `N`, even `0`, forces a
-- monochromatic solution. The value `S(0) = 0` comes from the `k < 1` branch, not from the
-- infimum (which is `0` here, and `0 - 1 = 0` in `ℕ` as well).
example (N : ℕ) : schurForces 0 N := fun c => (c 0).elim0

example : schurNumber 0 = 0 := by
  simp [schurNumber]

-- One colour: solutions with `x = y` count, so `1 + 1 = 2` makes `2` force a monochromatic
-- solution, while `{1}` contains none. The definition therefore gives `S(1) = 1`.
example : schurForces 1 2 := fun _ =>
  ⟨1, by simp, 1, by simp, 2, by simp, rfl, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

example : ¬ schurForces 1 1 := by
  intro h
  obtain ⟨x, hx, y, hy, z, hz, hxyz, -⟩ := h fun _ => 0
  simp only [Finset.mem_Icc] at hx hy hz
  omega

example : schurNumber 1 = 1 := by
  have h2 : schurForces 1 2 := fun _ =>
    ⟨1, by simp, 1, by simp, 2, by simp, rfl, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hlt : ∀ N < 2, ¬ schurForces 1 N := by
    intro N hN h
    obtain ⟨x, hx, y, hy, z, hz, hxyz, -⟩ := h fun _ => 0
    simp only [Finset.mem_Icc] at hx hy hz
    omega
  have hinf : sInf {N | schurForces 1 N} = 2 :=
    le_antisymm (Nat.sInf_le h2) (Nat.le_of_not_lt fun h =>
      hlt _ h (Nat.sInf_mem (s := {N | schurForces 1 N}) ⟨2, h2⟩))
  simp [schurNumber, hinf]

-- In two colours, 5 is the first interval endpoint that forces a triple.
example : IsLeast {N | schurForces 2 N} 5 := by
  have h := schurNumber_two
  rw [schurNumber, ite_eq_right (by decide)] at h
  have hinf : sInf {N | schurForces 2 N} = 4 + 1 := by omega
  simpa only [hinf] using isLeast_csInf (Nat.nonempty_of_sInf_eq_succ hinf)

-- For three colours, the least forcing endpoint is one past the Schur number.
example : IsLeast {N | schurForces 3 N} 14 := by
  have h := schurNumber_three
  rw [schurNumber, ite_eq_right (by decide)] at h
  have hinf : sInf {N | schurForces 3 N} = 13 + 1 := by omega
  simpa only [hinf] using isLeast_csInf (Nat.nonempty_of_sInf_eq_succ hinf)

-- The lower bound is not a junk value: it says that no `N ≤ 536` forces a monochromatic
-- solution in six colours, so some colouring of `{1, …, 536}` with six colours has none.
example {N : ℕ} (hN : N ≤ 536) : ¬ schurForces 6 N := by
  intro h
  have h1 := Nat.sInf_le (show N ∈ {N | schurForces 6 N} from h)
  have h2 := le_schurNumber_six
  rw [schurNumber, ite_eq_right (by omega)] at h2
  omega

-- In particular, `S(6)` is positive.
example : 0 < schurNumber 6 :=
  Nat.lt_of_lt_of_le (by omega) le_schurNumber_six

end MathlibExtTest.SchurNumbers
