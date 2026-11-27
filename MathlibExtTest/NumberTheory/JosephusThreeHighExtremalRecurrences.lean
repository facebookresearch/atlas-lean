/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.JosephusThreeHighExtremalRecurrences

open MetaMathlibExt

namespace JosephusThreeHighExtremalRecurrencesTest

private instance decidableHighExtremal : DecidablePred IsJosephusThreeHighExtremal :=
  fun n => inferInstanceAs (Decidable (1 ≤ n ∧ (josephus 3 n = n ∨ josephus 3 n + 1 = n)))

-- The recurrence starts at the fixed point 1 and selects 2 as its successor.
example : Nat.nth IsJosephusThreeHighExtremal 1 = 2 := by
  have ha : Nat.nth IsJosephusThreeHighExtremal 0 = 1 :=
    Nat.nth_count (p := IsJosephusThreeHighExtremal) (n := 1) (by decide)
  have h := (josephusThree_highExtremal_recurrences 0).1
  rw [ha] at h
  change 2 * (Nat.nth IsJosephusThreeHighExtremal 1 : ℤ) = 4 at h
  omega

-- At the even fixed point 2, the parity correction changes 0 to 1.
example : (Nat.nth IsJosephusThreeHighExtremal 2 : ℤ) % 2 = 1 := by
  have ha : Nat.nth IsJosephusThreeHighExtremal 1 = 2 :=
    Nat.nth_count (p := IsJosephusThreeHighExtremal) (n := 2) (by decide)
  have h := (josephusThree_highExtremal_recurrences 1).2.2.2
  rw [ha] at h
  exact h

-- After the odd pure point 3, the survivor is again one below the extremal point.
example :
    let b := Nat.nth IsJosephusThreeHighExtremal 3
    (b : ℤ) - josephus 3 b = 1 := by
  have ha : Nat.nth IsJosephusThreeHighExtremal 2 = 3 :=
    Nat.nth_count (p := IsJosephusThreeHighExtremal) (n := 3) (by decide)
  have h := (josephusThree_highExtremal_recurrences 2).2.2.1
  rw [ha] at h
  exact h

-- After the even pure point 8, the recurrence gives the survivor 13.
example : josephus 3 (Nat.nth IsJosephusThreeHighExtremal 5) = 13 := by
  have ha : Nat.nth IsJosephusThreeHighExtremal 4 = 8 :=
    Nat.nth_count (p := IsJosephusThreeHighExtremal) (n := 8) (by decide)
  have h := (josephusThree_highExtremal_recurrences 4).2.1
  rw [ha] at h
  change 2 * (josephus 3 (Nat.nth IsJosephusThreeHighExtremal 5) : ℤ) = 26 at h
  omega

end JosephusThreeHighExtremalRecurrencesTest
