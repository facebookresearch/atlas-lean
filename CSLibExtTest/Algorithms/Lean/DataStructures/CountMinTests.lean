/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.CountMin
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for the Count-Min sketch

Exact-value tests on the frequencies `2, 5, 7` of the three items of `Fin 3`. The hashes are
the identity (collision-free), a constant (everything collides), and parity (items `0` and `2`
share bucket `0`; item `1` is alone in bucket `1`).
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CountMinTests

open Cslib.Algorithms.Lean.CountMin

/-- A collision-free hash gives each item its own counter. -/
example : counter ![2, 5, 7] (fun y : Fin 3 => y.val) 0 = 2 := by decide

example : counter ![2, 5, 7] (fun y : Fin 3 => y.val) 1 = 5 := by decide

example : counter ![2, 5, 7] (fun y : Fin 3 => y.val) 2 = 7 := by decide

/-- A bucket that no item hashes to holds `0`. -/
example : counter ![2, 5, 7] (fun y : Fin 3 => y.val) 3 = 0 := by decide

/-- A constant hash puts the whole mass `14` in one bucket. -/
example : counter ![2, 5, 7] (fun _ : Fin 3 => 0) 0 = 14 := by decide

/-- Under parity, bucket `0` holds `2 + 7` and bucket `1` holds `5`. -/
example : counter ![2, 5, 7] (fun y : Fin 3 => y.val % 2) 0 = 9 := by decide

example : counter ![2, 5, 7] (fun y : Fin 3 => y.val % 2) 1 = 5 := by decide

/-- Two rows, the constant one first: the minimum selects the collision-free counter `5`
over `14`, so the estimate for item `1` is exact. -/
example :
    estimate ![2, 5, 7] (fun j (y : Fin 3) => if j = 0 then 0 else y.val) 2 (by decide) 1 = 5 := by
  decide

/-- The same two rows in the other order give the same estimate. -/
example :
    estimate ![2, 5, 7] (fun j (y : Fin 3) => if j = 0 then y.val else 0) 2 (by decide) 1 = 5 := by
  decide

/-- With `d = 1` only row `0` counts, so the constant row alone gives `14`. -/
example :
    estimate ![2, 5, 7] (fun j (y : Fin 3) => if j = 0 then 0 else y.val) 1 (by decide) 1
      = 14 := by
  decide

/-- When every row collides the estimate overcounts: for item `0` the parity row (`9`) beats
the constant row (`14`), and the excess over the frequency `2` is the colliding mass `7`. -/
example :
    estimate ![2, 5, 7] (fun j (y : Fin 3) => if j = 0 then y.val % 2 else 0) 2 (by decide) 0
      = 9 := by
  decide

/-- The colliding mass of item `0` under parity is the frequency `7` of item `2`. -/
example :
    ∑ y ∈ Finset.univ.filter (fun y : Fin 3 => y ≠ 0 ∧ y.val % 2 = (0 : Fin 3).val % 2),
      (![2, 5, 7] : Fin 3 → ℕ) y = 7 := by
  decide

/-- The colliding mass of item `1` under parity is `0`: it is alone in its bucket. -/
example :
    ∑ y ∈ Finset.univ.filter (fun y : Fin 3 => y ≠ 1 ∧ y.val % 2 = (1 : Fin 3).val % 2),
      (![2, 5, 7] : Fin 3 → ℕ) y = 0 := by
  decide

/-- `counter_le_freq_add_collision` holds with equality here: the counter `9` of item `0` is
its frequency `2` plus its colliding mass `7`. -/
example :
    counter ![2, 5, 7] (fun y : Fin 3 => y.val % 2) 0
      = (![2, 5, 7] : Fin 3 → ℕ) 0
        + ∑ y ∈ Finset.univ.filter (fun y : Fin 3 => y ≠ 0 ∧ y.val % 2 = (0 : Fin 3).val % 2),
          (![2, 5, 7] : Fin 3 → ℕ) y := by
  decide

example :
    counter ![2, 5, 7] (fun y : Fin 3 => y.val % 2) ((fun y : Fin 3 => y.val % 2) 0)
      ≤ (![2, 5, 7] : Fin 3 → ℕ) 0
        + ∑ y ∈ Finset.univ.filter
            (fun y : Fin 3 => y ≠ 0 ∧ (fun y : Fin 3 => y.val % 2) y
              = (fun y : Fin 3 => y.val % 2) 0),
          (![2, 5, 7] : Fin 3 → ℕ) y :=
  counter_le_freq_add_collision _ _ 0

/-- `freq_le_estimate` and `estimate_le_counter` on the two-row sketch: the frequency `5` of
item `1` is at most its estimate, which is at most the constant row's counter `14`. -/
example :
    (![2, 5, 7] : Fin 3 → ℕ) 1
      ≤ estimate ![2, 5, 7] (fun j (y : Fin 3) => if j = 0 then 0 else y.val) 2 (by decide) 1 :=
  freq_le_estimate _ _ _ _ 1

example :
    estimate ![2, 5, 7] (fun j (y : Fin 3) => if j = 0 then 0 else y.val) 2 (by decide) 1
      ≤ counter ![2, 5, 7] (fun _ : Fin 3 => 0) 0 :=
  estimate_le_counter _ _ _ _ 1 0 (by decide)

end Cslib.Algorithms.Lean.CountMinTests

end
