/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Parallel.CRCWCombining
public import CSLibExt.Parallel.PRAM
meta import CSLibExt.Parallel.CRCWCombining
import Mathlib.Data.Fin.VecNotation
meta import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace CSLibExtTest.Parallel.CRCWCombining

open Cslib.Parallel.PRAM

/-! ## Maximum rule -/

/-- The writes `0, 3, 1` resolve to `3`, by kernel evaluation and by compiled evaluation. -/
example : crcwMax ![0, 3, 1] = 3 := by decide

#guard crcwMax ![0, 3, 1] = 3

/-- Processors `0` and `1` read cells `0` and `3` of the identity memory and both write the
value read to cell `0`. -/
def twoWriters : PramProg ℕ 2 where
  readAddr i := if (i : ℕ) = 0 then 0 else 3
  compute _ v := v
  writeAddr _ := some 0

/-- For the writes `0, 3`, Priority CRCW (`stepCRCW`) stores processor `0`'s value `0`, while
the maximum rule stores `3`. -/
example : stepCRCW (fun a => a) twoWriters 0 = 0 := by decide

example : crcwMax (writeVal (fun a => a) twoWriters) = 3 := by decide

/-- The resolved value `3` is written by processor `1`, as `crcwMax_mem` guarantees for some
processor. -/
example : crcwMax ![0, 3, 1] = ![0, 3, 1] 1 := by decide

example : ∃ i, crcwMax ![0, 3, 1] = ![0, 3, 1] i := crcwMax_mem (by decide) _

/-- Every write is at most the resolved value. -/
example (i : Fin 3) : ![0, 3, 1] i ≤ crcwMax ![0, 3, 1] := le_crcwMax _ i

/-- With no processors the maximum is `0`. -/
example : crcwMax (![] : Fin 0 → ℕ) = 0 := by decide

/-! ## OR rule -/

/-- One `true` write makes the cell `true`. -/
example : crcwOr ![false, true, false] = true := by decide

#guard crcwOr ![false, true, false]

example : ∃ i, ![false, true, false] i = true := (crcwOr_iff _).1 (by decide)

/-- With only `false` writes the cell is `false`, and no processor writes `true`. -/
example : crcwOr ![false, false] = false := by decide

example : ¬ ∃ i, ![false, false] i = true := fun h =>
  absurd ((crcwOr_iff _).2 h) (by decide)

/-- With no processors the cell is `false`. -/
example : crcwOr (![] : Fin 0 → Bool) = false := by decide

example (w : Fin 0 → Bool) : crcwOr w = false := by
  cases h : crcwOr w with
  | false => rfl
  | true => exact ((crcwOr_iff w).1 h).elim fun i _ => i.elim0

end CSLibExtTest.Parallel.CRCWCombining
