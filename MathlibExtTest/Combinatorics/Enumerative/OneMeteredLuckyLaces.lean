/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.OneMeteredLuckyLaces

open MetaMathlibExt

namespace MathlibExtTest.OneMeteredLuckyLaces

private def luckyFlags {m n : ℕ} (f : Fin m → Fin n) : List Bool :=
  let prefs := List.ofFn fun i => (f i : ℕ)
  (prefs.zip (meteredOutcome 1 n prefs)).map fun p => decide (p.2 = some p.1)

-- The repeated head and the succeeding preference both extend the first lace.
example : luckyFlags (n := 4) ![1, 1, 2, 0] = [true, false, false, true] := by
  rw [luckyFlags, one_metered_lucky_iff_lace_start (by decide) (by decide)]
  decide

-- A failed bump at the last spot ends the lace. The next car can take that same spot.
example : luckyFlags (n := 3) ![2, 2, 2] = [true, false, true] := by
  rw [luckyFlags, one_metered_lucky_iff_lace_start (by decide) (by decide)]
  decide

example : luckyFlags (n := 3) ![2, 2, 2] = [true, false, true] := by decide

end MathlibExtTest.OneMeteredLuckyLaces
