/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.Additive.PerfectSubsetSumCoverOddMultiple

namespace MetaMathlibExt

open PerfectSubsetSumCover

-- Multiplying the first entry by 3 preserves a perfect 1-cover.
example : IsPerfectMCover 1 (Fin.cons 3 (![2, 4] : Fin 2 → ZMod 8)) := by
  have hs : IsPerfectMCover (2 ^ 0) (Fin.cons 1 (![2, 4] : Fin 2 → ZMod 8)) := by decide
  exact isPerfectMCover_cons_oddMultiple hs ⟨1, by decide⟩

-- A negative odd multiple also works when two tail entries have the same value.
example : IsPerfectMCover 2 (Fin.cons 5 (![2, 2, 4] : Fin 3 → ZMod 8)) := by
  have hs : IsPerfectMCover (2 ^ 1) (Fin.cons 1 (![2, 2, 4] : Fin 3 → ZMod 8)) := by decide
  exact isPerfectMCover_cons_oddMultiple hs ⟨-2, by decide⟩

-- The head may be zero and the tail may be empty.
example : IsPerfectMCover 2 (Fin.cons 0 (Fin.elim0 : Fin 0 → ZMod 1)) := by
  have hs : IsPerfectMCover (2 ^ 1) (Fin.cons 0 (Fin.elim0 : Fin 0 → ZMod 1)) := by decide
  exact isPerfectMCover_cons_oddMultiple hs ⟨1, by decide⟩

end MetaMathlibExt
