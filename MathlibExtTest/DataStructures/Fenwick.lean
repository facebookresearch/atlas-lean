/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.DataStructures.Fenwick

@[expose] public section

/-- Updating position `1` by `5` increases the query at `1` by `5`. -/
example (a : Fin 3 → ℤ) :
    prefixSum (Function.update a 1 (a 1 + 5)) 1 = prefixSum a 1 + 5 :=
  prefixSum_update a 1 1 5

/-- Updating position `1` leaves the query at `0` unchanged. -/
example (a : Fin 3 → ℤ) :
    prefixSum (Function.update a 1 (a 1 + 5)) 0 = prefixSum a 0 :=
  prefixSum_update_of_lt a 1 0 5 (by decide)

end
