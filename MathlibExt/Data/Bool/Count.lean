/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications Copyright (c) 2026 Meta Platforms, Inc. and affiliates.
Modified for Atlas: moved the theorem to the `List` namespace, narrowed imports, and added
importing-client tests.
-/
module

/-! # Counting true values in Boolean lists

Adapted from `SizeCircuit.sum_toNat` in `eth/proof/consequences/SizeCircuit/Circuit.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth, a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace List

/-- The sum of the natural values of a Boolean list is its number of `true` entries. -/
theorem sum_map_toNat_eq_count_true (bits : List Bool) :
    (bits.map Bool.toNat).sum = bits.count true := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    rw [map_cons, sum_cons, ih]
    cases bit
    · rw [count_cons_of_ne (by decide)]
      simp
    · rw [count_cons_self]
      simp [Nat.add_comm]

end List
