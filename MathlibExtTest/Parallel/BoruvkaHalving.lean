/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Parallel.BoruvkaHalving

@[expose] public section

/-- Pairing four components into two blocks at least halves the count. -/
example : 2 * Fintype.card (Fin 2) ≤ Fintype.card (Fin 4) :=
  card_le_of_forall_fiber_ge (fun c => c / 2) (by decide)

/-- Real form of the same pairing bound. -/
example : (Fintype.card (Fin 2) : ℝ) ≤ Fintype.card (Fin 4) / 2 :=
  merged_card_le_half (fun c => c / 2) (by decide)

end
