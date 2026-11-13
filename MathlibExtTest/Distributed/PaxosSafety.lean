/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Distributed.PaxosSafety

@[expose] public section

/-- Boundary check: two majorities of a 3-element set intersect. -/
example (S T : Finset (Fin 3)) (hS : 3 < 2 * S.card)
    (hT : 3 < 2 * T.card) : (S ∩ T).Nonempty :=
  majority_intersect S T hS hT
