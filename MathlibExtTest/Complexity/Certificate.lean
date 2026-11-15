/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.Certificate

@[expose] public section

/-- A leaf has the empty certificate. -/
example (x : Fin 1 → Bool) :
    ∃ S : Finset (Fin 1), S.card ≤ (QTree.leaf (n := 1) true).depth ∧
      ∀ y : Fin 1 → Bool, (∀ i ∈ S, y i = x i) →
        (QTree.leaf (n := 1) true).eval y = (QTree.leaf (n := 1) true).eval x :=
  QTree.exists_certificate _ _

end
