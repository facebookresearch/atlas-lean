/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentIntervalOperator
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalTwoBeadOrdinalCharts

/-!
# SAME complete original joined endpoint intervals

Both actual consecutive original endpoint intervals join into the same
complete outer interval. The entire native ordinal, both full input
operators and every original vertex are retained, including zero sides.
-/

noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBeadInterval

open SSet.OriginalTwoBead.OrdinalCharts

variable {n : ℕ} (a b c : Fin (n + 1)) (hab : a ≤ b) (hbc : b ≤ c)

/-- The SAME full original consecutive interval dimensions add exactly. -/
theorem joined_lengths (hab : a ≤ b) (hbc : b ≤ c) : length a b + length b c = length a c := by
  change b.val - a.val + (c.val - b.val) = c.val - a.val
  change a.val ≤ b.val at hab
  change b.val ≤ c.val at hbc
  omega

/-- The SAME original native gluing ordinal retains every whole input vertex value. -/
def joinedOperator : ⦋length a b + length b c⦌ ⟶ ⦋length a c⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨i.val, by
        change i.val < length a c + 1
        rw [← joined_lengths a b c hab hbc]
        exact i.isLt⟩
      monotone' := fun _ _ h => h }

/-- The SAME joined original ordinal retains its actual initial endpoint. -/
theorem joinedOperator_zero : (joinedOperator a b c hab hbc).toOrderHom 0 = 0 := rfl

/-- The SAME joined original ordinal retains its actual terminal endpoint. -/
theorem joinedOperator_last :
    (joinedOperator a b c hab hbc).toOrderHom (Fin.last (length a b + length b c)) =
      Fin.last (length a c) :=
  Fin.ext (joined_lengths a b c hab hbc)

/-- EVERY full original prefix vertex retains the original first interval embedding. -/
theorem joined_prefix_vertex (i : Fin (length a b + 1)) :
    embedding a c (hab.trans hbc)
      ((joinedOperator a b c hab hbc).toOrderHom (prefixEmbedding (length a b) (length b c) i)) =
        embedding a b hab i := Fin.ext rfl

/-- EVERY full original suffix vertex retains the original second interval embedding. -/
theorem joined_suffix_vertex (i : Fin (length b c + 1)) :
    embedding a c (hab.trans hbc)
      ((joinedOperator a b c hab hbc).toOrderHom (suffix (length a b) (length b c) i)) =
        embedding b c hbc i := by
  apply Fin.ext
  change a.val + (length a b + i.val) = b.val + i.val
  change a.val ≤ b.val at hab
  dsimp [length]
  omega

/-- Both SAME full original prefix maps commute with the original complete input ordinal. -/
theorem joined_prefix_square :
    prefixOperator (length a b) (length b c) ≫ joinedOperator a b c hab hbc ≫
      operator a c (hab.trans hbc) = operator a b hab := by
  ext i : 3
  exact joined_prefix_vertex a b c hab hbc i

/-- Both SAME full original suffix maps commute with the original complete input ordinal. -/
theorem joined_suffix_square :
    suffixOperator (length a b) (length b c) ≫ joinedOperator a b c hab hbc ≫
      operator a c (hab.trans hbc) = operator b c hbc := by
  ext i : 3
  exact joined_suffix_vertex a b c hab hbc i

end CategoryTheory.CoherentRealization.OriginalBeadInterval
