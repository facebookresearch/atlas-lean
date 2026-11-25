/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MotzkinFirstDownLastUp
import Mathlib.Data.Fin.VecNotation

namespace MetaMathlibExt

-- At lengths zero and one the equivalence has empty source and target.
example (n : ℕ) (hn : n < 2) : IsEmpty (MotzkinLastUpEvenFamily n) := by
  obtain ⟨e⟩ := motzkinFirstDownFamily_equiv_lastUpEvenFamily n
  refine ⟨fun q => ?_⟩
  have := (e.symm q).property.1
  omega

-- At the first nonempty length every equivalence sends UD at height zero to UU at height two.
example : ∃ e : MotzkinFirstDownFamily 2 ≃ MotzkinLastUpEvenFamily 2,
    ∃ q, q.val = (0, ![2, 0]) ∧ (e q).val = (1, ![2, 2]) := by
  obtain ⟨e⟩ := motzkinFirstDownFamily_equiv_lastUpEvenFamily 2
  let q : MotzkinFirstDownFamily 2 := ⟨(0, ![2, 0]), by
    refine ⟨by decide, by decide, ?_⟩
    unfold FirstNonupStepDown
    decide⟩
  refine ⟨e, q, rfl, ?_⟩
  obtain ⟨⟨k, p⟩, hk, hbound, hp, _⟩ := e q
  have he : k = 1 := by change 1 ≤ k at hk; change k ≤ 2 / 2 at hbound; omega
  subst k
  have only_ups : ∀ w : Fin 2 → Fin 3, IsMotzkinPrefix 2 2 w → w = ![2, 2] := by decide
  exact Prod.ext rfl (only_ups p hp)

-- A trailing flat is allowed. UUF therefore has a first-down preimage.
example : ∃ e : MotzkinFirstDownFamily 3 ≃ MotzkinLastUpEvenFamily 3,
    ∃ q, (e q).val = (1, ![2, 2, 1]) := by
  obtain ⟨e⟩ := motzkinFirstDownFamily_equiv_lastUpEvenFamily 3
  let r : MotzkinLastUpEvenFamily 3 := ⟨(1, ![2, 2, 1]), by
    refine ⟨by decide, by decide, by decide, ?_⟩
    unfold LastNonflatStepUp
    decide⟩
  exact ⟨e, e.symm r, congrArg Subtype.val (e.apply_symm_apply r)⟩

end MetaMathlibExt
