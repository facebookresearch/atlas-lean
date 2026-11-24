/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Order.QuasiFullRootedTree
import Mathlib.Data.Fintype.Prod

/-!
# Tests for the arity of quasi-full rooted trees

Two rooted trees with three elements: the chain `Fin 3`, which is quasi-full 1-ary, and the star
`{p : Fin 2 × Fin 2 // p ≠ (1, 1)}`, whose root `(0, 0)` lies below two incomparable leaves and
which is quasi-full 2-ary.
-/

namespace MetaMathlibExt

-- The three-element chain is quasi-full 1-ary, so it is quasi-full `t'`-ary for no `t' ≥ 3`.
example (t' : ℕ) (ht' : 3 ≤ t') :
    ¬ ∀ x : Fin 3, Nat.card {y : Fin 3 // x ⋖ y} = min (Nat.card (Set.Ici x) - 1) t' :=
  (quasiFullTree_arity (by decide) ⟨0, Fin.zero_le⟩
    (fun _ _ _ _ _ _ => le_total _ _)).2 1 (by decide)
    (by simp only [Nat.card_eq_fintype_card]; decide) t' (by simpa using ht')

-- The chain is not quasi-full 2-ary: its root is covered by one element only.
example : ¬ ∀ x : Fin 3, Nat.card {y : Fin 3 // x ⋖ y} = min (Nat.card (Set.Ici x) - 1) 2 := by
  simp only [Nat.card_eq_fintype_card]
  decide

-- The star is quasi-full 2-ary, that is `(n - 1)`-ary, so it is quasi-full `t`-ary for every
-- `t ≥ 3`. For `t = 3` this shows that the second part needs `t ≤ n - 2`: the star is
-- quasi-full `(n - 1)`-ary and quasi-full `n`-ary.
example (t : ℕ) (ht : 3 ≤ t) : ∀ x : {p : Fin 2 × Fin 2 // p ≠ (1, 1)},
    Nat.card {y : {p : Fin 2 × Fin 2 // p ≠ (1, 1)} // x ⋖ y} =
      min (Nat.card (Set.Ici x) - 1) t := by
  have hcard : Fintype.card {p : Fin 2 × Fin 2 // p ≠ (1, 1)} = 3 := by decide
  have hchain : ∀ x : {p : Fin 2 × Fin 2 // p ≠ (1, 1)}, IsChain (· ≤ ·) (Set.Iic x) := by
    simp only [IsChain, Set.Pairwise, Set.mem_Iic]
    decide
  have htwo : ∀ x : {p : Fin 2 × Fin 2 // p ≠ (1, 1)},
      Nat.card {y : {p : Fin 2 × Fin 2 // p ≠ (1, 1)} // x ⋖ y} =
        min (Nat.card (Set.Ici x) - 1) 2 := by
    simp only [CovBy, lt_iff_le_not_ge]
    simp only [Nat.card_eq_fintype_card]
    decide
  have hroot : ∃ ρ : {p : Fin 2 × Fin 2 // p ≠ (1, 1)}, ∀ x, ρ ≤ x :=
    ⟨⟨(0, 0), of_decide_eq_true rfl⟩, by decide⟩
  exact (quasiFullTree_arity (by rw [hcard]) hroot hchain).1 (by rw [hcard]; exact htwo) t
    (by rw [hcard]; exact ht)

end MetaMathlibExt
