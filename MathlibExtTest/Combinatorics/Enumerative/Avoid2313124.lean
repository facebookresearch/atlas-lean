/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Avoid2313124

open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

-- Putting zero first leaves exactly the choices for the remaining three entries.
example :
    Nat.card {σ : Equiv.Perm (Fin 4) //
      ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124 ∧ σ 0 = 0} =
      Nat.card {σ : Equiv.Perm (Fin 3) // ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124} := by
  simpa using card_avoid_231_3124_pos_zero 4 (by decide) 0 (by decide)

-- At the last allowed position, the suffix is a singleton and the factor is three.
example :
    Nat.card {σ : Equiv.Perm (Fin 4) //
      ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124 ∧ σ 2 = 0} = 3 := by
  have singleton {k : ℕ} (hk : 1 < k) (π : Fin k → Fin k) :
      ¬ HasPattern (Equiv.refl (Fin 1)) π := by
    rintro ⟨e, he, _⟩
    exact (Subsingleton.elim _ _ : e ⟨0, by omega⟩ = e ⟨1, hk⟩) |>.not_lt
      (he _ _ (show (⟨0, by omega⟩ : Fin k) < ⟨1, hk⟩ by exact Nat.zero_lt_one))
  have hcard := Nat.card_of_subsingleton
    (⟨Equiv.refl _, singleton (by decide) pat231, singleton (by decide) pat3124⟩ :
      {σ : Equiv.Perm (Fin 1) // ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124})
  simpa [hcard] using card_avoid_231_3124_pos_zero 4 (by decide) 2 (by decide)
