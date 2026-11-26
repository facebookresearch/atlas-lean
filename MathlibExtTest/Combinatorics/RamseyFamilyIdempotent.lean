/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.RamseyFamilyIdempotent

open MetaMathlibExt

attribute [local instance] Ultrafilter.semigroup

-- For the family of all nonempty sets, the conclusion gives an idempotent of βS.
example {S : Type*} [Semigroup S] [Nonempty S] : ∃ p : Ultrafilter S, p * p = p := by
  have hF : IsRamseyFamily {A : Set S | A.Nonempty} := by
    refine ⟨⟨Set.univ, Set.univ_nonempty⟩, Set.not_nonempty_empty, ?_, ?_⟩
    · exact fun _ _ hA hAB => hA.mono hAB
    · exact fun _ _ hAB => Set.union_nonempty.mp hAB
  obtain ⟨p, _, hp⟩ := exists_idempotent_mem_betaFamily hF (by simp [betaFamily_nonempty_sets])
  exact ⟨p, hp⟩

local instance : Semigroup Bool where
  mul _ y := y
  mul_assoc _ _ _ := rfl

-- In the two-element right-zero semigroup, sets containing true give a proper β(F).
example : ∃ p : Ultrafilter Bool, p * p = p ∧ p = pure true := by
  have hF : IsRamseyFamily {A : Set Bool | true ∈ A} :=
    ⟨⟨Set.univ, Set.mem_univ true⟩, id, fun _ _ hA hAB => hAB hA, fun _ _ h => h⟩
  have hleft := (betaFamily_isLeftIdeal_iff hF).2 (fun _ _ hA => ⟨true, hA, rfl⟩)
  obtain ⟨p, hp, hpp⟩ := exists_idempotent_mem_betaFamily hF (fun p _ q hq => hleft p q hq)
  have hβ : betaFamily {A : Set Bool | true ∈ A} = {pure true} := by
    simpa using (isRamseyFamily_and_betaFamily_eq_of_isClosed
      (isClosed_singleton (x := (pure true : Ultrafilter Bool))) (Set.singleton_nonempty _)).2
  exact ⟨p, hpp, Set.mem_singleton_iff.mp (hβ ▸ hp)⟩
