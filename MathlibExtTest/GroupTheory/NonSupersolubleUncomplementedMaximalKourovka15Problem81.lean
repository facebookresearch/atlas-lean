/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.NonSupersolubleUncomplementedMaximalKourovka15Problem81

open MathlibExt.GroupTheory.NonSupersolubleUncomplementedMaximalKourovka15Problem81Wanted
open scoped Pointwise

-- Apply the theorem and check that a complement of the witness would have to be the whole group.
example (G : Type) [Group G] [Finite G] (hG : ¬ IsSupersoluble G) :
    ∃ (p : ℕ) (P : Sylow p G) (M : Subgroup G),
      p.Prime ∧ ¬ IsCyclic (P : Subgroup G) ∧ M < P ∧
        (∀ L : Subgroup G, M < L → L ≤ P → L = P) ∧
          ∀ K : Subgroup G, (M : Set G) * (K : Set G) = Set.univ → M ⊓ K = ⊥ → K = ⊤ := by
  obtain ⟨p, hp, P, hP, M, hM, hmax, hnc⟩ :=
    nonSupersolubleHasUncomplementedSylowMaximal_holds G hG
  refine ⟨p, P, M, hp, hP, hM, hmax, fun K hmul hdisj => ?_⟩
  by_contra hK
  exact hnc ⟨K, hK, hmul, hdisj⟩

-- The trivial group admits the series of length zero.
example (G : Type) [Group G] [Subsingleton G] : IsSupersoluble G := by
  exact ⟨0, fun _ => ⊥, rfl, Subsingleton.elim _ _, fun _ => Subgroup.normal_bot,
    fun i => i.elim0⟩
