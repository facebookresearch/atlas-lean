/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ChernikovSubgroupLatticeDimensionKourovka11Problem116

namespace MathlibExt.GroupTheory.ChernikovSubgroupLatticeDimensionKourovka11Problem116Wanted

-- The identity embeds a quasicyclic square in itself.
example (Q : Type) [Group Q] (hQ : IsQuasicyclic Q) : ContainsQuasicyclicSquare (Q × Q) :=
  ⟨Q, inferInstance, hQ, MonoidHom.id _, Function.injective_id⟩

-- With zero quasicyclic factors, a nontrivial finite group still needs at least one linear order.
example (G : Type) [Group G] [Finite G] [Nontrivial G] :
    ∃ (n : ℕ) (L : Fin n → LinearOrder (Subgroup G)), 0 < n ∧
      ∀ H K : Subgroup G, H ≤ K ↔ ∀ i, (L i).le H K := by
  have hG : GroupClassesShared.IsChernikov G := by
    refine ⟨⊥, inferInstance, ?_, inferInstance⟩
    intro x hx y hy
    simp_all
  have hn : ¬ContainsQuasicyclicSquare G := by
    rintro ⟨Q, _, ⟨_, hInf, _⟩, f, hf⟩
    have : Finite (Q × Q) := Finite.of_injective f hf
    exact not_finite (Q × Q)
  obtain ⟨n, L, hL⟩ := chernikovSubgroupLatticeFiniteDimension_holds G hG hn
  refine ⟨n, L, Nat.pos_of_ne_zero (fun he ↦ ?_), hL⟩
  subst n
  exact (not_le_of_gt (bot_lt_top : (⊥ : Subgroup G) < ⊤)) ((hL ⊤ ⊥).mpr (fun i ↦ i.elim0))

end MathlibExt.GroupTheory.ChernikovSubgroupLatticeDimensionKourovka11Problem116Wanted
