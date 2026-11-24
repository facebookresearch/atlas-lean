/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatFiber
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatWeylAction
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatMixedCommutation
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatWeylCommutation
public import MathlibExt.GroupTheory.SubgroupClosureCommutation

/-! # Finite-rank Matsumoto action subgroups

Central and left/right permutation subgroups acting on `X F n`.
Central permutations centralize the left and right generated subgroups
without claiming centrality in the full symmetric group.
-/

@[expose] public section

universe u

open Matrix
open Matrix.GeneralLinearGroup

namespace MatsumotoTitsBruhatFiber

-- Central subgroup as the range of `centralHom`.
noncomputable def centralActionSubgroup (F : Type u) [Field F] (n : ℕ) :
    Subgroup (Equiv.Perm (X F n)) :=
  (centralHom (F := F) (n := n)).range

-- Weyl generator sets: all adjacent `leftWeylPerm` / `rightWeylPerm`.
def leftWeylGenerators (F : Type u) [Field F] (n : ℕ) :
    Set (Equiv.Perm (X F n)) :=
  { g | ∃ (i j : Fin n) (hij : i ⋖ j), g = leftWeylPerm (F := F) hij }

def rightWeylGenerators (F : Type u) [Field F] (n : ℕ) :
    Set (Equiv.Perm (X F n)) :=
  { g | ∃ (i j : Fin n) (hij : i ⋖ j), g = rightWeylPerm (F := F) hij }

-- Left/right action generators: upper range plus Weyl generators.
noncomputable def leftActionGenerators (F : Type u) [Field F] (n : ℕ) :
    Set (Equiv.Perm (X F n)) :=
  Set.range (leftUpperPerm (F := F) (n := n)) ∪ leftWeylGenerators F n

noncomputable def rightActionGenerators (F : Type u) [Field F] (n : ℕ) :
    Set (Equiv.Perm (X F n)) :=
  Set.range (rightUpperPerm (F := F) (n := n)) ∪
    rightWeylGenerators F n

-- Generated left/right action subgroups.
noncomputable def leftActionSubgroup (F : Type u) [Field F] (n : ℕ) :
    Subgroup (Equiv.Perm (X F n)) :=
  Subgroup.closure (leftActionGenerators F n)

noncomputable def rightActionSubgroup (F : Type u) [Field F] (n : ℕ) :
    Subgroup (Equiv.Perm (X F n)) :=
  Subgroup.closure (rightActionGenerators F n)

/-! ### Generator membership -/

theorem leftUpperPerm_mem_leftActionSubgroup
    (F : Type u) [Field F] {n : ℕ}
    (u : upperElementarySubgroup (Fin n) F) :
    leftUpperPerm (F := F) (n := n) u ∈ leftActionSubgroup F n := by
  apply Subgroup.subset_closure
  exact Or.inl ⟨u, rfl⟩

theorem rightUpperPerm_mem_rightActionSubgroup
    (F : Type u) [Field F] {n : ℕ}
    (u : upperElementarySubgroup (Fin n) F) :
    rightUpperPerm (F := F) (n := n) u ∈ rightActionSubgroup F n := by
  apply Subgroup.subset_closure
  exact Or.inl ⟨u, rfl⟩

theorem leftWeylPerm_mem_leftActionSubgroup
    (F : Type u) [Field F] {n : ℕ} {i j : Fin n} (hij : i ⋖ j) :
    leftWeylPerm (F := F) hij ∈ leftActionSubgroup F n := by
  apply Subgroup.subset_closure
  exact Or.inr ⟨i, j, hij, rfl⟩

theorem rightWeylPerm_mem_rightActionSubgroup
    (F : Type u) [Field F] {n : ℕ} {i j : Fin n} (hij : i ⋖ j) :
    rightWeylPerm (F := F) hij ∈ rightActionSubgroup F n := by
  apply Subgroup.subset_closure
  exact Or.inr ⟨i, j, hij, rfl⟩

theorem centralPerm_mem_centralActionSubgroup
    (F : Type u) [Field F] {n : ℕ}
    (c : Multiplicative (MilnorK F 2)) :
    centralPerm (F := F) (n := n) c ∈ centralActionSubgroup F n := by
  rw [centralActionSubgroup, MonoidHom.mem_range]
  exact ⟨c, rfl⟩

/-! ### Left/right generatorwise commutation -/

theorem leftActionGenerator_rightActionGenerator_comm
    {F : Type u} [Field F] {n : ℕ}
    {g h : Equiv.Perm (X F n)}
    (hg : g ∈ leftActionGenerators (F := F) (n := n))
    (hh : h ∈ rightActionGenerators (F := F) (n := n)) :
    Commute g h := by
  rcases hg with ⟨u, rfl⟩ | ⟨i, j, hij, rfl⟩
  · rcases hh with ⟨v, rfl⟩ | ⟨k, l, hkl, rfl⟩
    · exact leftUpperPerm_rightUpperPerm_comm (F := F) u v
    · exact leftUpperPerm_rightWeylPerm_comm (F := F) hkl u
  · rcases hh with ⟨v, rfl⟩ | ⟨k, l, hkl, rfl⟩
    · exact leftWeylPerm_rightUpperPerm_comm (F := F) hij v
    · exact leftWeylPerm_rightWeylPerm_comm (F := F) hij hkl

theorem rightActionSubgroup_le_centralizer_leftActionSubgroup
    (F : Type u) [Field F] (n : ℕ) :
    rightActionSubgroup F n ≤
      Subgroup.centralizer (leftActionSubgroup F n) := by
  apply Subgroup.closure_le_centralizer_closure_of_commute
  intro g hg h hh
  exact leftActionGenerator_rightActionGenerator_comm hg hh

theorem leftActionSubgroup_rightActionSubgroup_comm
    {F : Type u} [Field F] {n : ℕ}
    {g h : Equiv.Perm (X F n)}
    (hg : g ∈ leftActionSubgroup (F := F) (n := n))
    (hh : h ∈ rightActionSubgroup (F := F) (n := n)) :
    Commute g h := by
  have h_gen :
      ∀ x ∈ leftActionGenerators (F := F) (n := n),
        ∀ y ∈ rightActionGenerators (F := F) (n := n),
          Commute x y :=
    fun _ hx _ hy => leftActionGenerator_rightActionGenerator_comm hx hy
  exact Subgroup.commute_of_mem_closure h_gen hg hh

/-! ### Central vs left/right generatorwise commutation -/

theorem centralPerm_leftActionGenerator_comm
    {F : Type u} [Field F] {n : ℕ}
    (c : Multiplicative (MilnorK F 2))
    {g : Equiv.Perm (X F n)}
    (hg : g ∈ leftActionGenerators (F := F) (n := n)) :
    Commute (centralPerm (F := F) (n := n) c) g := by
  rcases hg with ⟨u, rfl⟩ | ⟨i, j, hij, rfl⟩
  · exact centralPerm_leftUpperPerm_comm (F := F) c u
  · exact centralPerm_leftWeylPerm_comm (F := F) hij c

theorem centralPerm_rightActionGenerator_comm
    {F : Type u} [Field F] {n : ℕ}
    (c : Multiplicative (MilnorK F 2))
    {g : Equiv.Perm (X F n)}
    (hg : g ∈ rightActionGenerators (F := F) (n := n)) :
    Commute (centralPerm (F := F) (n := n) c) g := by
  rcases hg with ⟨u, rfl⟩ | ⟨i, j, hij, rfl⟩
  · exact centralPerm_rightUpperPerm_comm (F := F) c u
  · exact centralPerm_rightWeylPerm_comm (F := F) hij c

theorem centralActionSubgroup_le_centralizer_leftActionSubgroup
    (F : Type u) [Field F] (n : ℕ) :
    centralActionSubgroup F n ≤
      Subgroup.centralizer (leftActionSubgroup F n) := by
  intro y hy
  rcases MonoidHom.mem_range.mp hy with ⟨c, rfl⟩
  have h_eq :
      Subgroup.centralizer (leftActionSubgroup F n) =
        Subgroup.centralizer (leftActionGenerators F n) := by
    unfold leftActionSubgroup
    rw [Subgroup.centralizer_closure]
  rw [h_eq]
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have h_comm :=
    centralPerm_leftActionGenerator_comm (F := F) (n := n) c hg
  exact h_comm.symm

theorem centralActionSubgroup_le_centralizer_rightActionSubgroup
    (F : Type u) [Field F] (n : ℕ) :
    centralActionSubgroup F n ≤
      Subgroup.centralizer (rightActionSubgroup F n) := by
  intro y hy
  rcases MonoidHom.mem_range.mp hy with ⟨c, rfl⟩
  have h_eq :
      Subgroup.centralizer (rightActionSubgroup F n) =
        Subgroup.centralizer (rightActionGenerators F n) := by
    unfold rightActionSubgroup
    rw [Subgroup.centralizer_closure]
  rw [h_eq]
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have h_comm :=
    centralPerm_rightActionGenerator_comm (F := F) (n := n) c hg
  exact h_comm.symm

end MatsumotoTitsBruhatFiber

end
