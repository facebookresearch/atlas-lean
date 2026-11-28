/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.EssentialCRSet
import MathlibExt.Combinatorics.RamseyFamily

open MetaMathlibExt

attribute [local instance] Ultrafilter.addSemigroup

-- A two-element commutative semigroup without an additive identity.
local instance : AddCommSemigroup Bool where
  add _ _ := false
  add_assoc _ _ _ := rfl
  add_comm _ _ := rfl

-- Direct matrix witnesses: the seed can be true, since adding the selected row gives false.
private theorem singleton_matrix_witness :
    ∀ (κ : Type) [Fintype κ], ∃ r : ℕ, ∀ M : Fin r → κ → Bool,
      ∃ R : Finset (Fin r), R.Nonempty ∧ ∃ s : Bool,
        ∀ j, (R.toList.map fun i => M i j).foldl (· + ·) s ∈ ({false} : Set Bool) := by
  intro κ _
  refine ⟨1, fun M => ⟨{0}, Finset.singleton_nonempty _, true, fun j => ?_⟩⟩
  rw [Finset.toList_singleton, List.map_cons, List.foldl_cons]
  exact Set.mem_singleton _

-- The principal ultrafilter at false is idempotent, and every one of its members has the
-- same matrix witnesses. This verifies the ultrafilter side without the sequence theorem.
example : ∃ p : Ultrafilter Bool, p + p = p ∧ (∀ B ∈ p, IsCRSet B) ∧ ({false} : Set Bool) ∈ p := by
  refine ⟨pure false, ?_, ?_, by simp⟩
  · ext B
    rw [show B ∈ (pure false : Ultrafilter Bool) + pure false ↔ false + false ∈ B by rfl]
    rfl
  · intro B hB
    have hfalse : false ∈ B := Ultrafilter.mem_pure.mp hB
    apply isCRSet_iff_fintype.mpr
    intro κ _
    obtain ⟨r, hr⟩ := singleton_matrix_witness κ
    refine ⟨r, fun M => ?_⟩
    obtain ⟨R, hR, s, hs⟩ := hr M
    exact ⟨R, hR, s, fun j => (Set.mem_singleton_iff.mp (hs j)).symm ▸ hfalse⟩

private theorem singleton_sequence :
    ∃ C : ℕ → Set Bool, Antitone C ∧ (∀ n, C n ⊆ {false}) ∧
      (∀ n, ∀ x ∈ C n, ∃ m, C m ⊆ {y : Bool | x + y ∈ C n}) ∧ ∀ n, IsCRSet (C n) :=
  ⟨fun _ => {false}, antitone_const, fun _ => Set.Subset.rfl,
    fun _ _ _ => ⟨0, fun _ _ => Set.mem_singleton _⟩,
    fun _ => isCRSet_iff_fintype.mpr singleton_matrix_witness⟩

-- Client example: construct essentiality from an explicit constant sequence.
example : IsEssentialCRSet ({false} : Set Bool) :=
  (isEssentialCRSet_iff_exists_decreasing_sequence _).mpr singleton_sequence

-- Verify the union criterion's conditions directly for the family of subsets containing false.
private theorem containsFalse_union_criterion :
    let F : Set (Set Bool) := {A | false ∈ A}
    Set.univ ∈ F ∧ ∅ ∉ F ∧ ∀ A B, A ∪ B ∈ F ↔ A ∈ F ∨ B ∈ F :=
  ⟨Set.mem_univ false, Set.notMem_empty false, fun A B => Set.mem_union false A B⟩

example : IsRamseyFamily {A : Set Bool | false ∈ A} :=
  isRamseyFamily_iff_univ_empty_union.mpr containsFalse_union_criterion

local instance : AddCommSemigroup Empty where
  add x _ := x
  add_assoc x := Empty.elim x
  add_comm x := Empty.elim x

-- On an empty carrier, even the zero-column case cannot supply a shift. No CR sequence exists.
example : ¬ ∃ C : ℕ → Set Empty, ∀ n, IsCRSet (C n) := by
  rintro ⟨C, hC⟩
  obtain ⟨r, hr⟩ := isCRSet_iff_fintype.mp (hC 0) (Fin 0)
  obtain ⟨_, _, s, _⟩ := hr fun _ => Fin.elim0
  exact Empty.elim s
