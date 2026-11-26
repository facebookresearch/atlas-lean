/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Split

/-!
# Degree-zero term of a simplicial splitting

For a simplicial splitting s of X, the only epimorphism index in degree zero is the identity
[0] → [0]. Its cofan map is ι₀ : N₀ → X₀, so the splitting coproduct property provides its
inverse.

The two composites are the identities of N₀ and X₀. Thus the degree-zero summand is
canonically isomorphic to X₀ through its given cofan map. This works in any category with the
specified splitting, with independent object and morphism universes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject.Splitting

variable {C : Type u} [Category.{v} C] {X : SimplicialObject C} (s : Splitting X)

private theorem zeroIndex (a : IndexSet (op ⦋0⦌)) : a = IndexSet.id _ :=
  (a.eqId_iff_len_le).mpr (Nat.zero_le _)

/-- Inverse of the degree-zero splitting map.

For a simplicial splitting s, construct X₀ → N₀ by coproduct descent in degree zero. The only
summand index is identity, so the family consists of the canonical identification with N₀. -/
def zeroInverse : X.obj (op ⦋0⦌) ⟶ s.N 0 :=
  s.desc (op ⦋0⦌) (fun a => eqToHom
    (congrArg (fun b : IndexSet (op ⦋0⦌) => s.N b.1.unop.len)
      ((a.eqId_iff_len_le).mpr (Nat.zero_le _))))

/-- Degree-zero splitting map followed by its inverse.

For a splitting s of X, ι₀ ≫ zeroInverse = id_{N₀}. This is the value of the degree-zero
descendant on its unique coproduct summand. -/
theorem zero_hom_inv : s.ι 0 ≫ s.zeroInverse = 𝟙 (s.N 0) := by
  have h := s.ι_desc (op ⦋0⦌)
    (fun a => eqToHom (congrArg
      (fun b : IndexSet (op ⦋0⦌) => s.N b.1.unop.len) (zeroIndex a))) (IndexSet.id _)
  rw [s.cofan_inj_id 0] at h
  dsimp only [IndexSet.id, summand] at h
  change s.ι 0 ≫ s.zeroInverse = eqToHom (rfl : s.N 0 = s.N 0) at h
  exact h.trans (by rfl)

/-- Degree-zero splitting inverse followed by its cofan map.

For a splitting s, zeroInverse ≫ ι₀ = id_{X₀}. Equality can be tested on the unique
degree-zero summand of the splitting. -/
theorem zero_inv_hom : s.zeroInverse ≫ s.ι 0 = 𝟙 (X.obj (op ⦋0⦌)) := by
  apply s.hom_ext'
  intro a
  obtain rfl := zeroIndex a
  rw [s.cofan_inj_id 0]
  calc
    s.ι 0 ≫ (s.zeroInverse ≫ s.ι 0) = (s.ι 0 ≫ s.zeroInverse) ≫ s.ι 0 :=
      (Category.assoc _ _ _).symm
    _ = s.ι 0 := by rw [s.zero_hom_inv, Category.id_comp]
    _ = s.ι 0 ≫ 𝟙 (X.obj (op ⦋0⦌)) := (Category.comp_id _).symm

/-- Isomorphism from the degree-zero summand to the simplicial term.

For a splitting s of X, zeroIso : N₀ ≅ X₀ has hom ι₀ and inverse zeroInverse, with both
identity equations supplied by the degree-zero coproduct universal property. -/
def zeroIso : s.N 0 ≅ X.obj (op ⦋0⦌) where
  hom := s.ι 0
  inv := s.zeroInverse
  hom_inv_id := s.zero_hom_inv
  inv_hom_id := s.zero_inv_hom

end CategoryTheory.SimplicialObject.Splitting

end
