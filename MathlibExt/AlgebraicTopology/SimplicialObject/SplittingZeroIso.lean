/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Split

/-!
# The actual distinguished zero summand of a native simplicial splitting

There is only the identity epi index over [0]. Native coproduct descent and
its characteristic therefore earn the original inclusion's inverse. This
general categorical provider does not assume the desired IsIso certificate
and imposes no free/flat/projective or global coproduct hypothesis.
Source proposals only; UNEXECUTED.
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

def zeroInverse : X.obj (op ⦋0⦌) ⟶ s.N 0 :=
  s.desc (op ⦋0⦌) (fun a => eqToHom
    (congrArg (fun b : IndexSet (op ⦋0⦌) => s.N b.1.unop.len)
      ((a.eqId_iff_len_le).mpr (Nat.zero_le _))))

theorem zero_hom_inv : s.ι 0 ≫ s.zeroInverse = 𝟙 (s.N 0) := by
  have h := s.ι_desc (op ⦋0⦌)
    (fun a => eqToHom (congrArg
      (fun b : IndexSet (op ⦋0⦌) => s.N b.1.unop.len) (zeroIndex a))) (IndexSet.id _)
  rw [s.cofan_inj_id 0] at h
  dsimp only [IndexSet.id, summand] at h
  change s.ι 0 ≫ s.zeroInverse = eqToHom (rfl : s.N 0 = s.N 0) at h
  exact h.trans (by rfl)

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

/-- The zero summand is identified by its original native inclusion map. -/
def zeroIso : s.N 0 ≅ X.obj (op ⦋0⦌) where
  hom := s.ι 0
  inv := s.zeroInverse
  hom_inv_id := s.zero_hom_inv
  inv_hom_id := s.zero_inv_hom

end CategoryTheory.SimplicialObject.Splitting

end
