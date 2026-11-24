/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.GroupTheory.PermutationRootOverlap
public import MathlibExt.KTheory.Ring.K2.MatsumotoBruhatOppositeWeylTransport

/-!
# Root-overlap classifier bridges for Matsumoto Bruhat transport

This compatibility layer identifies the four historical left/right overlap
predicates with the generic three-way root-overlap classifier.  Keeping the
bridge out of `MatsumotoBruhatOppositeWeylTransport` avoids adding the generic
classifier to the critical Tits-commutation import path before its selective
migration.
-/

@[expose] public section

open PermutationBilinearCocycle

namespace MatsumotoBruhatOppositeWeylTransport

variable {F : Type*} [Field F] {n : ℕ}

theorem posOverlapLR_iff_adjacentOverlapClass_eq_positive
    (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l) :
    PosOverlapLR M hij hkl ↔
      PermutationSchurCocycle.adjacentOverlapClass M.right hij hkl = .positive :=
  (PermutationSchurCocycle.adjacentOverlapClass_eq_positive_iff
    M.right hij hkl).symm

theorem negOverlapLR_iff_adjacentOverlapClass_eq_negative
    (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l) :
    NegOverlapLR M hij hkl ↔
      PermutationSchurCocycle.adjacentOverlapClass M.right hij hkl = .negative := by
  rw [PermutationSchurCocycle.adjacentOverlapClass_eq_negative_iff]
  exact and_comm

theorem posOverlapRL_iff_adjacentOverlapClass_eq_positive
    (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l) :
    PosOverlapRL M hij hkl ↔
      PermutationSchurCocycle.adjacentOverlapClass M.right hij hkl = .positive := by
  rw [PermutationSchurCocycle.adjacentOverlapClass_eq_positive_iff]
  constructor
  · rintro ⟨hki, hlj⟩
    exact ⟨by simpa using (congrArg M.right hki).symm,
      by simpa using (congrArg M.right hlj).symm⟩
  · rintro ⟨hki, hlj⟩
    exact ⟨by simpa using (congrArg M.right.symm hki).symm,
      by simpa using (congrArg M.right.symm hlj).symm⟩

theorem negOverlapRL_iff_adjacentOverlapClass_eq_negative
    (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l) :
    NegOverlapRL M hij hkl ↔
      PermutationSchurCocycle.adjacentOverlapClass M.right hij hkl = .negative := by
  rw [PermutationSchurCocycle.adjacentOverlapClass_eq_negative_iff]
  constructor
  · rintro ⟨hkj, hli⟩
    exact ⟨by simpa using (congrArg M.right hkj).symm,
      by simpa using (congrArg M.right hli).symm⟩
  · rintro ⟨hkj, hli⟩
    exact ⟨by simpa using (congrArg M.right.symm hkj).symm,
      by simpa using (congrArg M.right.symm hli).symm⟩

end MatsumotoBruhatOppositeWeylTransport

end
