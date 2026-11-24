/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Ring.K2.MatsumotoBruhatOverlapClassifier

@[expose] public section

open Matrix.GeneralLinearGroup
open MatsumotoBruhatOppositeWeylTransport
open PermutationBilinearCocycle
open PermutationSchurCocycle

namespace PermutationRootOverlapTests

private abbrev h01Fin3 : (0 : Fin 3) ⋖ 1 := by simp
private abbrev h12Fin4 : (1 : Fin 4) ⋖ 2 := by simp
private abbrev h01Fin4 : (0 : Fin 4) ⋖ 1 := by simp
private abbrev h23Fin4 : (2 : Fin 4) ⋖ 3 := by simp
private def root01Fin3 : Root 3 := ⟨(0, 1), by decide⟩

example : adjacentOverlapClass (1 : Equiv.Perm (Fin 3)) h01Fin3 h01Fin3 = .positive := by
  exact adjacentOverlapClass_one_self h01Fin3

example : adjacentOverlapClass (Equiv.swap 0 1) h01Fin3 h01Fin3 = .negative := by
  rw [adjacentOverlapClass_eq_negative_iff]
  simp

example : adjacentOverlapClass
    (Equiv.swap 0 1 * Equiv.swap 0 1) h01Fin3 h01Fin3 = .positive := by
  rw [Equiv.swap_mul_self]
  exact adjacentOverlapClass_one_self h01Fin3

example : (rootTransport (1 : Equiv.Perm (Fin 3)) root01Fin3).orientation = 0 := by
  simp

example : adjacentOverlapClass (1 : Equiv.Perm (Fin 4)) h01Fin4 h12Fin4 = .none := by
  rw [adjacentOverlapClass_eq_none_iff]
  decide

example : adjacentOverlapClass (1 : Equiv.Perm (Fin 4)) h01Fin4 h23Fin4 = .none := by
  rw [adjacentOverlapClass_eq_none_iff]
  decide

example (p q : Equiv.Perm (Fin 4)) (target source : Root 4) :
    rootOverlapClass (p * q) target source =
      RootOverlapClass.comp
        (rootOverlapClass p target (rootPerm q source))
        (rootOverlapClass q (rootPerm q source) source) :=
  rootOverlapClass_mul p q target source

example (p : Equiv.Perm (Fin 4)) (target source : Root 4) :
    rootOverlapClass p⁻¹ source target = rootOverlapClass p target source :=
  rootOverlapClass_inv p target source

example (p : Equiv.Perm (Fin 3)) :
    adjacentOverlapClass (Equiv.swap 0 1 * p) h01Fin3 h01Fin3 =
      RootOverlapClass.flip (adjacentOverlapClass p h01Fin3 h01Fin3) :=
  adjacentOverlapClass_left_swap p h01Fin3 h01Fin3

example (p : Equiv.Perm (Fin 3)) :
    adjacentOverlapClass (p * Equiv.swap 0 1) h01Fin3 h01Fin3 =
      RootOverlapClass.flip (adjacentOverlapClass p h01Fin3 h01Fin3) :=
  adjacentOverlapClass_right_swap p h01Fin3 h01Fin3

example {A B : Type} [Group A] [Group B] (f : A →* B)
    (M : MonomialBase A (Fin 3)) :
    adjacentOverlapClass (monomialBaseHom f M).right h01Fin3 h01Fin3 =
      adjacentOverlapClass M.right h01Fin3 h01Fin3 :=
  adjacentOverlapClass_monomialBaseHom f M h01Fin3 h01Fin3

section Legacy

variable {F : Type} [Field F] (M : MonomialBase Fˣ (Fin 3))

example : PosOverlapLR M h01Fin3 h01Fin3 ↔
    adjacentOverlapClass M.right h01Fin3 h01Fin3 = .positive :=
  posOverlapLR_iff_adjacentOverlapClass_eq_positive M h01Fin3 h01Fin3

example : NegOverlapLR M h01Fin3 h01Fin3 ↔
    adjacentOverlapClass M.right h01Fin3 h01Fin3 = .negative :=
  negOverlapLR_iff_adjacentOverlapClass_eq_negative M h01Fin3 h01Fin3

example : PosOverlapRL M h01Fin3 h01Fin3 ↔
    adjacentOverlapClass M.right h01Fin3 h01Fin3 = .positive :=
  posOverlapRL_iff_adjacentOverlapClass_eq_positive M h01Fin3 h01Fin3

example : NegOverlapRL M h01Fin3 h01Fin3 ↔
    adjacentOverlapClass M.right h01Fin3 h01Fin3 = .negative :=
  negOverlapRL_iff_adjacentOverlapClass_eq_negative M h01Fin3 h01Fin3

example : Decidable (PosOverlapLR M h01Fin3 h01Fin3) := inferInstance
example : Decidable (NegOverlapLR M h01Fin3 h01Fin3) := inferInstance
example : Decidable (PosOverlapRL M h01Fin3 h01Fin3) := inferInstance
example : Decidable (NegOverlapRL M h01Fin3 h01Fin3) := inferInstance

example (M₂ : MonomialBase (ZMod 2)ˣ (Fin 3)) :
    Decidable (adjacentOverlapClass M₂.right h01Fin3 h01Fin3 = .negative) :=
  inferInstance

end Legacy

end PermutationRootOverlapTests

end
