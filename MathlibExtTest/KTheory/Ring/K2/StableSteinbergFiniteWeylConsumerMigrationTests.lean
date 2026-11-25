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


import MathlibExt.KTheory.Ring.K2.StableSteinbergSimpleRootTransport
import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteStageKernelClosure
import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylKernelMonomial
import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylTorus
import Mathlib.Data.ZMod.Basic

/-!
# Finite-Weyl consumer migration tests

These tests pin the carrier/list compatibility used by the selective Slice C2
migration. They cover empty and singleton words, ranks zero and one, a concrete
characteristic-two word, the head-left permutation orientation, and the
unchanged public bounded-`Nat` consumer surface.
-/

noncomputable section

open Matrix.GeneralLinearGroup
open AlgebraicKTheory
open AlgebraicKTheory.StableSteinberg

namespace MathlibExtTest.KTheory.Ring.K2
namespace StableSteinbergFiniteWeylConsumerMigrationTests

/-- The empty rank-zero word evaluates to the identity in every relevant
carrier. -/
example : FiniteWeylWord.permEval
    ([] : FiniteWeylWord (ZMod 2) (Fin 0)) = 1 := by
  simp

example : FiniteWeylWord.monomialSLEval
    ([] : FiniteWeylWord (ZMod 2) (Fin 0)) = 1 := by
  simp

example : evalFiniteWeylWord
    ([] : FiniteWeylWord (ZMod 2) (Fin 0)) = 1 := by
  simp

/-- A concrete characteristic-two singleton letter. -/
def f2Letter : WeylLetter (ZMod 2) (Fin 2) where
  left := 0
  right := 1
  ne := by decide
  unit := 1

def f2Word : FiniteWeylWord (ZMod 2) (Fin 2) :=
  [f2Letter]

/-- Singleton evaluation preserves the head-left swap orientation. -/
example : FiniteWeylWord.permEval f2Word =
    Equiv.swap (0 : Fin 2) (1 : Fin 2) := by
  simp [f2Word, f2Letter, FiniteWeylWord.permEval,
    WeylLetter.perm]

example : FiniteWeylWord.specialLinearEval f2Word =
    monomialSLHom (ZMod 2) (Fin 2)
      (FiniteWeylWord.monomialSLEval f2Word) :=
  FiniteWeylWord.specialLinearEval_eq_monomialSLHom f2Word

/-- The bounded-`Nat` adapter and the bundled stable evaluation agree for the
concrete singleton word. -/
example :
    evalFiniteWeylWord
        (FiniteWeylWord.ofBoundedNat (n := 2)
          (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 1)
          (fun _ => by decide) (fun _ => by decide)
          (fun _ => by omega) (fun _ => (1 : (ZMod 2)ˣ))) =
      (List.ofFn fun _ : Fin 1 =>
        weyl (R := ZMod 2) 0 1 (by omega) (1 : (ZMod 2)ˣ)).prod := by
  exact evalFiniteWeylWord_ofBoundedNat (n := 2)
    (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 1)
    (fun _ => by decide) (fun _ => by decide)
    (fun _ => by omega) (fun _ => (1 : (ZMod 2)ˣ))

/-- The rank-zero and rank-one finite Weyl carriers remain bottom. -/
example : finiteWeylSubgroup (R := ZMod 2) 0 = ⊥ :=
  finiteWeylSubgroup_zero_eq_bot

example : finiteWeylSubgroup (R := ZMod 2) 1 = ⊥ :=
  finiteWeylSubgroup_one_eq_bot

/- Public compatibility endpoints remain available with their original
bounded-`Nat` signatures. -/
#check finiteWeylPerm_weyl
#check finiteWeyl_conj_x
#check finiteCentralKernel_list_monomial_prod_eq_one
#check ker_toStableE_le_torusCocycleSubgroup
#check finiteWeyl_simpleRoot_mem_borel

#print axioms finiteWeylPerm_weyl
#print axioms finiteWeyl_conj_x
#print axioms finiteCentralKernel_list_monomial_prod_eq_one
#print axioms ker_toStableE_le_torusCocycleSubgroup

end StableSteinbergFiniteWeylConsumerMigrationTests
end MathlibExtTest.KTheory.Ring.K2

end
