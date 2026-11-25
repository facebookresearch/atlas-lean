/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Category.ModuleCat.Colimits
import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ProjectedRetraction

/-! # Low-degree clients for the bisimplicial Eilenberg–Zilber maps -/

open AlgebraicTopology CategoryTheory Simplicial
open scoped Simplicial

namespace BisimplicialEilenbergZilberTests

open AlgebraicTopology.EilenbergZilber

private def transposedShuffle : Shuffle 1 1 where
  perm := Equiv.swap (0 : Fin 2) 1
  isShuffle := by
    constructor <;> intro i j h <;> exact (False.elim (by omega))

private def degreeTwoIndex : ShihIndex 2 := ⟨0, 1, transposedShuffle⟩

example : degreeTwoIndex.gap = 1 := rfl

-- The two words differ: the first sends vertex 2 to 0, the second sends it to 2.
example : (degreeTwoIndex.leftHom.toOrderHom 2).val = 0 := by decide
example : (degreeTwoIndex.rightHom.toOrderHom 2).val = 2 := by decide

private theorem degreeTwoSign : degreeTwoIndex.sign = -1 := by
  have h : (0 : Fin 2) ≠ 1 := by decide
  change (↑(Equiv.Perm.sign (Equiv.swap (0 : Fin 2) 1)) : ℤ) = -1
  rw [Equiv.Perm.sign_swap h]
  rfl

private noncomputable def integers : SimplicialObject (SimplicialObject (ModuleCat ℤ)) :=
  (Functor.const _).obj ((Functor.const _).obj (ModuleCat.of ℤ ℤ))

-- On constant integral chains the underlying map is the identity; the signed term
-- still sends 1 to -1. In particular this is not a vacuous zero/empty-index check.
example : (BisimplicialEilenbergZilber.shihSummand integers degreeTwoIndex) (1 : ℤ) =
    (-1 : ℤ) := by
  have h : BisimplicialEilenbergZilber.shihMap integers degreeTwoIndex =
      𝟙 (ModuleCat.of ℤ ℤ) := by
    simp [BisimplicialEilenbergZilber.shihMap, Bisimplicial.map, integers]
  rw [BisimplicialEilenbergZilber.shihSummand, degreeTwoSign, h]
  change ((-1 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) 1 = -1
  simp

private theorem transposed_ne_block : transposedShuffle ≠ Shuffle.blockShuffle 1 1 := by
  intro h
  have he := congrArg (fun s : Shuffle 1 1 => s.perm (0 : Fin 2)) h
  change (1 : Fin 2) = 0 at he
  exact (by decide : (1 : Fin 2) ≠ 0) he

-- At the original cut the nonblock shuffle is killed by normalization.
example : BisimplicialNormalization.projectedShuffleAlexanderWhitneyTerm
    integers 1 1 transposedShuffle ⟨1, by decide⟩ = 0 :=
  BisimplicialNormalization.projectedTerm_eq_zero_of_shuffle_ne
    integers 1 1 transposedShuffle transposed_ne_block

local notation "P" => BisimplicialNormalization.totalPInfty integers
local notation "aw" => BisimplicialAlexanderWhitney.alternatingMap integers
local notation "ez" => BisimplicialEilenbergZilber.alternatingMap integers

example : P ≫ ez ≫ aw ≫ P = P := BisimplicialNormalization.projectedStrictRetraction integers

end BisimplicialEilenbergZilberTests
