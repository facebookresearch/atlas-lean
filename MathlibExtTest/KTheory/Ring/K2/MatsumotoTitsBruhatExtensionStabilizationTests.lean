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

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatExtensionStabilization

@[expose] public section

noncomputable section

open Matrix.GeneralLinearGroup

namespace MatsumotoTitsBruhatFiber

universe u

variable (F : Type u) [Field F] (n : ℕ)

example (g : LeftExtensionSuccGen F n) :
    (leftExtensionSuccGenerators F n).val g =
      LeftExtensionSuccGenSource F n g :=
  leftExtensionSuccGenerators_val g

example : Function.Surjective (LeftExtensionSuccSourceLift F n) :=
  LeftExtensionSuccSourceLift_surjective F n

example (hn : 2 ≤ n) (u : upperElementarySubgroup (Fin n) F) :
    leftExtensionSuccHom F n hn
        ⟨(UpperElementary.toSLHom u, leftUpperPerm (F := F) u),
          leftUpperPair_mem_leftExtensionSubgroup (F := F) (n := n) u⟩ =
      ⟨(UpperElementary.toSLHom (UpperElementary.stabilization F n u),
          leftUpperPerm (F := F) (UpperElementary.stabilization F n u)),
        leftUpperPair_mem_leftExtensionSubgroup (F := F) (n := n + 1)
          (UpperElementary.stabilization F n u)⟩ :=
  leftExtensionSuccHom_upper F n hn u

example (hn : 2 ≤ n) {i j : Fin n} (hij : i ⋖ j) :
    leftExtensionSuccHom F n hn
        ⟨(weylSLUnit i j hij.ne (1 : Fˣ), leftWeylPerm (F := F) hij),
          leftWeylPair_mem_leftExtensionSubgroup (F := F) (n := n) hij⟩ =
      ⟨(weylSLUnit (Fin.castSucc i) (Fin.castSucc j)
          (Fin.castSucc_covBy hij).ne (1 : Fˣ),
          leftWeylPerm (F := F) (Fin.castSucc_covBy hij)),
        leftWeylPair_mem_leftExtensionSubgroup (F := F) (n := n + 1)
          (Fin.castSucc_covBy hij)⟩ :=
  leftExtensionSuccHom_weyl F n hn hij

example (hn : 2 ≤ n) (c : Multiplicative (MilnorK F 2)) :
    leftExtensionSuccHom F n hn
        ⟨((1 : Matrix.SpecialLinearGroup (Fin n) F),
            centralPerm (F := F) c),
          centralPair_mem_leftExtensionSubgroup (F := F) (n := n) c⟩ =
      ⟨((1 : Matrix.SpecialLinearGroup (Fin (n + 1)) F),
          centralPerm (F := F) c),
        centralPair_mem_leftExtensionSubgroup (F := F) (n := n + 1) c⟩ :=
  leftExtensionSuccHom_central F n hn c

end MatsumotoTitsBruhatFiber
