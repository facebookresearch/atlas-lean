/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















import Code.Walls.rc61doubledbutterfly

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace


def rc62_isDown3 (𝒜 : Finset (Finset (Fin 3))) : Bool :=
  decide (∀ S ∈ 𝒜, ∀ i : Fin 3, i ∈ S → S.erase i ∈ 𝒜)


def rc62_isUp3 (ℬ : Finset (Finset (Fin 3))) : Bool :=
  decide (∀ S ∈ ℬ, ∀ i : Fin 3, i ∉ S → insert i S ∈ ℬ)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in 




theorem rc62_fixpoint_wall_fin3 :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 3)),
      rc62_isDown3 𝒜 = true → rc62_isUp3 ℬ = true →
      (rc20_famCylBoxComp 3 𝒜 ℬ).card ≤ (rc20_reflInterComp 3 𝒜 ℬ).card := by
  decide

end StatMech.Walls
