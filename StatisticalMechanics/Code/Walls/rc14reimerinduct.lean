/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































import Code.Walls.rc11core
import Code.Walls.rc10core
import Code.Walls.rc12reimerinjection

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]






open Classical in


noncomputable def rc14_boxE (E : Finset α) (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  E.powerset.filter (fun S => ∃ K L : Finset α, Disjoint K L ∧ K ⊆ S ∧ L ⊆ S ∧ K ∈ 𝒜 ∧ L ∈ ℬ)

open Classical in


noncomputable def rc14_reflE (E : Finset α) (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  E.powerset.filter (fun S => S ∈ 𝒜 ∧ E \ S ∈ ℬ)

open Classical in

theorem rc14_mem_boxE (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc14_boxE E 𝒜 ℬ ↔
      S ⊆ E ∧ ∃ K L : Finset α, Disjoint K L ∧ K ⊆ S ∧ L ⊆ S ∧ K ∈ 𝒜 ∧ L ∈ ℬ := by
  simp only [rc14_boxE, Finset.mem_filter, Finset.mem_powerset]

open Classical in

theorem rc14_mem_reflE (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc14_reflE E 𝒜 ℬ ↔ S ⊆ E ∧ S ∈ 𝒜 ∧ E \ S ∈ ℬ := by
  simp only [rc14_reflE, Finset.mem_filter, Finset.mem_powerset]

end StatMech.Walls
