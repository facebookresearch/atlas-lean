/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Code.Walls.rc4_core

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]











theorem rc5_downComp_card (i : α) (𝒜 : Finset (Finset α)) :
    (Down.compression i 𝒜).card = 𝒜.card :=
  Down.card_compression i 𝒜


















theorem rc5_iterDownComp_card (cs : List α) (𝒜 : Finset (Finset α)) :
    (iterDownComp cs 𝒜).card = 𝒜.card := by
  induction cs with
  | nil => rw [iterDownComp_nil]
  | cons i cs ih => rw [iterDownComp_cons, rc5_downComp_card, ih]












theorem rc5_iterDownComp_eq_self_of_isLowerSet {𝒜 : Finset (Finset α)}
    (h : IsLowerSet (𝒜 : Set (Finset α))) (cs : List α) :
    iterDownComp cs 𝒜 = 𝒜 :=
  iterDownComp_eq_self_of_isLowerSet h cs




theorem rc5_iterDownComp_card_of_isLowerSet {𝒜 : Finset (Finset α)}
    (h : IsLowerSet (𝒜 : Set (Finset α))) (cs : List α) :
    (iterDownComp cs 𝒜).card = 𝒜.card := by
  rw [rc5_iterDownComp_eq_self_of_isLowerSet h cs]














theorem rc5_iterDownComp_count_mono (cs : List α) (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ)
      ∧ (iterDownComp cs 𝒜).card = 𝒜.card
      ∧ (iterDownComp cs ℬ).card = ℬ.card :=
  ⟨dpairsCount_iterDownComp_mono cs 𝒜 ℬ, rc5_iterDownComp_card cs 𝒜,
    rc5_iterDownComp_card cs ℬ⟩









theorem rc5_iterDownComp_empty (cs : List α) :
    iterDownComp cs (∅ : Finset (Finset α)) = ∅ := by
  rw [← Finset.card_eq_zero, rc5_iterDownComp_card, Finset.card_eq_zero]





theorem rc5_iterDownComp_card_powerset (cs : List α) (s : Finset α) :
    (iterDownComp cs s.powerset).card = 2 ^ s.card := by
  rw [rc5_iterDownComp_card, Finset.card_powerset]
















theorem rc5_itercomp_card (cs : List α) (i : α) (𝒜 : Finset (Finset α)) :
    (Down.compression i 𝒜).card = 𝒜.card ∧ (iterDownComp cs 𝒜).card = 𝒜.card :=
  ⟨rc5_downComp_card i 𝒜, rc5_iterDownComp_card cs 𝒜⟩

end StatMech.Walls
