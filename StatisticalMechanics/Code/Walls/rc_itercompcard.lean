/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Code.Walls.rmr_compresscard

open Finset
open scoped NNReal FinsetFamily

namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]













noncomputable def iterDownCompress (cs : List E) (𝒜 : Finset (ConfigSpace E)) :
    Finset (ConfigSpace E) :=
  cs.foldr downCompress 𝒜

@[simp] theorem iterDownCompress_nil (𝒜 : Finset (ConfigSpace E)) :
    iterDownCompress [] 𝒜 = 𝒜 := rfl

@[simp] theorem iterDownCompress_cons (i : E) (cs : List E) (𝒜 : Finset (ConfigSpace E)) :
    iterDownCompress (i :: cs) 𝒜 = downCompress i (iterDownCompress cs 𝒜) := rfl















theorem rc_iterDownCompress_card (cs : List E) (𝒜 : Finset (ConfigSpace E)) :
    (iterDownCompress cs 𝒜).card = 𝒜.card := by
  induction cs with
  | nil => rfl
  | cons i cs ih =>
      rw [iterDownCompress_cons, rmr_downCompress_card, ih]
















theorem rc_iterDownCompress_eq_self_of_isDownAtCoord (cs : List E) (𝒜 : Finset (ConfigSpace E))
    (h : ∀ i ∈ cs, IsDownAtCoord i 𝒜) : iterDownCompress cs 𝒜 = 𝒜 := by
  induction cs with
  | nil => rfl
  | cons i cs ih =>
      rw [iterDownCompress_cons, ih (fun j hj => h j (List.mem_cons_of_mem i hj))]
      exact rmr_downCompress_eq_self_of_isDownAtCoord i 𝒜 (h i List.mem_cons_self)









theorem rc_iterDownCompress_empty (cs : List E) :
    iterDownCompress cs (∅ : Finset (ConfigSpace E)) = ∅ := by
  rw [← Finset.card_eq_zero, rc_iterDownCompress_card, Finset.card_eq_zero]




theorem rc_iterDownCompress_univ (cs : List E) :
    iterDownCompress cs (Finset.univ : Finset (ConfigSpace E)) = Finset.univ :=
  rc_iterDownCompress_eq_self_of_isDownAtCoord cs _ (fun i _ => rmr_isDownAtCoord_univ i)



theorem rc_iterDownCompress_card_univ (cs : List E) :
    (iterDownCompress cs (Finset.univ : Finset (ConfigSpace E))).card = 2 ^ Fintype.card E := by
  rw [rc_iterDownCompress_card, Finset.card_univ, Fintype.card_fun, Fintype.card_bool]

end StatMech.Walls
