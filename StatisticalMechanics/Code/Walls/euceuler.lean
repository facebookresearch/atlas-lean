/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Mathlib

open scoped BigOperators
open Finset

namespace StatMech.Euc


abbrev Cell := ℤ × ℤ

abbrev Vtx := ℤ × ℤ



def cellVerts (c : Cell) : Finset Vtx :=
  {(c.1, c.2), (c.1 + 1, c.2), (c.1, c.2 + 1), (c.1 + 1, c.2 + 1)}



def cellEdges (c : Cell) : Finset (Sym2 Vtx) :=
  { s((c.1, c.2), (c.1 + 1, c.2)),          
    s((c.1, c.2 + 1), (c.1 + 1, c.2 + 1)),  
    s((c.1, c.2), (c.1, c.2 + 1)),          
    s((c.1 + 1, c.2), (c.1 + 1, c.2 + 1)) } 


def regVerts (K : Finset Cell) : Finset Vtx := K.biUnion cellVerts


def regEdges (K : Finset Cell) : Finset (Sym2 Vtx) := K.biUnion cellEdges



def regChi (K : Finset Cell) : ℤ :=
  (regVerts K).card - (regEdges K).card + K.card




theorem euc_cellVerts_card (c : Cell) : (cellVerts c).card = 4 := by
  obtain ⟨a, b⟩ := c
  unfold cellVerts
  rw [card_insert_of_notMem (by simp), card_insert_of_notMem (by simp),
    card_insert_of_notMem (by simp), card_singleton]


theorem euc_cellEdges_card (c : Cell) : (cellEdges c).card = 4 := by
  obtain ⟨a, b⟩ := c
  unfold cellEdges
  rw [card_insert_of_notMem (by simp), card_insert_of_notMem (by simp),
    card_insert_of_notMem (by simp), card_singleton]



theorem euc_chi_singleton (c : Cell) : regChi {c} = 1 := by
  unfold regChi regVerts regEdges
  rw [singleton_biUnion, singleton_biUnion,
    euc_cellVerts_card, euc_cellEdges_card, card_singleton]
  norm_num





def newVerts (c : Cell) (K : Finset Cell) : ℕ := (cellVerts c \ regVerts K).card



def newEdges (c : Cell) (K : Finset Cell) : ℕ := (cellEdges c \ regEdges K).card


theorem euc_regVerts_insert (c : Cell) (K : Finset Cell) :
    regVerts (insert c K) = cellVerts c ∪ regVerts K := by
  unfold regVerts; rw [biUnion_insert]


theorem euc_regEdges_insert (c : Cell) (K : Finset Cell) :
    regEdges (insert c K) = cellEdges c ∪ regEdges K := by
  unfold regEdges; rw [biUnion_insert]


theorem euc_regVerts_card_insert (c : Cell) (K : Finset Cell) :
    (regVerts (insert c K)).card = newVerts c K + (regVerts K).card := by
  rw [euc_regVerts_insert, newVerts, ← card_sdiff_add_card (cellVerts c) (regVerts K)]


theorem euc_regEdges_card_insert (c : Cell) (K : Finset Cell) :
    (regEdges (insert c K)).card = newEdges c K + (regEdges K).card := by
  rw [euc_regEdges_insert, newEdges, ← card_sdiff_add_card (cellEdges c) (regEdges K)]







theorem euc_chi_insert (c : Cell) (K : Finset Cell) (hc : c ∉ K) :
    regChi (insert c K)
      = regChi K + ((newVerts c K : ℤ) - (newEdges c K : ℤ) + 1) := by
  unfold regChi
  rw [euc_regVerts_card_insert, euc_regEdges_card_insert, card_insert_of_notMem hc]
  push_cast
  ring




theorem euc_chi_attach (c : Cell) (K : Finset Cell) (hc : c ∉ K)
    (harc : newEdges c K = newVerts c K + 1) :
    regChi (insert c K) = regChi K := by
  rw [euc_chi_insert c K hc, harc]
  push_cast; ring











inductive EucBuildable : Finset Cell → Prop
  | singleton (c : Cell) : EucBuildable {c}
  | attach (c : Cell) (K : Finset Cell) (hK : EucBuildable K) (hc : c ∉ K)
      (harc : newEdges c K = newVerts c K + 1) : EucBuildable (insert c K)



theorem euc_chi_induction {K : Finset Cell} (hK : EucBuildable K) : regChi K = 1 := by
  induction hK with
  | singleton c => exact euc_chi_singleton c
  | attach c K _ hc harc ih => rw [euc_chi_attach c K hc harc]; exact ih


theorem euc_buildable_nonempty {K : Finset Cell} (hK : EucBuildable K) : K.Nonempty := by
  induction hK with
  | singleton c => exact ⟨c, mem_singleton_self c⟩
  | attach c K _ _ _ _ => exact ⟨c, mem_insert_self c K⟩









private lemma euc_regChi_eval (K : Finset Cell) :
    regChi K = ((regVerts K).card : ℤ) - (regEdges K).card + K.card := rfl


theorem euc_chi_domino : regChi {((0 : ℤ), (0 : ℤ)), (1, 0)} = 1 := by
  have hv : (regVerts {((0 : ℤ), (0 : ℤ)), (1, 0)}).card = 6 := by decide
  have he : (regEdges {((0 : ℤ), (0 : ℤ)), (1, 0)}).card = 7 := by decide
  rw [euc_regChi_eval, hv, he]
  decide



theorem euc_chi_box2 :
    regChi {((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1), (1, 1)} = 1 := by
  have hv : (regVerts {((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1), (1, 1)}).card = 9 := by decide
  have he : (regEdges {((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1), (1, 1)}).card = 12 := by decide
  rw [euc_regChi_eval, hv, he]
  decide



theorem euc_chi_Ltromino : regChi {((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1)} = 1 := by
  have hv : (regVerts {((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1)}).card = 8 := by decide
  have he : (regEdges {((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1)}).card = 10 := by decide
  rw [euc_regChi_eval, hv, he]
  decide






theorem euc_chi_holeyRing :
    regChi ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)} : Finset Cell) = 0 := by
  have hv : (regVerts ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)}
      : Finset Cell)).card = 16 := by decide
  have he : (regEdges ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)}
      : Finset Cell)).card = 24 := by decide
  rw [euc_regChi_eval, hv, he]
  decide





theorem euc_buildable_domino :
    EucBuildable ({((0:ℤ),(0:ℤ)), (1,0)} : Finset Cell) := by
  have h : (insert ((1:ℤ),(0:ℤ)) {((0:ℤ),(0:ℤ))} : Finset Cell)
      = ({((0:ℤ),(0:ℤ)), (1,0)} : Finset Cell) := by decide
  rw [← h]
  refine EucBuildable.attach ((1:ℤ),(0:ℤ)) {((0:ℤ),(0:ℤ))}
    (EucBuildable.singleton _) (by decide) (by decide)



theorem euc_buildable_Ltromino :
    EucBuildable ({((0:ℤ),(0:ℤ)), (1,0), (0,1)} : Finset Cell) := by
  have h : (insert ((0:ℤ),(1:ℤ)) {((0:ℤ),(0:ℤ)), (1,0)} : Finset Cell)
      = ({((0:ℤ),(0:ℤ)), (1,0), (0,1)} : Finset Cell) := by decide
  rw [← h]
  refine EucBuildable.attach ((0:ℤ),(1:ℤ)) {((0:ℤ),(0:ℤ)), (1,0)}
    euc_buildable_domino (by decide) (by decide)





































end StatMech.Euc
