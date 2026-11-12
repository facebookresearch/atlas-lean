/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































import Mathlib
import Code.Walls.bof2leafcount
import Code.Walls.bgf2faithcontract

open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls







def bfct_restrict {V : Type*} (G : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∈ S} :=
  G.comap Subtype.val

instance bfct_restrict_decAdj {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    DecidableRel (bfct_restrict G S).Adj :=
  fun a b => inferInstanceAs (Decidable (G.Adj (a : V) (b : V)))

@[simp] theorem bfct_restrict_adj {V : Type*} (G : SimpleGraph V) (S : Finset V)
    (a b : {v // v ∈ S}) : (bfct_restrict G S).Adj a b ↔ G.Adj (a : V) (b : V) :=
  Iff.rfl

#check @bfct_restrict











def bfct_delHom {V : Type*} (G : SimpleGraph V) (S : Finset V) (t : {v // v ∈ S}) :
    bkg_deleteVertex (bfct_restrict G S) t →g bkg_deleteVertex G (t : V) :=
  { toFun := Subtype.val
    map_rel' := by
      rintro a b ⟨hadj, hat, hbt⟩
      exact ⟨hadj, fun h => hat (Subtype.ext h), fun h => hbt (Subtype.ext h)⟩ }



theorem bfct_reach_transport {V : Type*} {G : SimpleGraph V} {S : Finset V} {t a b : {v // v ∈ S}}
    (h : (bkg_deleteVertex (bfct_restrict G S) t).Reachable a b) :
    (bkg_deleteVertex G (t : V)).Reachable (a : V) (b : V) :=
  h.map (bfct_delHom G S t)





theorem bfct_cut_transport {V : Type*} {G : SimpleGraph V} {S : Finset V} {t a b : {v // v ∈ S}}
    (h : ¬ (bkg_deleteVertex G (t : V)).Reachable (a : V) (b : V)) :
    ¬ (bkg_deleteVertex (bfct_restrict G S) t).Reachable a b :=
  fun hr => h (bfct_reach_transport hr)

#check @bfct_cut_transport


















theorem bfct_count {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {T : SimpleGraph {v // v ∈ S}} [DecidableRel T.Adj]
    (hTH : T ≤ bfct_restrict G S) (hT : T.IsTree)
    {ι : Type*} [Fintype ι] (f : ι → {v // v ∈ S}) (hf : Function.Injective f)
    (hcut : ∀ i, ∃ a₁ a₂ a₃ : {v // v ∈ S},
        a₁ ≠ f i ∧ a₂ ≠ f i ∧ a₃ ≠ f i ∧
        ¬ (bkg_deleteVertex G (f i : V)).Reachable (a₁ : V) (a₂ : V) ∧
        ¬ (bkg_deleteVertex G (f i : V)).Reachable (a₁ : V) (a₃ : V) ∧
        ¬ (bkg_deleteVertex G (f i : V)).Reachable (a₂ : V) (a₃ : V))
    (B : Finset {v // v ∈ S}) (hleaf : ∀ v, T.degree v = 1 → v ∈ B) :
    Fintype.card ι ≤ B.card := by
  refine bof2_trifCount_le_boundary hTH hT f hf ?_ B hleaf
  intro i
  obtain ⟨a₁, a₂, a₃, hn₁, hn₂, hn₃, hs₁₂, hs₁₃, hs₂₃⟩ := hcut i
  exact ⟨a₁, a₂, a₃, hn₁, hn₂, hn₃,
    bfct_cut_transport hs₁₂, bfct_cut_transport hs₁₃, bfct_cut_transport hs₂₃⟩

#check @bfct_count













theorem bfct_hub_cut_of_separation {V : Type*} {G : SimpleGraph V} {S : Finset V} (hub : {v // v ∈ S})
    {w₁ w₂ w₃ : V} (hw₁ : w₁ ∈ S) (hw₂ : w₂ ∈ S) (hw₃ : w₃ ∈ S)
    (hn₁ : w₁ ≠ (hub : V)) (hn₂ : w₂ ≠ (hub : V)) (hn₃ : w₃ ≠ (hub : V))
    (hs₁₂ : ¬ (bkg_deleteVertex G (hub : V)).Reachable w₁ w₂)
    (hs₁₃ : ¬ (bkg_deleteVertex G (hub : V)).Reachable w₁ w₃)
    (hs₂₃ : ¬ (bkg_deleteVertex G (hub : V)).Reachable w₂ w₃) :
    ∃ a₁ a₂ a₃ : {v // v ∈ S}, a₁ ≠ hub ∧ a₂ ≠ hub ∧ a₃ ≠ hub ∧
      ¬ (bkg_deleteVertex G (hub : V)).Reachable (a₁ : V) (a₂ : V) ∧
      ¬ (bkg_deleteVertex G (hub : V)).Reachable (a₁ : V) (a₃ : V) ∧
      ¬ (bkg_deleteVertex G (hub : V)).Reachable (a₂ : V) (a₃ : V) :=
  ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩, ⟨w₃, hw₃⟩,
    fun h => hn₁ (congrArg Subtype.val h),
    fun h => hn₂ (congrArg Subtype.val h),
    fun h => hn₃ (congrArg Subtype.val h),
    hs₁₂, hs₁₃, hs₂₃⟩






theorem bfct_origin_feed {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ} (h : bao_AllOpenTrif ω L)
    {S : Finset (Site 2)} (h0S : (0 : Site 2) ∈ S)
    (hmem : ∀ w₁ w₂ w₃ : Site 2, w₁ ≠ 0 → w₂ ≠ 0 → w₃ ≠ 0 → w₁ ∈ S ∧ w₂ ∈ S ∧ w₃ ∈ S) :
    ∃ a₁ a₂ a₃ : {v // v ∈ S}, a₁ ≠ (⟨0, h0S⟩ : {v // v ∈ S}) ∧ a₂ ≠ ⟨0, h0S⟩ ∧ a₃ ≠ ⟨0, h0S⟩ ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable (a₁ : Site 2) (a₂ : Site 2) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable (a₁ : Site 2) (a₃ : Site 2) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable (a₂ : Site 2) (a₃ : Site 2) := by
  obtain ⟨w₁, w₂, w₃, hne₁, hne₂, hne₃, hcut₁₂, hcut₁₃, hcut₂₃⟩ := bgf2_trif_separation h
  obtain ⟨hm₁, hm₂, hm₃⟩ := hmem w₁ w₂ w₃ hne₁ hne₂ hne₃
  exact bfct_hub_cut_of_separation (G := bgf2_Gf ω L) ⟨0, h0S⟩ hm₁ hm₂ hm₃
    hne₁ hne₂ hne₃ hcut₁₂ hcut₁₃ hcut₂₃









def bfct_star : SimpleGraph (Fin 4) := SimpleGraph.fromEdgeSet {s(0, 1), s(0, 2), s(0, 3)}

instance : DecidableRel bfct_star.Adj := by unfold bfct_star; infer_instance

instance bfct_delDec {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (t : V) :
    DecidableRel (bkg_deleteVertex G t).Adj :=
  fun a b => decidable_of_iff _ (bkg_deleteVertex_adj G t a b).symm


theorem bfct_reach_isolated {V : Type*} {H : SimpleGraph V} {u : V}
    (hiso : ∀ z, ¬ H.Adj u z) {a : V} (h : H.Reachable a u) : a = u := by
  obtain ⟨w⟩ := h.symm
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hiso _)


def bfct_starS : Finset (Fin 4) := {0, 1, 2}



theorem bfct_star_cut : ¬ (bkg_deleteVertex bfct_star (0 : Fin 4)).Reachable 1 2 := by
  have hiso : ∀ z, ¬ (bkg_deleteVertex bfct_star 0).Adj 1 z := by decide
  intro h
  exact absurd (bfct_reach_isolated hiso h.symm) (by decide)





theorem bfct_transport_witness :
    ¬ (bkg_deleteVertex (bfct_restrict bfct_star bfct_starS)
        (⟨0, by decide⟩ : {v // v ∈ bfct_starS})).Reachable
        (⟨1, by decide⟩ : {v // v ∈ bfct_starS}) (⟨2, by decide⟩ : {v // v ∈ bfct_starS}) :=
  bfct_cut_transport (by
    show ¬ (bkg_deleteVertex bfct_star (0 : Fin 4)).Reachable 1 2
    exact bfct_star_cut)

#check @bfct_transport_witness













































theorem bfct_status :
    
    (∀ {V : Type} {G : SimpleGraph V} {S : Finset V} {t a b : {v // v ∈ S}},
      ¬ (bkg_deleteVertex G (t : V)).Reachable (a : V) (b : V) →
      ¬ (bkg_deleteVertex (bfct_restrict G S) t).Reachable a b) ∧
    
    (∀ {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
      {T : SimpleGraph {v // v ∈ S}} [_i : DecidableRel T.Adj],
      T ≤ bfct_restrict G S → T.IsTree →
      ∀ {ι : Type} [Fintype ι] (f : ι → {v // v ∈ S}), Function.Injective f →
      (∀ i, ∃ a₁ a₂ a₃ : {v // v ∈ S}, a₁ ≠ f i ∧ a₂ ≠ f i ∧ a₃ ≠ f i ∧
        ¬ (bkg_deleteVertex G (f i : V)).Reachable (a₁ : V) (a₂ : V) ∧
        ¬ (bkg_deleteVertex G (f i : V)).Reachable (a₁ : V) (a₃ : V) ∧
        ¬ (bkg_deleteVertex G (f i : V)).Reachable (a₂ : V) (a₃ : V)) →
      ∀ (B : Finset {v // v ∈ S}), (∀ v, T.degree v = 1 → v ∈ B) → Fintype.card ι ≤ B.card) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ), bao_AllOpenTrif ω L →
      ∃ w₁ w₂ w₃ : Site 2, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ w₃ ≠ 0 ∧
        ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₂ ∧
        ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₃ ∧
        ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₂ w₃) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V G S t a b h; exact bfct_cut_transport h
  · intro V _ G _ S T _ hTH hT ι _ f hf hcut B hleaf
    exact bfct_count G S hTH hT f hf hcut B hleaf
  · intro ω L h; exact bgf2_trif_separation h

#check @bfct_status

end StatMech.Walls


#print axioms StatMech.Walls.bfct_restrict
#print axioms StatMech.Walls.bfct_cut_transport
#print axioms StatMech.Walls.bfct_count
#print axioms StatMech.Walls.bfct_hub_cut_of_separation
#print axioms StatMech.Walls.bfct_origin_feed
#print axioms StatMech.Walls.bfct_transport_witness
#print axioms StatMech.Walls.bfct_status
