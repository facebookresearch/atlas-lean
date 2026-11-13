/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.BeffaraDC.TorusCellCrossing
import Code.BeffaraDC.TorusDefectComplement

open SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Lattice
open StatMech.Onsager




noncomputable def torusCellPrimalOfDualEdge (L : ℕ) [Fact (2 < L)]
    (e : Sym2 (ZMod L × ZMod L)) : Sym2 (ZMod L × ZMod L) :=
  if he : e ∈ (onsTorusGraph L).edgeFinset then
    ((torusCellCrossing L).symm ⟨e, he⟩ : TorusAmbientEdge L)
  else e

theorem torusCellPrimalOfDualEdge_of_mem (L : ℕ) [Fact (2 < L)]
    {e : Sym2 (ZMod L × ZMod L)}
    (he : e ∈ (onsTorusGraph L).edgeFinset) :
    torusCellPrimalOfDualEdge L e =
      ((torusCellCrossing L).symm ⟨e, he⟩ : TorusAmbientEdge L) := by
  simp [torusCellPrimalOfDualEdge, he]


theorem torusCellPrimalOfDualEdge_mem (L : ℕ) [Fact (2 < L)]
    {e : Sym2 (ZMod L × ZMod L)}
    (he : e ∈ (onsTorusGraph L).edgeFinset) :
    torusCellPrimalOfDualEdge L e ∈ (onsTorusGraph L).edgeFinset := by
  rw [torusCellPrimalOfDualEdge_of_mem L he]
  exact ((torusCellCrossing L).symm ⟨e, he⟩).2


theorem torusCellPrimalOfDualEdge_injOn (L : ℕ) [Fact (2 < L)] :
    Set.InjOn (torusCellPrimalOfDualEdge L)
      (↑(onsTorusGraph L).edgeFinset : Set (Sym2 (ZMod L × ZMod L))) := by
  intro e he e' he' h
  have he0 : e ∈ (onsTorusGraph L).edgeFinset := he
  have he1 : e' ∈ (onsTorusGraph L).edgeFinset := he'
  rw [torusCellPrimalOfDualEdge_of_mem L he0,
    torusCellPrimalOfDualEdge_of_mem L he1] at h
  exact congrArg Subtype.val ((torusCellCrossing L).symm.injective
    (Subtype.ext h))



noncomputable def torusCellDualCutGraph (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) :
    SimpleGraph (ZMod L × ZMod L) where
  Adj f g := (onsTorusGraph L).Adj f g ∧
    torusCellPrimalOfDualEdge L s(f, g) ∉ G.edgeSet
  symm := by
    rintro f g ⟨hfg, hwall⟩
    refine ⟨hfg.symm, ?_⟩
    simpa [Sym2.eq_swap] using hwall
  loopless := ⟨fun f h => (onsTorusGraph L).irrefl h.1⟩

@[simp] theorem torusCellDualCutGraph_adj (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) (f g : ZMod L × ZMod L) :
    (torusCellDualCutGraph L G).Adj f g ↔
      (onsTorusGraph L).Adj f g ∧
        torusCellPrimalOfDualEdge L s(f, g) ∉ G.edgeSet := Iff.rfl


noncomputable def torusCellDualConfig (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    ConfigSpace (Sym2 (ZMod L × ZMod L)) := fun e =>
  if he : e ∈ (onsTorusGraph L).edgeFinset then
    !(ω (torusCellPrimalOfDualEdge L e))
  else false



theorem torusCellPrimal_mem_openSub_iff (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L)))
    {e : Sym2 (ZMod L × ZMod L)}
    (he : e ∈ (onsTorusGraph L).edgeFinset) :
    torusCellPrimalOfDualEdge L e ∈
        (FK.openSub (onsTorusGraph L) ω).edgeSet ↔
      ω (torusCellPrimalOfDualEdge L e) = true := by
  let pe := torusCellPrimalOfDualEdge L e
  have hp : pe ∈ (onsTorusGraph L).edgeFinset := by
    simpa [pe] using torusCellPrimalOfDualEdge_mem L he
  change pe ∈ (FK.openSub (onsTorusGraph L) ω).edgeSet ↔ ω pe = true
  revert hp
  induction pe using Sym2.inductionOn with
  | _ p q =>
      intro hp
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hp
      rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
      exact and_iff_right hp



theorem torusCell_openSub_dualConfig (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    FK.openSub (onsTorusGraph L) (torusCellDualConfig L ω) =
      torusCellDualCutGraph L (FK.openSub (onsTorusGraph L) ω) := by
  ext f g
  by_cases hfg : (onsTorusGraph L).Adj f g
  · have he : s(f, g) ∈ (onsTorusGraph L).edgeFinset := by
      simpa only [SimpleGraph.mem_edgeFinset]
    simp only [FK.openSub_adj, torusCellDualCutGraph_adj, hfg, true_and,
      torusCellDualConfig, dif_pos he]
    rw [torusCellPrimal_mem_openSub_iff L ω he]
    cases ω (torusCellPrimalOfDualEdge L s(f, g)) <;> simp
  · simp [FK.openSub_adj, torusCellDualCutGraph_adj, hfg]



theorem torusCell_dual_openCount (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    FK.openCount (onsTorusGraph L) (torusCellDualConfig L ω) =
      (onsTorusGraph L).edgeFinset.card -
        FK.openCount (onsTorusGraph L) ω := by
  classical
  unfold FK.openCount
  let E := (onsTorusGraph L).edgeFinset
  have hopen : E.filter (fun e => torusCellDualConfig L ω e = true) =
      E.filter (fun e => ω (torusCellPrimalOfDualEdge L e) = false) := by
    ext e
    simp only [Finset.mem_filter]
    by_cases he : e ∈ E
    · have he' : e ∈ (onsTorusGraph L).edgeFinset := by
        simpa [E] using he
      simp only [he, true_and, torusCellDualConfig, dif_pos he']
      cases ω (torusCellPrimalOfDualEdge L e) <;> simp
    · simp [he]
  rw [hopen]
  have hcard :
      (E.filter (fun e => ω (torusCellPrimalOfDualEdge L e) = false)).card =
        (E.filter (fun e => ω e = false)).card := by
    apply Finset.card_bij
        (fun e (_he : e ∈ E.filter
          (fun e => ω (torusCellPrimalOfDualEdge L e) = false)) =>
            torusCellPrimalOfDualEdge L e)
    · intro e he
      simp only [Finset.mem_filter] at he ⊢
      exact ⟨torusCellPrimalOfDualEdge_mem L he.1, he.2⟩
    · intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).1
      have hb' := (Finset.mem_filter.mp hb).1
      exact torusCellPrimalOfDualEdge_injOn L ha' hb' hab
    · intro b hb
      simp only [Finset.mem_filter] at hb
      let eb : TorusAmbientEdge L := ⟨b, hb.1⟩
      let d : Sym2 (ZMod L × ZMod L) :=
        (torusCellCrossing L eb : TorusAmbientEdge L)
      have hd : d ∈ E := (torusCellCrossing L eb).2
      have hdb : torusCellPrimalOfDualEdge L d = b := by
        rw [torusCellPrimalOfDualEdge_of_mem L hd]
        exact congrArg Subtype.val ((torusCellCrossing L).symm_apply_apply eb)
      refine ⟨d, ?_, hdb⟩
      simp only [Finset.mem_filter]
      exact ⟨hd, hdb ▸ hb.2⟩
  rw [hcard]
  have hc := Finset.card_filter_add_card_filter_not
    (s := E) (fun e => ω e = true)
  have hnot : E.filter (fun e => ¬ ω e = true) =
      E.filter (fun e => ω e = false) := by
    ext e
    simp only [Finset.mem_filter]
    cases ω e <;> simp
  rw [hnot] at hc
  change (E.filter (fun e => ω e = false)).card =
    E.card - (E.filter (fun e => ω e = true)).card
  omega


@[simp] theorem torusCellDualCutGraph_bot (L : ℕ) [Fact (2 < L)] :
    torusCellDualCutGraph L
      (⊥ : SimpleGraph (ZMod L × ZMod L)) = onsTorusGraph L := by
  ext f g
  simp [torusCellDualCutGraph_adj]


theorem torusCellDualCutGraph_full (L : ℕ) [Fact (2 < L)] :
    torusCellDualCutGraph L (onsTorusGraph L) = ⊥ := by
  ext f g
  simp only [torusCellDualCutGraph_adj, bot_adj, iff_false]
  rintro ⟨hfg, hwall⟩
  apply hwall
  have heSet : s(f, g) ∈ (onsTorusGraph L).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact hfg
  have he : s(f, g) ∈ (onsTorusGraph L).edgeFinset := by
    simpa [SimpleGraph.edgeFinset] using heSet
  have hp := torusCellPrimalOfDualEdge_mem L he
  simpa [SimpleGraph.edgeFinset] using hp


noncomputable def torusCellDualOfPrimalEdge (L : ℕ) [Fact (2 < L)]
    (e : Sym2 (ZMod L × ZMod L)) : Sym2 (ZMod L × ZMod L) :=
  if he : e ∈ (onsTorusGraph L).edgeFinset then
    (torusCellCrossing L ⟨e, he⟩ : TorusAmbientEdge L)
  else e

theorem torusCellDualOfPrimalEdge_of_mem (L : ℕ) [Fact (2 < L)]
    {e : Sym2 (ZMod L × ZMod L)}
    (he : e ∈ (onsTorusGraph L).edgeFinset) :
    torusCellDualOfPrimalEdge L e =
      (torusCellCrossing L ⟨e, he⟩ : TorusAmbientEdge L) := by
  simp [torusCellDualOfPrimalEdge, he]



theorem torusCellDualCutGraph_sup_edge (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) {p q : ZMod L × ZMod L}
    (hpq : (onsTorusGraph L).Adj p q) :
    torusCellDualCutGraph L (G ⊔ edge p q) =
      (torusCellDualCutGraph L G).deleteEdges
        {torusCellDualOfPrimalEdge L s(p, q)} := by
  let ep : TorusAmbientEdge L :=
    ⟨s(p, q), by simpa only [SimpleGraph.mem_edgeFinset] using hpq⟩
  let ed : TorusAmbientEdge L := torusCellCrossing L ep
  have hed : torusCellDualOfPrimalEdge L s(p, q) =
      (ed : Sym2 (ZMod L × ZMod L)) := by
    simpa [ed] using torusCellDualOfPrimalEdge_of_mem L ep.2
  ext f g
  by_cases hfg : (onsTorusGraph L).Adj f g
  · have hefg : s(f, g) ∈ (onsTorusGraph L).edgeFinset := by
      simpa only [SimpleGraph.mem_edgeFinset] using hfg
    have hcross : torusCellPrimalOfDualEdge L s(f, g) = s(p, q) ↔
        s(f, g) = (ed : Sym2 (ZMod L × ZMod L)) := by
      rw [torusCellPrimalOfDualEdge_of_mem L hefg]
      constructor
      · intro h
        have hs : (torusCellCrossing L).symm
            (⟨s(f, g), hefg⟩ : TorusAmbientEdge L) = ep :=
          Subtype.ext h
        have := congrArg (torusCellCrossing L) hs
        simpa [ed] using congrArg Subtype.val this
      · intro h
        have hs : (⟨s(f, g), hefg⟩ : TorusAmbientEdge L) = ed :=
          Subtype.ext h
        have := congrArg (torusCellCrossing L).symm hs
        simpa [ep, ed] using congrArg Subtype.val this
    simp only [torusCellDualCutGraph_adj, deleteEdges_adj, hfg, true_and,
      Set.mem_singleton_iff]
    rw [hed]
    rw [edgeSet_sup, edgeSet_edge_of_ne hpq.ne]
    simp only [Set.mem_union, Set.mem_singleton_iff, not_or]
    exact and_congr_right (fun _ => not_congr hcross)
  · simp [torusCellDualCutGraph_adj, deleteEdges_adj, hfg]


noncomputable def torusCellFaceCount (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) : ℕ :=
  Nat.card (torusCellDualCutGraph L G).ConnectedComponent


noncomputable def torusCellDefect (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) : ℤ :=
  (G.edgeSet.ncard : ℤ) - Nat.card (ZMod L × ZMod L) +
    Nat.card G.ConnectedComponent + 1 - torusCellFaceCount L G



theorem torusCell_euler (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) :
    (Nat.card (ZMod L × ZMod L) : ℤ) - G.edgeSet.ncard +
        torusCellFaceCount L G =
      Nat.card G.ConnectedComponent + 1 - torusCellDefect L G := by
  unfold torusCellDefect
  ring


theorem torusCell_numClusters_dualConfig (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    FK.numClusters (onsTorusGraph L) (torusCellDualConfig L ω) =
      torusCellFaceCount L (FK.openSub (onsTorusGraph L) ω) := by
  unfold FK.numClusters torusCellFaceCount
  rw [← Nat.card_eq_fintype_card]
  exact congrArg (fun G : SimpleGraph (ZMod L × ZMod L) =>
    Nat.card G.ConnectedComponent) (torusCell_openSub_dualConfig L ω)



theorem torusCellFaceCount_bot (L : ℕ) [Fact (2 < L)]
    (hconn : (onsTorusGraph L).Connected) :
    torusCellFaceCount L (⊥ : SimpleGraph (ZMod L × ZMod L)) = 1 := by
  unfold torusCellFaceCount
  rw [torusCellDualCutGraph_bot,
    StatMech.Lattice.card_components_eq_one_of_connected hconn]



theorem torusCellFaceCount_full (L : ℕ) [Fact (2 < L)] :
    torusCellFaceCount L (onsTorusGraph L) = L ^ 2 := by
  unfold torusCellFaceCount
  rw [torusCellDualCutGraph_full, StatMech.Lattice.card_components_bot]
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]
  ring


theorem torusCellDefect_bot (L : ℕ) [Fact (2 < L)]
    (hconn : (onsTorusGraph L).Connected) :
    torusCellDefect L (⊥ : SimpleGraph (ZMod L × ZMod L)) = 0 := by
  unfold torusCellDefect
  rw [torusCellFaceCount_bot L hconn, StatMech.Lattice.card_components_bot]
  simp


theorem torusCellDefect_full (L : ℕ) [Fact (2 < L)]
    (hconn : (onsTorusGraph L).Connected) :
    torusCellDefect L (onsTorusGraph L) = 2 := by
  have hedge : (onsTorusGraph L).edgeSet.ncard = 2 * L ^ 2 := by
    rw [Set.ncard_eq_toFinset_card']
    exact onsTorus_card_edges L
  unfold torusCellDefect
  rw [hedge, StatMech.Lattice.card_components_eq_one_of_connected hconn,
    torusCellFaceCount_full]
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]
  push_cast
  ring



def torusCellOldObstructionConfig3 :
    ConfigSpace (Sym2 (ZMod 3 × ZMod 3)) := fun e => decide (e ∈ ({
      s(((0, 0) : ZMod 3 × ZMod 3), ((1, 0) : ZMod 3 × ZMod 3)),
      s(((0, 1) : ZMod 3 × ZMod 3), ((1, 1) : ZMod 3 × ZMod 3)),
      s(((0, 2) : ZMod 3 × ZMod 3), ((1, 2) : ZMod 3 × ZMod 3)),
      s(((1, 0) : ZMod 3 × ZMod 3), ((2, 0) : ZMod 3 × ZMod 3)),
      s(((1, 0) : ZMod 3 × ZMod 3), ((1, 1) : ZMod 3 × ZMod 3)),
      s(((1, 1) : ZMod 3 × ZMod 3), ((2, 1) : ZMod 3 × ZMod 3)),
      s(((1, 1) : ZMod 3 × ZMod 3), ((1, 2) : ZMod 3 × ZMod 3)),
      s(((1, 2) : ZMod 3 × ZMod 3), ((2, 2) : ZMod 3 × ZMod 3))} :
        Finset (Sym2 (ZMod 3 × ZMod 3))))

end StatMech.BeffaraDC
