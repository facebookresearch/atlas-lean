/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.BeffaraDC.TorusCellDual

open SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Onsager



def torusCellDiagonalShift (L : ℕ) :
    (ZMod L × ZMod L) ≃ (ZMod L × ZMod L) where
  toFun v := (v.1 + 1, v.2 + 1)
  invFun v := (v.1 - 1, v.2 - 1)
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp

@[simp] theorem torusCellDiagonalShift_apply (L : ℕ)
    (v : ZMod L × ZMod L) :
    torusCellDiagonalShift L v = (v.1 + 1, v.2 + 1) := rfl


theorem torusCellDiagonalShift_adj_iff (L : ℕ) [Fact (2 < L)]
    (u v : ZMod L × ZMod L) :
    (onsTorusGraph L).Adj (torusCellDiagonalShift L u)
        (torusCellDiagonalShift L v) ↔
      (onsTorusGraph L).Adj u v := by
  simp only [onsTorusGraph, onsTorusAdj, torusCellDiagonalShift_apply]
  constructor
  · rintro (⟨h, h' | h'⟩ | ⟨h, h' | h'⟩)
    · exact Or.inl ⟨by linear_combination h,
        Or.inl (by linear_combination h')⟩
    · exact Or.inl ⟨by linear_combination h,
        Or.inr (by linear_combination h')⟩
    · exact Or.inr ⟨by linear_combination h,
        Or.inl (by linear_combination h')⟩
    · exact Or.inr ⟨by linear_combination h,
        Or.inr (by linear_combination h')⟩
  · rintro (⟨h, h' | h'⟩ | ⟨h, h' | h'⟩)
    · exact Or.inl ⟨by linear_combination h,
        Or.inl (by linear_combination h')⟩
    · exact Or.inl ⟨by linear_combination h,
        Or.inr (by linear_combination h')⟩
    · exact Or.inr ⟨by linear_combination h,
        Or.inl (by linear_combination h')⟩
    · exact Or.inr ⟨by linear_combination h,
        Or.inr (by linear_combination h')⟩



theorem torusCellCrossing_symm_sq (L : ℕ) [Fact (2 < L)]
    (e : TorusAmbientEdge L) :
    (((torusCellCrossing L).symm
        ((torusCellCrossing L).symm e) : TorusAmbientEdge L) :
      Sym2 (ZMod L × ZMod L)) =
      Sym2.map (torusCellDiagonalShift L)
        (e : Sym2 (ZMod L × ZMod L)) := by
  obtain ⟨c, rfl⟩ := (torusEdgeCodeEquiv L).surjective e
  rcases c with ⟨⟨x, y⟩, o⟩
  cases o
  · simp [torusEdgeOfCode, torusCellDiagonalShift, Sym2.map_mk]
  · simp [torusEdgeOfCode, torusCellDiagonalShift, Sym2.map_mk]



theorem torusCellPrimalOfDualEdge_sq (L : ℕ) [Fact (2 < L)]
    {e : Sym2 (ZMod L × ZMod L)}
    (he : e ∈ (onsTorusGraph L).edgeFinset) :
    torusCellPrimalOfDualEdge L (torusCellPrimalOfDualEdge L e) =
      Sym2.map (torusCellDiagonalShift L) e := by
  have hp := torusCellPrimalOfDualEdge_mem L he
  have hsub : (⟨torusCellPrimalOfDualEdge L e, hp⟩ :
      TorusAmbientEdge L) = (torusCellCrossing L).symm ⟨e, he⟩ := by
    apply Subtype.ext
    exact torusCellPrimalOfDualEdge_of_mem L he
  rw [torusCellPrimalOfDualEdge_of_mem L hp, hsub]
  exact torusCellCrossing_symm_sq L ⟨e, he⟩



theorem torusCellDualConfig_dualConfig_of_mem (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (ZMod L × ZMod L)))
    {e : Sym2 (ZMod L × ZMod L)}
    (he : e ∈ (onsTorusGraph L).edgeFinset) :
    torusCellDualConfig L (torusCellDualConfig L omega) e =
      FK.reCfg (torusCellDiagonalShift L) omega e := by
  have hp := torusCellPrimalOfDualEdge_mem L he
  simp only [torusCellDualConfig, dif_pos he, dif_pos hp, FK.reCfg]
  rw [torusCellPrimalOfDualEdge_sq L he]
  cases omega (Sym2.map (torusCellDiagonalShift L) e) <;> rfl



theorem torusCell_openSub_dualConfig_dualConfig
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    FK.openSub (onsTorusGraph L)
        (torusCellDualConfig L (torusCellDualConfig L omega)) =
      FK.openSub (onsTorusGraph L)
        (FK.reCfg (torusCellDiagonalShift L) omega) := by
  ext u v
  by_cases huv : (onsTorusGraph L).Adj u v
  · have he : s(u, v) ∈ (onsTorusGraph L).edgeFinset := by
      simpa only [SimpleGraph.mem_edgeFinset] using huv
    simp only [FK.openSub_adj, huv, true_and]
    rw [torusCellDualConfig_dualConfig_of_mem L omega he]
  · simp [FK.openSub_adj, huv]


theorem torusCell_numClusters_dualConfig_dualConfig
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    FK.numClusters (onsTorusGraph L)
        (torusCellDualConfig L (torusCellDualConfig L omega)) =
      FK.numClusters (onsTorusGraph L) omega := by
  have hopen := torusCell_openSub_dualConfig_dualConfig L omega
  have hcard := congrArg (fun G : SimpleGraph (ZMod L × ZMod L) =>
    Nat.card G.ConnectedComponent) hopen
  have hshift := FK.fkTI_numClusters_reCfg
    (onsTorusGraph L) (torusCellDiagonalShift L)
      (torusCellDiagonalShift_adj_iff L) omega
  unfold FK.numClusters at hshift ⊢
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hshift ⊢
  exact hcard.trans hshift



theorem torusCellDefect_add_dualConfig (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    torusCellDefect L (FK.openSub (onsTorusGraph L) omega) +
      torusCellDefect L
        (FK.openSub (onsTorusGraph L) (torusCellDualConfig L omega)) = 2 := by
  have hopen := torusCell_dual_openCount L omega
  have hfaces := torusCell_numClusters_dualConfig L omega
  have hfacesDual := torusCell_numClusters_dualConfig L
    (torusCellDualConfig L omega)
  have hclusters2 := torusCell_numClusters_dualConfig_dualConfig L omega
  have hedge : (onsTorusGraph L).edgeFinset.card = 2 * L ^ 2 :=
    onsTorus_card_edges L
  have hvert : Nat.card (ZMod L × ZMod L) = L ^ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]
    ring
  have hclusters :
      Nat.card (FK.openSub (onsTorusGraph L) omega).ConnectedComponent =
        FK.numClusters (onsTorusGraph L) omega := by
    unfold FK.numClusters
    rw [Nat.card_eq_fintype_card]
  have hclustersDual :
      Nat.card (FK.openSub (onsTorusGraph L)
        (torusCellDualConfig L omega)).ConnectedComponent =
        FK.numClusters (onsTorusGraph L) (torusCellDualConfig L omega) := by
    unfold FK.numClusters
    rw [Nat.card_eq_fintype_card]
  unfold torusCellDefect
  rw [torus_openSub_edge_ncard, torus_openSub_edge_ncard]
  rw [hclusters, hclustersDual]
  rw [← hfaces, ← hfacesDual, hclusters2]
  have hopen_le : FK.openCount (onsTorusGraph L) omega ≤
      (onsTorusGraph L).edgeFinset.card := by
    unfold FK.openCount
    exact Finset.card_filter_le _ _
  have hopenAdd :
      FK.openCount (onsTorusGraph L) (torusCellDualConfig L omega) +
        FK.openCount (onsTorusGraph L) omega =
          (onsTorusGraph L).edgeFinset.card := by
    omega
  have htorus : (onsTorusGraph L).edgeFinset.card =
      2 * Nat.card (ZMod L × ZMod L) := by
    omega
  have hopenAddZ :
      (FK.openCount (onsTorusGraph L) (torusCellDualConfig L omega) : ℤ) +
        FK.openCount (onsTorusGraph L) omega =
          (onsTorusGraph L).edgeFinset.card := by
    exact_mod_cast hopenAdd
  have htorusZ : ((onsTorusGraph L).edgeFinset.card : ℤ) =
      2 * Nat.card (ZMod L × ZMod L) := by
    exact_mod_cast htorus
  linarith



theorem torusCellDefect_add_dualCutGraph (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L) :
    torusCellDefect L K +
      torusCellDefect L (torusCellDualCutGraph L K) = 2 := by
  let omega := torusConfigOfGraph L K
  have hopen : FK.openSub (onsTorusGraph L) omega = K :=
    torus_openSub_configOfGraph L K hK
  have hdual := torusCell_openSub_dualConfig L omega
  rw [hopen] at hdual
  simpa only [hopen, hdual] using torusCellDefect_add_dualConfig L omega

end StatMech.BeffaraDC
