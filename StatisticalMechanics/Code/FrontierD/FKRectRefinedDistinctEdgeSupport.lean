/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedEdgeCenterClass
import Code.FrontierD.FKRectRefinedBoundaryLocalSupport










namespace StatMech.FrontierD

noncomputable section

private theorem fkRectDistinctSupport_intCast_four_mul_add_ne_four_mul
    {L : Nat} [NeZero L] (hL : (4 : Int) ∣ (L : Int))
    (x a k : Int) (hk : ¬ (4 : Int) ∣ k) :
    ((4 * x + k : Int) : ZMod L) ≠ ((4 * a : Int) : ZMod L) := by
  intro h
  have hd : (L : Int) ∣ (4 * a) - (4 * x + k) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ L).mp h
  obtain ⟨m, hm⟩ := hd
  obtain ⟨n, hn⟩ := hL
  apply hk
  refine ⟨a - x - n * m, ?_⟩
  rw [hn] at hm
  linarith

private theorem fkRectDistinctSupport_center_cast_eq
    {L : Nat} [NeZero L] (hL : (4 : Int) ∣ (L : Int))
    (x a r i j : Int) (hlo : -3 ≤ i - j) (hhi : i - j ≤ 3)
    (h : ((4 * x + r + i : Int) : ZMod L) =
      ((4 * a + r + j : Int) : ZMod L)) :
    ((4 * x + r : Int) : ZMod L) =
      ((4 * a + r : Int) : ZMod L) := by
  have hd : (L : Int) ∣
      (4 * a + r + j) - (4 * x + r + i) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ L).mp h
  obtain ⟨m, hm⟩ := hd
  obtain ⟨n, hn⟩ := hL
  have hfour : (4 : Int) ∣ j - i := by
    refine ⟨n * m - (a - x), ?_⟩
    rw [hn] at hm
    linarith
  obtain ⟨k, hk⟩ := hfour
  have hij : i = j := by omega
  subst j
  apply_fun fun z : ZMod L => z - (i : ZMod L) at h
  convert h using 1 <;> push_cast <;> ring

private theorem fkRectRefinedLocalDarts_false_usesPoint_offsets
    {L : Nat} (c : Int × Int) (side : FKMedialSide)
    (p : ZMod L × ZMod L)
    (h : FKRectDartListUsesPoint
      ((fkRectRefinedLocalDarts false c side).map
        (fkRectIntegralSquareDartMod L)) p) :
    ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ (j = -1 ∨ j = 1) ∧
      p = ((((c.1 + i : Int) : ZMod L)),
        (((c.2 + j : Int) : ZMod L))) := by
  cases side
  · simp [FKRectDartListUsesPoint, fkRectRefinedLocalDarts,
      fkRectRefinedDartPoint, fkRectRefinedSideOffset,
      fkRectIntegralSquareDartMod, StatMech.Onsager.ons_dirStep] at h ⊢
    rcases h with (h | h) | h | h <;> subst p
    · exact ⟨-1, by norm_num, by norm_num, Or.inl (by ring)⟩
    · exact ⟨0, by norm_num, by norm_num, Or.inl (by ring)⟩
    · exact ⟨0, by norm_num, by norm_num, Or.inl (by ring)⟩
    · exact ⟨1, by norm_num, by norm_num, Or.inl (by ring)⟩
  · simp [FKRectDartListUsesPoint, fkRectRefinedLocalDarts,
      fkRectRefinedDartPoint, fkRectRefinedSideOffset,
      fkRectIntegralSquareDartMod, StatMech.Onsager.ons_dirStep] at h ⊢
    rcases h with (h | h) | h | h <;> subst p
    · exact ⟨1, by norm_num, by norm_num, Or.inr (by ring)⟩
    · exact ⟨0, by norm_num, by norm_num, Or.inr (by ring)⟩
    · exact ⟨0, by norm_num, by norm_num, Or.inr (by ring)⟩
    · exact ⟨-1, by norm_num, by norm_num, Or.inr (by ring)⟩
  · simp [FKRectDartListUsesPoint, fkRectRefinedLocalDarts,
      fkRectRefinedDartPoint, fkRectRefinedSideOffset,
      fkRectIntegralSquareDartMod, StatMech.Onsager.ons_dirStep] at h ⊢
    rcases h with (h | h) | h | h <;> subst p
    · exact ⟨-1, by norm_num, by norm_num, Or.inr (by ring)⟩
    · exact ⟨0, by norm_num, by norm_num, Or.inr (by ring)⟩
    · exact ⟨0, by norm_num, by norm_num, Or.inr (by ring)⟩
    · exact ⟨1, by norm_num, by norm_num, Or.inr (by ring)⟩
  · simp [FKRectDartListUsesPoint, fkRectRefinedLocalDarts,
      fkRectRefinedDartPoint, fkRectRefinedSideOffset,
      fkRectIntegralSquareDartMod, StatMech.Onsager.ons_dirStep] at h ⊢
    rcases h with (h | h) | h | h <;> subst p
    · exact ⟨1, by norm_num, by norm_num, Or.inl (by ring)⟩
    · exact ⟨0, by norm_num, by norm_num, Or.inl (by ring)⟩
    · exact ⟨0, by norm_num, by norm_num, Or.inl (by ring)⟩
    · exact ⟨-1, by norm_num, by norm_num, Or.inl (by ring)⟩

private theorem fkRectRefinedLocalDarts_true_usesPoint_offsets
    {L : Nat} (c : Int × Int) (side : FKMedialSide)
    (p : ZMod L × ZMod L)
    (h : FKRectDartListUsesPoint
      ((fkRectRefinedLocalDarts true c side).map
        (fkRectIntegralSquareDartMod L)) p) :
    ∃ i j : Int, (i = -1 ∨ i = 1) ∧ -1 ≤ j ∧ j ≤ 1 ∧
      p = ((((c.1 + i : Int) : ZMod L)),
        (((c.2 + j : Int) : ZMod L))) := by
  cases side
  · simp [FKRectDartListUsesPoint, fkRectRefinedLocalDarts,
      fkRectRefinedDartPoint, fkRectRefinedSideOffset,
      fkRectIntegralSquareDartMod, StatMech.Onsager.ons_dirStep] at h ⊢
    rcases h with (h | h) | h | h <;> subst p
    · exact Or.inl ⟨-1, by norm_num, by norm_num, by ring⟩
    · exact Or.inl ⟨0, by norm_num, by norm_num, by ring⟩
    · exact Or.inl ⟨0, by norm_num, by norm_num, by ring⟩
    · exact Or.inl ⟨1, by norm_num, by norm_num, by ring⟩
  · simp [FKRectDartListUsesPoint, fkRectRefinedLocalDarts,
      fkRectRefinedDartPoint, fkRectRefinedSideOffset,
      fkRectIntegralSquareDartMod, StatMech.Onsager.ons_dirStep] at h ⊢
    rcases h with (h | h) | h | h <;> subst p
    · exact Or.inr ⟨1, by norm_num, by norm_num, by ring⟩
    · exact Or.inr ⟨0, by norm_num, by norm_num, by ring⟩
    · exact Or.inr ⟨0, by norm_num, by norm_num, by ring⟩
    · exact Or.inr ⟨-1, by norm_num, by norm_num, by ring⟩
  · simp [FKRectDartListUsesPoint, fkRectRefinedLocalDarts,
      fkRectRefinedDartPoint, fkRectRefinedSideOffset,
      fkRectIntegralSquareDartMod, StatMech.Onsager.ons_dirStep] at h ⊢
    rcases h with (h | h) | h | h <;> subst p
    · exact Or.inl ⟨1, by norm_num, by norm_num, by ring⟩
    · exact Or.inl ⟨0, by norm_num, by norm_num, by ring⟩
    · exact Or.inl ⟨0, by norm_num, by norm_num, by ring⟩
    · exact Or.inl ⟨-1, by norm_num, by norm_num, by ring⟩
  · simp [FKRectDartListUsesPoint, fkRectRefinedLocalDarts,
      fkRectRefinedDartPoint, fkRectRefinedSideOffset,
      fkRectIntegralSquareDartMod, StatMech.Onsager.ons_dirStep] at h ⊢
    rcases h with (h | h) | h | h <;> subst p
    · exact Or.inr ⟨-1, by norm_num, by norm_num, by ring⟩
    · exact Or.inr ⟨0, by norm_num, by norm_num, by ring⟩
    · exact Or.inr ⟨0, by norm_num, by norm_num, by ring⟩
    · exact Or.inr ⟨1, by norm_num, by norm_num, by ring⟩

private theorem fkRectRefinedCenterline_false_usesPoint_offsets
    {L : Nat} (z : Int × Int) (p : ZMod L × ZMod L)
    (h : FKRectDartListUsesPoint
      ((fkRectRefinedPrimalCenterlineDarts false z).map
        (fkRectIntegralSquareDartMod L)) p) :
    ∃ j : Int, -2 ≤ j ∧ j ≤ 2 ∧
      p = ((((z.1 : Int) : ZMod L)),
        (((z.2 + j : Int) : ZMod L))) := by
  simp [FKRectDartListUsesPoint, fkRectRefinedPrimalCenterlineDarts,
    fkRectIntegralSquareDartMod, StatMech.Onsager.ons_dirStep] at h ⊢
  rcases h with (h | h) | (h | h) | (h | h) | h | h <;> subst p
  all_goals
    solve
    | refine ⟨-2, by norm_num, by norm_num, ?_⟩ <;> push_cast <;> ring
    | refine ⟨-1, by norm_num, by norm_num, ?_⟩ <;> push_cast <;> ring
    | refine ⟨0, by norm_num, by norm_num, ?_⟩ <;> push_cast <;> ring
    | refine ⟨1, by norm_num, by norm_num, ?_⟩ <;> push_cast <;> ring
    | refine ⟨2, by norm_num, by norm_num, ?_⟩ <;> push_cast <;> ring

private theorem fkRectRefinedCenterline_true_usesPoint_offsets
    {L : Nat} (z : Int × Int) (p : ZMod L × ZMod L)
    (h : FKRectDartListUsesPoint
      ((fkRectRefinedPrimalCenterlineDarts true z).map
        (fkRectIntegralSquareDartMod L)) p) :
    ∃ i : Int, -2 ≤ i ∧ i ≤ 2 ∧
      p = ((((z.1 + i : Int) : ZMod L)),
        (((z.2 : Int) : ZMod L))) := by
  simp [FKRectDartListUsesPoint, fkRectRefinedPrimalCenterlineDarts,
    fkRectIntegralSquareDartMod, StatMech.Onsager.ons_dirStep] at h ⊢
  rcases h with (h | h) | (h | h) | (h | h) | h | h <;> subst p
  all_goals
    solve
    | refine ⟨-2, by norm_num, by norm_num, ?_⟩ <;> push_cast <;> ring
    | refine ⟨-1, by norm_num, by norm_num, ?_⟩ <;> push_cast <;> ring
    | refine ⟨0, by norm_num, by norm_num, ?_⟩ <;> push_cast <;> ring
    | refine ⟨1, by norm_num, by norm_num, ?_⟩ <;> push_cast <;> ring
    | refine ⟨2, by norm_num, by norm_num, ?_⟩ <;> push_cast <;> ring



theorem fkRectRefinedCenter_mod_eq_of_closed_local_centerline_commonPoint
    (R : FKRectTorus) (closed targetHorizontal : Bool)
    (c z : Int × Int) (side : FKMedialSide)
    (hc : FKRectRefinedEdgeCenterNormal closed c)
    (hz : FKRectRefinedEdgeCenterNormal targetHorizontal z)
    (p : ZMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)) ×
      ZMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))
    (hl : FKRectDartListUsesPoint
      ((fkRectRefinedLocalDarts closed c side).map
        (fkRectIntegralSquareDartMod
          (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p)
    (ht : FKRectDartListUsesPoint
      ((fkRectRefinedPrimalCenterlineDarts targetHorizontal z).map
        (fkRectIntegralSquareDartMod
          (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p) :
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
      (((z.1 : Int) : ZMod L), ((z.2 : Int) : ZMod L)) := by
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  have hL : (4 : Int) ∣ (L : Int) := by
    refine ⟨(fkRectSquareCoverSide R : Int), ?_⟩
    simp [L]
  have hne (u v k : Int) (hk : ¬ (4 : Int) ∣ k) :
      ((4 * u + k : Int) : ZMod L) ≠
        ((4 * v : Int) : ZMod L) :=
    fkRectDistinctSupport_intCast_four_mul_add_ne_four_mul hL u v k hk
  dsimp only
  change (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
    (((z.1 : Int) : ZMod L), ((z.2 : Int) : ZMod L))
  change FKRectDartListUsesPoint
      ((fkRectRefinedLocalDarts closed c side).map
        (fkRectIntegralSquareDartMod L)) p at hl
  change FKRectDartListUsesPoint
      ((fkRectRefinedPrimalCenterlineDarts targetHorizontal z).map
        (fkRectIntegralSquareDartMod L)) p at ht
  cases closed <;> cases targetHorizontal
  · simp only [FKRectRefinedEdgeCenterNormal, if_false] at hc hz
    obtain ⟨x, y, rfl⟩ := hc
    obtain ⟨a, b, rfl⟩ := hz
    obtain ⟨i, j, hi0, hi1, hj, hpLocal⟩ :=
      fkRectRefinedLocalDarts_false_usesPoint_offsets
        (L := L) (4 * x, 4 * y + 2) side p hl
    obtain ⟨k, hk0, hk1, hpTarget⟩ :=
      fkRectRefinedCenterline_false_usesPoint_offsets
        (L := L) (4 * a, 4 * b + 2) p ht
    have hpEq := hpLocal.symm.trans hpTarget
    have hx := congrArg Prod.fst hpEq
    have hy := congrArg Prod.snd hpEq
    apply Prod.ext
    · change ((4 * x : Int) : ZMod L) = ((4 * a : Int) : ZMod L)
      have hcast := fkRectDistinctSupport_center_cast_eq hL x a 0 i 0
        (by omega) (by omega) (by
          convert hx using 1 <;> push_cast <;> ring)
      simpa only [add_zero] using hcast
    · change (((4 * y + 2 : Int) : ZMod L)) =
        (((4 * b + 2 : Int) : ZMod L))
      apply fkRectDistinctSupport_center_cast_eq hL y b 2 j k
        (by omega) (by omega)
      convert hy using 1 <;> push_cast <;> ring
  · simp only [FKRectRefinedEdgeCenterNormal, if_false, if_true] at hc hz
    obtain ⟨x, y, rfl⟩ := hc
    obtain ⟨a, b, rfl⟩ := hz
    obtain ⟨i, j, hi0, hi1, hj, hpLocal⟩ :=
      fkRectRefinedLocalDarts_false_usesPoint_offsets
        (L := L) (4 * x, 4 * y + 2) side p hl
    obtain ⟨k, hk0, hk1, hpTarget⟩ :=
      fkRectRefinedCenterline_true_usesPoint_offsets
        (L := L) (4 * a - 2, 4 * b) p ht
    have hpEq := hpLocal.symm.trans hpTarget
    have hy := congrArg Prod.snd hpEq
    rcases hj with rfl | rfl
    · exfalso
      apply hne y b 1 (by norm_num)
      convert hy using 1 <;> push_cast <;> ring
    · exfalso
      apply hne y b 3 (by norm_num)
      convert hy using 1 <;> push_cast <;> ring
  · simp only [FKRectRefinedEdgeCenterNormal, if_false, if_true] at hc hz
    obtain ⟨x, y, rfl⟩ := hc
    obtain ⟨a, b, rfl⟩ := hz
    obtain ⟨i, j, hi, hj0, hj1, hpLocal⟩ :=
      fkRectRefinedLocalDarts_true_usesPoint_offsets
        (L := L) (4 * x - 2, 4 * y) side p hl
    obtain ⟨k, hk0, hk1, hpTarget⟩ :=
      fkRectRefinedCenterline_false_usesPoint_offsets
        (L := L) (4 * a, 4 * b + 2) p ht
    have hpEq := hpLocal.symm.trans hpTarget
    have hx := congrArg Prod.fst hpEq
    rcases hi with rfl | rfl
    · exfalso
      apply hne x a (-3) (by norm_num)
      convert hx using 1 <;> push_cast <;> ring
    · exfalso
      apply hne x a (-1) (by norm_num)
      convert hx using 1 <;> push_cast <;> ring
  · simp only [FKRectRefinedEdgeCenterNormal, if_true] at hc hz
    obtain ⟨x, y, rfl⟩ := hc
    obtain ⟨a, b, rfl⟩ := hz
    obtain ⟨i, j, hi, hj0, hj1, hpLocal⟩ :=
      fkRectRefinedLocalDarts_true_usesPoint_offsets
        (L := L) (4 * x - 2, 4 * y) side p hl
    obtain ⟨k, hk0, hk1, hpTarget⟩ :=
      fkRectRefinedCenterline_true_usesPoint_offsets
        (L := L) (4 * a - 2, 4 * b) p ht
    have hpEq := hpLocal.symm.trans hpTarget
    have hx := congrArg Prod.fst hpEq
    have hy := congrArg Prod.snd hpEq
    apply Prod.ext
    · change (((4 * x - 2 : Int) : ZMod L)) =
        (((4 * a - 2 : Int) : ZMod L))
      apply fkRectDistinctSupport_center_cast_eq hL x a (-2) i k
        (by omega) (by omega)
      convert hx using 1 <;> push_cast <;> ring
    · change ((4 * y : Int) : ZMod L) = ((4 * b : Int) : ZMod L)
      have hcast := fkRectDistinctSupport_center_cast_eq hL y b 0 j 0
        (by omega) (by omega) (by
          convert hy using 1 <;> push_cast <;> ring)
      simpa only [add_zero] using hcast



theorem fkRectRefinedBoundaryLocal_endpointDisjoint_of_closed_ne
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (c : Int × Int)
    (e f : R.EdgeIndex) (u : Int × Int)
    (hcurrent : fkRectTorusMedialEdgeEquiv R d.1 = f)
    (hclosed : pairing d.1 = fkRectClosedPairingAtEdge f)
    (hcenter : c =
      ((fkRectRefinedPrimalEdgeCenter R f).1 +
          4 * (fkRectSquareDeckTranslation R u).1,
        (fkRectRefinedPrimalEdgeCenter R f).2 +
          4 * (fkRectSquareDeckTranslation R u).2))
    (hne : f ≠ e) :
    ∀ p,
      FKRectDartListUsesPoint
          ((fkRectRefinedLocalDarts (pairing d.1) c d.2).map
            (fkRectIntegralSquareDartMod
              (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p →
        ¬ FKRectDartListUsesPoint
          ((fkRectRefinedPrimalEdgeDarts R e).map
            (fkRectIntegralSquareDartMod
              (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p := by
  intro p hl ht
  rw [hclosed] at hl
  rw [fkRectRefinedPrimalEdgeDarts_eq_centerline] at ht
  have hnormal : FKRectRefinedEdgeCenterNormal
      (fkRectClosedPairingAtEdge f) c := by
    rw [hcenter]
    exact (fkRectRefinedPrimalEdgeCenter_normal R f).add_four
      (fkRectSquareDeckTranslation R u).1
      (fkRectSquareDeckTranslation R u).2
  have hmod :=
    fkRectRefinedCenter_mod_eq_of_closed_local_centerline_commonPoint
      R (fkRectClosedPairingAtEdge f) (fkRectClosedPairingAtEdge e)
      c (fkRectRefinedPrimalEdgeCenter R e) d.2 hnormal
      (fkRectRefinedPrimalEdgeCenter_normal R e) p hl ht
  apply hne
  apply fkRectIndexedEdge_eq_of_refinedCenter_deck_mod_eq R f e u
  dsimp only at hmod ⊢
  rw [hcenter] at hmod
  exact hmod



theorem fkRectRefinedBoundaryLocalInteraction_eq_zero_of_closed_ne
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (c : Int × Int)
    (e f : R.EdgeIndex) (u : Int × Int)
    (hcurrent : fkRectTorusMedialEdgeEquiv R d.1 = f)
    (hclosed : pairing d.1 = fkRectClosedPairingAtEdge f)
    (hcenter : c =
      ((fkRectRefinedPrimalEdgeCenter R f).1 +
          4 * (fkRectSquareDeckTranslation R u).1,
        (fkRectRefinedPrimalEdgeCenter R f).2 +
          4 * (fkRectSquareDeckTranslation R u).2))
    (hne : f ≠ e) :
    fkRectRefinedBoundaryLocalInteraction R pairing d c e = 0 := by
  apply fkRectRefinedBoundaryLocalInteraction_eq_zero_of_endpointDisjoint
  exact fkRectRefinedBoundaryLocal_endpointDisjoint_of_closed_ne
    R pairing d c e f u hcurrent hclosed hcenter hne

end

end StatMech.FrontierD
