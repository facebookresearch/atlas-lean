/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedDualEdgeInteraction
import Code.FrontierD.FKRectRefinedDualPrimalInteractionAlgebra
import Code.FrontierD.FKRectRefinedEdgeCenterClass
import Code.FrontierD.FKRectRefinedSupportInteraction
import Code.FrontierD.FKRectMedialDualShift










namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

private theorem fkRectDualPrimal_center_cast_eq
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

private theorem fkRectDualPrimal_centerline_false_usesPoint
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

private theorem fkRectDualPrimal_centerline_true_usesPoint
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




theorem fkRectRefined_perpendicular_centerlines_center_mod_eq_of_commonPoint
    (R : FKRectTorus) (pairing : Bool) (c z : Int × Int)
    (hc : FKRectRefinedEdgeCenterNormal pairing c)
    (hz : FKRectRefinedEdgeCenterNormal pairing z)
    (p : ZMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)) ×
      ZMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))
    (hl : FKRectDartListUsesPoint
      ((fkRectRefinedPrimalCenterlineDarts (!pairing) c).map
        (fkRectIntegralSquareDartMod
          (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p)
    (hr : FKRectDartListUsesPoint
      ((fkRectRefinedPrimalCenterlineDarts pairing z).map
        (fkRectIntegralSquareDartMod
          (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p) :
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
      (((z.1 : Int) : ZMod L), ((z.2 : Int) : ZMod L)) := by
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  have hL : (4 : Int) ∣ (L : Int) := by
    refine ⟨(fkRectSquareCoverSide R : Int), ?_⟩
    simp [L]
  dsimp only
  change (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
    (((z.1 : Int) : ZMod L), ((z.2 : Int) : ZMod L))
  change FKRectDartListUsesPoint
    ((fkRectRefinedPrimalCenterlineDarts (!pairing) c).map
      (fkRectIntegralSquareDartMod L)) p at hl
  change FKRectDartListUsesPoint
    ((fkRectRefinedPrimalCenterlineDarts pairing z).map
      (fkRectIntegralSquareDartMod L)) p at hr
  cases pairing
  · simp only [FKRectRefinedEdgeCenterNormal, if_false] at hc hz
    obtain ⟨x, y, rfl⟩ := hc
    obtain ⟨a, b, rfl⟩ := hz
    obtain ⟨i, hi0, hi1, hpLeft⟩ :=
      fkRectDualPrimal_centerline_true_usesPoint
        (L := L) (4 * x, 4 * y + 2) p hl
    obtain ⟨j, hj0, hj1, hpRight⟩ :=
      fkRectDualPrimal_centerline_false_usesPoint
        (L := L) (4 * a, 4 * b + 2) p hr
    have hpEq := hpLeft.symm.trans hpRight
    have hx := congrArg Prod.fst hpEq
    have hy := congrArg Prod.snd hpEq
    apply Prod.ext
    · change ((4 * x : Int) : ZMod L) = ((4 * a : Int) : ZMod L)
      have hcast := fkRectDualPrimal_center_cast_eq hL x a 0 i 0
        (by omega) (by omega) (by
          convert hx using 1 <;> push_cast <;> ring)
      simpa only [add_zero] using hcast
    · change ((4 * y + 2 : Int) : ZMod L) =
        ((4 * b + 2 : Int) : ZMod L)
      apply fkRectDualPrimal_center_cast_eq hL y b 2 0 j
        (by omega) (by omega)
      convert hy using 1 <;> push_cast <;> ring
  · simp only [FKRectRefinedEdgeCenterNormal, if_true] at hc hz
    obtain ⟨x, y, rfl⟩ := hc
    obtain ⟨a, b, rfl⟩ := hz
    obtain ⟨j, hj0, hj1, hpLeft⟩ :=
      fkRectDualPrimal_centerline_false_usesPoint
        (L := L) (4 * x - 2, 4 * y) p hl
    obtain ⟨i, hi0, hi1, hpRight⟩ :=
      fkRectDualPrimal_centerline_true_usesPoint
        (L := L) (4 * a - 2, 4 * b) p hr
    have hpEq := hpLeft.symm.trans hpRight
    have hx := congrArg Prod.fst hpEq
    have hy := congrArg Prod.snd hpEq
    apply Prod.ext
    · change ((4 * x - 2 : Int) : ZMod L) =
        ((4 * a - 2 : Int) : ZMod L)
      apply fkRectDualPrimal_center_cast_eq hL x a (-2) 0 i
        (by omega) (by omega)
      convert hx using 1 <;> push_cast <;> ring
    · change ((4 * y : Int) : ZMod L) = ((4 * b : Int) : ZMod L)
      have hcast := fkRectDualPrimal_center_cast_eq hL y b 0 j 0
        (by omega) (by omega) (by
          convert hy using 1 <;> push_cast <;> ring)
      simpa only [add_zero] using hcast

private theorem fkRectRefinedPrimalCenterline_map_eq_of_center_mod_eq
    {L : Nat} (pairing : Bool) (c z : Int × Int)
    (h : (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
      (((z.1 : Int) : ZMod L), ((z.2 : Int) : ZMod L))) :
    (fkRectRefinedPrimalCenterlineDarts pairing c).map
        (fkRectIntegralSquareDartMod L) =
      (fkRectRefinedPrimalCenterlineDarts pairing z).map
        (fkRectIntegralSquareDartMod L) := by
  have hx : ((c.1 : Int) : ZMod L) = ((z.1 : Int) : ZMod L) :=
    congrArg Prod.fst h
  have hy : ((c.2 : Int) : ZMod L) = ((z.2 : Int) : ZMod L) :=
    congrArg Prod.snd h
  have hxadd (k : Int) : (((c.1 + k : Int) : ZMod L)) =
      (((z.1 + k : Int) : ZMod L)) := by
    push_cast
    exact congrArg (fun a : ZMod L => a + (k : ZMod L)) hx
  have hyadd (k : Int) : (((c.2 + k : Int) : ZMod L)) =
      (((z.2 + k : Int) : ZMod L)) := by
    push_cast
    exact congrArg (fun a : ZMod L => a + (k : ZMod L)) hy
  cases pairing <;>
    simp [fkRectRefinedPrimalCenterlineDarts,
      fkRectIntegralSquareDartMod, Prod.ext_iff, hx, hy, hxadd, hyadd]


theorem fkRectRefined_perpendicular_legal_centerlines_interaction
    (R : FKRectTorus) (pairing : Bool) (c z : Int × Int)
    (hc : FKRectRefinedEdgeCenterNormal pairing c)
    (hz : FKRectRefinedEdgeCenterNormal pairing z) :
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    fkRectRefinedRawInteraction
        ((fkRectRefinedPrimalCenterlineDarts (!pairing) c).map
          (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalCenterlineDarts pairing z).map
          (fkRectIntegralSquareDartMod L)) =
      if (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
          (((z.1 : Int) : ZMod L), ((z.2 : Int) : ZMod L))
      then if pairing then 1 else -1 else 0 := by
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  dsimp only
  by_cases hcenter :
      (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
        (((z.1 : Int) : ZMod L), ((z.2 : Int) : ZMod L))
  · rw [if_pos hcenter]
    rw [fkRectRefinedPrimalCenterline_map_eq_of_center_mod_eq
      (!pairing) c z hcenter]
    exact fkRectRefined_perpendicular_centerlines_interaction pairing z
  · rw [if_neg hcenter]
    apply fkRectRefinedRawInteraction_eq_zero_of_endpointDisjoint
    intro p hl hr
    apply hcenter
    exact fkRectRefined_perpendicular_centerlines_center_mod_eq_of_commonPoint
      R pairing c z hc hz p hl hr



theorem fkRectRefined_parallel_centerlines_interaction_eq_zero
    {L : Nat} [Fact (8 < L)] (pairing : Bool) (c z : Int × Int) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedPrimalCenterlineDarts pairing c).map
          (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalCenterlineDarts pairing z).map
          (fkRectIntegralSquareDartMod L)) = 0 := by
  cases pairing <;>
    simp [fkRectRefinedRawInteraction,
      fkRectRefinedPrimalCenterlineDarts, fkRectIntegralSquareDartMod,
      IntegralSquareTorusCycle.dartHorizontal,
      IntegralSquareTorusCycle.dartVertical]


theorem fkRectRefinedPrimalCenterlineDarts_translate
    (pairing : Bool) (c t : Int × Int) :
    (fkRectRefinedPrimalCenterlineDarts pairing c).map
        (fkRectIntegralSquareDartTranslate t) =
      fkRectRefinedPrimalCenterlineDarts pairing
        (c.1 + t.1, c.2 + t.2) := by
  cases pairing <;>
    simp [fkRectRefinedPrimalCenterlineDarts,
      fkRectIntegralSquareDartTranslate, Prod.ext_iff] <;> ring <;> simp



theorem fkRectRefinedDualEdgeCenter_normal
    (R : FKRectTorus) (d : R.EdgeIndex) :
    FKRectRefinedEdgeCenterNormal (!(fkRectClosedPairingAtEdge d))
      (fkRectRefinedDualEdgeCenter R d) := by
  let e := fkRectDualEdgeToEdge R d
  have hde : fkRectEdgeToDualEdge R e = d := by
    simp [e]
  obtain ⟨u, hu⟩ :=
    exists_fkRectRefinedDualEdgeCenter_edgeToDualEdge_eq_add_deck R e
  rw [hde] at hu
  rw [hu]
  have hnormal := fkRectRefinedPrimalEdgeCenter_normal R e
  have hpair := fkRectClosedPairingAtEdge_edgeToDualEdge R e
  rw [hde] at hpair
  cases hdv : fkRectClosedPairingAtEdge d <;>
    cases hev : fkRectClosedPairingAtEdge e <;> simp_all
  all_goals
    exact hnormal.add_four
      (fkRectSquareDeckTranslation R u).1
      (fkRectSquareDeckTranslation R u).2



theorem fkRectRefinedDualEdgeCenter_deck_normal
    (R : FKRectTorus) (d : R.EdgeIndex) (u : Int × Int) :
    FKRectRefinedEdgeCenterNormal (!(fkRectClosedPairingAtEdge d))
      ((fkRectRefinedDualEdgeCenter R d).1 +
          (fkRectRefinedDeckTranslation R u).1,
        (fkRectRefinedDualEdgeCenter R d).2 +
          (fkRectRefinedDeckTranslation R u).2) := by
  exact (fkRectRefinedDualEdgeCenter_normal R d).add_four
    (fkRectSquareDeckTranslation R u).1
    (fkRectSquareDeckTranslation R u).2



theorem fkRectIndexedEdge_eq_of_refinedCenter_twoDeck_mod_eq
    (R : FKRectTorus) (e f : R.EdgeIndex) (u v : Int × Int)
    (hmod :
      let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
      let c := fkRectRefinedPrimalEdgeCenter R e
      let z := fkRectRefinedPrimalEdgeCenter R f
      (((c.1 + (fkRectRefinedDeckTranslation R u).1 : Int) : ZMod L),
          ((c.2 + (fkRectRefinedDeckTranslation R u).2 : Int) : ZMod L)) =
        (((z.1 + (fkRectRefinedDeckTranslation R v).1 : Int) : ZMod L),
          ((z.2 + (fkRectRefinedDeckTranslation R v).2 : Int) : ZMod L))) :
    e = f := by
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  apply fkRectIndexedEdge_eq_of_refinedCenter_deck_mod_eq R e f
    (u.1 - v.1, u.2 - v.2)
  dsimp only at hmod ⊢
  have hx := congrArg Prod.fst hmod
  have hy := congrArg Prod.snd hmod
  apply Prod.ext
  · change
      (((fkRectRefinedPrimalEdgeCenter R e).1 +
        4 * (fkRectSquareDeckTranslation R
          (u.1 - v.1, u.2 - v.2)).1 : Int) : ZMod L) =
        ((fkRectRefinedPrimalEdgeCenter R f).1 : ZMod L)
    change
      (((fkRectRefinedPrimalEdgeCenter R e).1 +
        (fkRectRefinedDeckTranslation R u).1 : Int) : ZMod L) =
      (((fkRectRefinedPrimalEdgeCenter R f).1 +
        (fkRectRefinedDeckTranslation R v).1 : Int) : ZMod L) at hx
    push_cast at hx ⊢
    simp [fkRectRefinedDeckTranslation,
      fkRectSquareDeckTranslation] at hx ⊢
    linear_combination hx
  · change
      (((fkRectRefinedPrimalEdgeCenter R e).2 +
        4 * (fkRectSquareDeckTranslation R
          (u.1 - v.1, u.2 - v.2)).2 : Int) : ZMod L) =
        ((fkRectRefinedPrimalEdgeCenter R f).2 : ZMod L)
    change
      (((fkRectRefinedPrimalEdgeCenter R e).2 +
        (fkRectRefinedDeckTranslation R u).2 : Int) : ZMod L) =
      (((fkRectRefinedPrimalEdgeCenter R f).2 +
        (fkRectRefinedDeckTranslation R v).2 : Int) : ZMod L) at hy
    push_cast at hy ⊢
    simp [fkRectRefinedDeckTranslation,
      fkRectSquareDeckTranslation] at hy ⊢
    linear_combination hy



theorem fkRectDualEdge_eq_edgeToDualEdge_of_refinedCenter_deck_mod_eq
    (R : FKRectTorus) (d e : R.EdgeIndex) (u v : Int × Int)
    (hmod :
      let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
      ((((fkRectRefinedDualEdgeCenter R d).1 +
            (fkRectRefinedDeckTranslation R u).1 : Int) : ZMod L),
          (((fkRectRefinedDualEdgeCenter R d).2 +
            (fkRectRefinedDeckTranslation R u).2 : Int) : ZMod L)) =
        ((((fkRectRefinedPrimalEdgeCenter R e).1 +
            (fkRectRefinedDeckTranslation R v).1 : Int) : ZMod L),
          (((fkRectRefinedPrimalEdgeCenter R e).2 +
            (fkRectRefinedDeckTranslation R v).2 : Int) : ZMod L))) :
    d = fkRectEdgeToDualEdge R e := by
  let f := fkRectDualEdgeToEdge R d
  have hdf : fkRectEdgeToDualEdge R f = d := by simp [f]
  obtain ⟨t, ht⟩ :=
    exists_fkRectRefinedDualEdgeCenter_edgeToDualEdge_eq_add_deck R f
  rw [hdf] at ht
  have hfe : f = e := by
    apply fkRectIndexedEdge_eq_of_refinedCenter_twoDeck_mod_eq R f e
      (t.1 + u.1, t.2 + u.2) v
    dsimp only at hmod ⊢
    rw [ht] at hmod
    convert hmod using 1 <;>
      simp [fkRectRefinedDeckTranslation,
        fkRectSquareDeckTranslation] <;> ring <;> simp
  rw [← hfe]
  exact hdf.symm



theorem fkRectRefinedDualOpen_primalOpen_centers_mod_ne
    (R : FKRectTorus) (omega : R.Configuration)
    (d e : R.EdgeIndex)
    (hd : fkRectDualConfigurationEquiv R omega d = true)
    (he : omega e = true) (u v : Int × Int) :
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    let c : ZMod L × ZMod L :=
      ((fkRectRefinedDualEdgeCenter R d).1 +
          (fkRectRefinedDeckTranslation R u).1,
        (fkRectRefinedDualEdgeCenter R d).2 +
          (fkRectRefinedDeckTranslation R u).2)
    let z : ZMod L × ZMod L :=
      ((fkRectRefinedPrimalEdgeCenter R e).1 +
          (fkRectRefinedDeckTranslation R v).1,
        (fkRectRefinedPrimalEdgeCenter R e).2 +
          (fkRectRefinedDeckTranslation R v).2)
    c ≠ z := by
  dsimp only
  intro hcenter
  have hde : d = fkRectEdgeToDualEdge R e := by
    apply fkRectDualEdge_eq_edgeToDualEdge_of_refinedCenter_deck_mod_eq
      R d e u v
    dsimp only
    push_cast
    exact hcenter
  have hd' : fkRectDualConfigurationEquiv R omega
      (fkRectEdgeToDualEdge R e) = true := by
    rw [← hde]
    exact hd
  have hclosed :=
    (fkRectDualConfiguration_open_iff_primal_closed R omega e).mp hd'
  rw [he] at hclosed
  contradiction



theorem fkRectRefined_dualOpen_primalOpen_edgeBlocks_interaction_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (d e : R.EdgeIndex)
    (hd : fkRectDualConfigurationEquiv R omega d = true)
    (he : omega e = true) (u v : Int × Int) :
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    fkRectRefinedRawInteraction
        (((fkRectRefinedDualEdgeDarts R d).map
          (fkRectIntegralSquareDartTranslate
            (fkRectRefinedDeckTranslation R u))).map
              (fkRectIntegralSquareDartMod L))
        (((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartTranslate
            (fkRectRefinedDeckTranslation R v))).map
              (fkRectIntegralSquareDartMod L)) = 0 := by
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  dsimp only
  rw [fkRectRefinedDualEdgeDarts_eq_centerline,
    fkRectRefinedPrimalEdgeDarts_eq_centerline,
    fkRectRefinedPrimalCenterlineDarts_translate,
    fkRectRefinedPrimalCenterlineDarts_translate]
  by_cases hpair : fkRectClosedPairingAtEdge d =
      fkRectClosedPairingAtEdge e
  · rw [hpair]
    exact fkRectRefined_parallel_centerlines_interaction_eq_zero
      (fkRectClosedPairingAtEdge e) _ _
  · have hopp : fkRectClosedPairingAtEdge d =
        !(fkRectClosedPairingAtEdge e) := by
      cases hd0 : fkRectClosedPairingAtEdge d <;>
        cases he0 : fkRectClosedPairingAtEdge e <;> simp_all
    rw [hopp]
    have hdual := fkRectRefinedDualEdgeCenter_deck_normal R d u
    rw [hopp] at hdual
    have hdual' : FKRectRefinedEdgeCenterNormal
        (fkRectClosedPairingAtEdge e)
        ((fkRectRefinedDualEdgeCenter R d).1 +
            (fkRectRefinedDeckTranslation R u).1,
          (fkRectRefinedDualEdgeCenter R d).2 +
            (fkRectRefinedDeckTranslation R u).2) := by
      simpa using hdual
    have hprimal : FKRectRefinedEdgeCenterNormal
        (fkRectClosedPairingAtEdge e)
        ((fkRectRefinedPrimalEdgeCenter R e).1 +
            (fkRectRefinedDeckTranslation R v).1,
          (fkRectRefinedPrimalEdgeCenter R e).2 +
            (fkRectRefinedDeckTranslation R v).2) := by
      simpa [fkRectRefinedDeckTranslation] using
        (fkRectRefinedPrimalEdgeCenter_normal R e).add_four
          (fkRectSquareDeckTranslation R v).1
          (fkRectSquareDeckTranslation R v).2
    rw [fkRectRefined_perpendicular_legal_centerlines_interaction
      R (fkRectClosedPairingAtEdge e) _ _ hdual' hprimal]
    have hne := fkRectRefinedDualOpen_primalOpen_centers_mod_ne
      R omega d e hd he u v
    dsimp only at hne
    rw [if_neg (by
      intro hcenter
      apply hne
      simp only [Prod.fst, Prod.snd] at hcenter
      push_cast at hcenter ⊢
      exact hcenter)]

end

end StatMech.FrontierD
