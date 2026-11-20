/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedDualPrimalOpenInteraction
import Code.FrontierD.FKRectFaithfulShearEmbedding



namespace StatMech.FrontierD

noncomputable section


def FKRectIntegralDartListUsesPoint
    (l : List FKRectIntegralSquareDart) (p : Int × Int) : Prop :=
  p ∈ l.flatMap (fun d => [d.1, fkRectIntegralSquareDartEnd d])

theorem FKRectIntegralDartListUsesPoint.of_mem_source
    {l : List FKRectIntegralSquareDart} {d : FKRectIntegralSquareDart}
    (hd : d ∈ l) :
    FKRectIntegralDartListUsesPoint l d.1 := by
  apply List.mem_flatMap.mpr
  exact ⟨d, hd, by simp⟩

theorem FKRectIntegralDartListUsesPoint.of_mem_end
    {l : List FKRectIntegralSquareDart} {d : FKRectIntegralSquareDart}
    (hd : d ∈ l) :
    FKRectIntegralDartListUsesPoint l (fkRectIntegralSquareDartEnd d) := by
  apply List.mem_flatMap.mpr
  exact ⟨d, hd, by simp⟩

theorem fkRectIntegralDartListUsesPoint_append
    (l k : List FKRectIntegralSquareDart) (p : Int × Int) :
    FKRectIntegralDartListUsesPoint (l ++ k) p ↔
      FKRectIntegralDartListUsesPoint l p ∨
        FKRectIntegralDartListUsesPoint k p := by
  simp [FKRectIntegralDartListUsesPoint]

theorem fkRectIntegralDartListUsesPoint_reverse
    (l : List FKRectIntegralSquareDart) (p : Int × Int) :
    FKRectIntegralDartListUsesPoint
        (fkRectIntegralSquareDartListReverse l) p ↔
      FKRectIntegralDartListUsesPoint l p := by
  induction l with
  | nil => simp [FKRectIntegralDartListUsesPoint,
      fkRectIntegralSquareDartListReverse]
  | cons d l ih =>
      rw [show fkRectIntegralSquareDartListReverse (d :: l) =
          fkRectIntegralSquareDartListReverse l ++
            [fkRectIntegralSquareDartReverse d] by
        simp [fkRectIntegralSquareDartListReverse]]
      rw [fkRectIntegralDartListUsesPoint_append, ih]
      rcases d with ⟨⟨x, y⟩, mu⟩
      fin_cases mu <;>
        simp [FKRectIntegralDartListUsesPoint,
          fkRectIntegralSquareDartReverse,
          fkRectIntegralSquareDartEnd,
          StatMech.Onsager.ons_dirExponentX,
          StatMech.Onsager.ons_dirExponentY] <;> aesop



theorem fkRectRefined_perpendicular_centerlines_center_eq_of_integral_commonPoint
    (pairing : Bool) (c z p : Int × Int)
    (hc : FKRectRefinedEdgeCenterNormal pairing c)
    (hz : FKRectRefinedEdgeCenterNormal pairing z)
    (hl : FKRectIntegralDartListUsesPoint
      (fkRectRefinedPrimalCenterlineDarts (!pairing) c) p)
    (hr : FKRectIntegralDartListUsesPoint
      (fkRectRefinedPrimalCenterlineDarts pairing z) p) :
    c = z := by
  cases pairing
  · simp only [FKRectRefinedEdgeCenterNormal, if_false] at hc hz
    obtain ⟨x, y, rfl⟩ := hc
    obtain ⟨a, b, rfl⟩ := hz
    simp [FKRectIntegralDartListUsesPoint,
      fkRectRefinedPrimalCenterlineDarts,
      fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY, Prod.ext_iff] at hl hr ⊢
    omega
  · simp only [FKRectRefinedEdgeCenterNormal, if_true] at hc hz
    obtain ⟨x, y, rfl⟩ := hc
    obtain ⟨a, b, rfl⟩ := hz
    simp [FKRectIntegralDartListUsesPoint,
      fkRectRefinedPrimalCenterlineDarts,
      fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY, Prod.ext_iff] at hl hr ⊢
    omega



theorem fkRectRefined_parallel_oppositeNormal_centerlines_pointDisjoint
    (pairing : Bool) (c z p : Int × Int)
    (hc : FKRectRefinedEdgeCenterNormal (!pairing) c)
    (hz : FKRectRefinedEdgeCenterNormal pairing z)
    (hl : FKRectIntegralDartListUsesPoint
      (fkRectRefinedPrimalCenterlineDarts pairing c) p) :
    ¬ FKRectIntegralDartListUsesPoint
      (fkRectRefinedPrimalCenterlineDarts pairing z) p := by
  intro hr
  cases pairing
  · simp only [Bool.not_false, FKRectRefinedEdgeCenterNormal,
      if_true] at hc
    simp only [FKRectRefinedEdgeCenterNormal, if_false] at hz
    obtain ⟨x, y, rfl⟩ := hc
    obtain ⟨a, b, rfl⟩ := hz
    simp [FKRectIntegralDartListUsesPoint,
      fkRectRefinedPrimalCenterlineDarts,
      fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY, Prod.ext_iff] at hl hr
    omega
  · simp only [Bool.not_true, FKRectRefinedEdgeCenterNormal,
      if_false] at hc
    simp only [FKRectRefinedEdgeCenterNormal, if_true] at hz
    obtain ⟨x, y, rfl⟩ := hc
    obtain ⟨a, b, rfl⟩ := hz
    simp [FKRectIntegralDartListUsesPoint,
      fkRectRefinedPrimalCenterlineDarts,
      fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY, Prod.ext_iff] at hl hr
    omega



theorem fkRectRefined_dualOpen_primalOpen_edgeBlocks_pointDisjoint
    (R : FKRectTorus) (omega : R.Configuration)
    (d e : R.EdgeIndex)
    (hd : fkRectDualConfigurationEquiv R omega d = true)
    (he : omega e = true) (u v : Int × Int) :
    ∀ p,
      FKRectIntegralDartListUsesPoint
        ((fkRectRefinedDualEdgeDarts R d).map
          (fkRectIntegralSquareDartTranslate
            (fkRectRefinedDeckTranslation R u))) p →
      ¬ FKRectIntegralDartListUsesPoint
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartTranslate
            (fkRectRefinedDeckTranslation R v))) p := by
  rw [fkRectRefinedDualEdgeDarts_eq_centerline,
    fkRectRefinedPrimalEdgeDarts_eq_centerline,
    fkRectRefinedPrimalCenterlineDarts_translate,
    fkRectRefinedPrimalCenterlineDarts_translate]
  intro p hpdual hpprimal
  let c : Int × Int :=
    ((fkRectRefinedDualEdgeCenter R d).1 +
        (fkRectRefinedDeckTranslation R u).1,
      (fkRectRefinedDualEdgeCenter R d).2 +
        (fkRectRefinedDeckTranslation R u).2)
  let z : Int × Int :=
    ((fkRectRefinedPrimalEdgeCenter R e).1 +
        (fkRectRefinedDeckTranslation R v).1,
      (fkRectRefinedPrimalEdgeCenter R e).2 +
        (fkRectRefinedDeckTranslation R v).2)
  have hdual := fkRectRefinedDualEdgeCenter_deck_normal R d u
  have hprimal : FKRectRefinedEdgeCenterNormal
      (fkRectClosedPairingAtEdge e) z := by
    simpa [z, fkRectRefinedDeckTranslation] using
      (fkRectRefinedPrimalEdgeCenter_normal R e).add_four
        (fkRectSquareDeckTranslation R v).1
        (fkRectSquareDeckTranslation R v).2
  by_cases hpair : fkRectClosedPairingAtEdge d =
      fkRectClosedPairingAtEdge e
  · have hdual' : FKRectRefinedEdgeCenterNormal
        (!(fkRectClosedPairingAtEdge e)) c := by
      simpa [c, hpair] using hdual
    exact fkRectRefined_parallel_oppositeNormal_centerlines_pointDisjoint
      (fkRectClosedPairingAtEdge e) c z p hdual' hprimal
      (by simpa [c, hpair] using hpdual) (by simpa [z] using hpprimal)
  · have hopp : fkRectClosedPairingAtEdge d =
        !(fkRectClosedPairingAtEdge e) := by
      cases hd0 : fkRectClosedPairingAtEdge d <;>
        cases he0 : fkRectClosedPairingAtEdge e <;> simp_all
    have hdual' : FKRectRefinedEdgeCenterNormal
        (fkRectClosedPairingAtEdge e) c := by
      simpa [c, hopp] using hdual
    have hcz : c = z :=
      fkRectRefined_perpendicular_centerlines_center_eq_of_integral_commonPoint
        (fkRectClosedPairingAtEdge e) c z p hdual' hprimal
        (by simpa [c, hopp] using hpdual) (by simpa [z] using hpprimal)
    have hne := fkRectRefinedDualOpen_primalOpen_centers_mod_ne
      R omega d e hd he u v
    apply hne
    push_cast
    simpa [c, z] using congrArg (fun a : Int × Int =>
      (((a.1 : Int) : ZMod
          (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))),
        ((a.2 : Int) : ZMod
          (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))))) hcz



theorem FKRectRefinedOpenEdgeBlocks.pointDisjoint_from_dualEdgeBlock
    (R : FKRectTorus) (omega : R.Configuration)
    (F : Finset R.EdgeIndex)
    (hF : ∀ e, e ∈ F ↔ omega e = true)
    {k : List FKRectIntegralSquareDart}
    (hk : FKRectRefinedOpenEdgeBlocks R F k)
    (d : R.EdgeIndex) (u : Int × Int)
    (hd : fkRectDualConfigurationEquiv R omega d = true) :
    ∀ p,
      FKRectIntegralDartListUsesPoint
        ((fkRectRefinedDualEdgeDarts R d).map
          (fkRectIntegralSquareDartTranslate
            (fkRectRefinedDeckTranslation R u))) p →
      ¬ FKRectIntegralDartListUsesPoint k p := by
  induction hk with
  | nil => simp [FKRectIntegralDartListUsesPoint]
  | @consForward e v he l tail ih =>
      intro p hpdual hp
      rw [fkRectIntegralDartListUsesPoint_append] at hp
      rcases hp with hp | hp
      · exact fkRectRefined_dualOpen_primalOpen_edgeBlocks_pointDisjoint
          R omega d e hd ((hF e).mp he) u v p hpdual hp
      · exact ih p hpdual hp
  | @consReverse e v he l tail ih =>
      intro p hpdual hp
      rw [fkRectIntegralDartListUsesPoint_append] at hp
      rcases hp with hp | hp
      · have hrev : FKRectIntegralDartListUsesPoint
            (fkRectIntegralSquareDartListReverse
              ((fkRectRefinedPrimalEdgeDarts R e).map
                (fkRectIntegralSquareDartTranslate
                  (fkRectRefinedDeckTranslation R v)))) p := by
          rw [fkRectIntegralSquareDartListReverse_translate]
          exact hp
        have hforward :=
          (fkRectIntegralDartListUsesPoint_reverse
            ((fkRectRefinedPrimalEdgeDarts R e).map
              (fkRectIntegralSquareDartTranslate
                (fkRectRefinedDeckTranslation R v))) p).mp hrev
        exact fkRectRefined_dualOpen_primalOpen_edgeBlocks_pointDisjoint
          R omega d e hd ((hF e).mp he) u v p hpdual hforward
      · exact ih p hpdual hp



theorem FKRectRefinedDualOpenEdgeBlocks.pointDisjoint_of_edgeBlocks
    (R : FKRectTorus) (omega : R.Configuration)
    (F : Finset R.EdgeIndex)
    (hF : ∀ e, e ∈ F ↔ omega e = true)
    {l k : List FKRectIntegralSquareDart}
    (hl : FKRectRefinedDualOpenEdgeBlocks R omega l)
    (hk : FKRectRefinedOpenEdgeBlocks R F k) :
    ∀ p, FKRectIntegralDartListUsesPoint l p →
      ¬ FKRectIntegralDartListUsesPoint k p := by
  induction hl with
  | nil => simp [FKRectIntegralDartListUsesPoint]
  | @consForward d u hd l tail ih =>
      intro p hpdual hpprimal
      rw [fkRectIntegralDartListUsesPoint_append] at hpdual
      rcases hpdual with hpdual | hpdual
      · exact hk.pointDisjoint_from_dualEdgeBlock R omega F hF d u hd
          p hpdual hpprimal
      · exact ih p hpdual hpprimal
  | @consReverse d u hd l tail ih =>
      intro p hpdual hpprimal
      rw [fkRectIntegralDartListUsesPoint_append] at hpdual
      rcases hpdual with hpdual | hpdual
      · have hrev : FKRectIntegralDartListUsesPoint
            (fkRectIntegralSquareDartListReverse
              ((fkRectRefinedDualEdgeDarts R d).map
                (fkRectIntegralSquareDartTranslate
                  (fkRectRefinedDeckTranslation R u)))) p := by
          rw [fkRectIntegralSquareDartListReverse_translate]
          exact hpdual
        have hforward :=
          (fkRectIntegralDartListUsesPoint_reverse
            ((fkRectRefinedDualEdgeDarts R d).map
              (fkRectIntegralSquareDartTranslate
                (fkRectRefinedDeckTranslation R u))) p).mp hrev
        exact hk.pointDisjoint_from_dualEdgeBlock R omega F hF d u hd
          p hforward hpprimal
      · exact ih p hpdual hpprimal



theorem FKRectRefinedDualOpenEdgeBlocks.not_incident_of_mem_edgeBlocks
    (R : FKRectTorus) (omega : R.Configuration)
    (F : Finset R.EdgeIndex)
    (hF : ∀ e, e ∈ F ↔ omega e = true)
    {l k : List FKRectIntegralSquareDart}
    (hl : FKRectRefinedDualOpenEdgeBlocks R omega l)
    (hk : FKRectRefinedOpenEdgeBlocks R F k)
    {d e : FKRectIntegralSquareDart} (hd : d ∈ l) (he : e ∈ k) :
    ¬ FKRectIntegralSquareDartsIncident d e := by
  intro hincident
  have hdisjoint := hl.pointDisjoint_of_edgeBlocks R omega F hF hk
  rcases hincident with h | h | h | h
  · apply hdisjoint d.1
      (FKRectIntegralDartListUsesPoint.of_mem_source hd)
      (by simpa [h] using FKRectIntegralDartListUsesPoint.of_mem_source he)
  · apply hdisjoint d.1
      (FKRectIntegralDartListUsesPoint.of_mem_source hd)
      (by simpa [h] using FKRectIntegralDartListUsesPoint.of_mem_end he)
  · apply hdisjoint (fkRectIntegralSquareDartEnd d)
      (FKRectIntegralDartListUsesPoint.of_mem_end hd)
      (by simpa [h] using FKRectIntegralDartListUsesPoint.of_mem_source he)
  · apply hdisjoint (fkRectIntegralSquareDartEnd d)
      (FKRectIntegralDartListUsesPoint.of_mem_end hd)
      (by simpa [h] using FKRectIntegralDartListUsesPoint.of_mem_end he)

end

end StatMech.FrontierD
