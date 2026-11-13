/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDualBarrierLocalizedCycle
import Code.FrontierD.FKRectFaithfulDualConfinement
import Code.FrontierD.FKRectFaithfulVerticalRepeat
import Code.FrontierD.FKRectFaithfulWalkExtrema
import Code.FrontierD.FKRectFaithfulHorizontalExtension



open SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice
open StatMech.RSW.Box

noncomputable section

private theorem FKRectRefinedOpenEdgeBlocks.append
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    {l k : List FKRectIntegralSquareDart}
    (hl : FKRectRefinedOpenEdgeBlocks R F l)
    (hk : FKRectRefinedOpenEdgeBlocks R F k) :
    FKRectRefinedOpenEdgeBlocks R F (l ++ k) := by
  induction hl with
  | nil => simpa using hk
  | consForward e u he tail ih =>
      rw [List.append_assoc]
      exact .consForward e u he ih
  | consReverse e u he tail ih =>
      rw [List.append_assoc]
      exact .consReverse e u he ih

private theorem FKRectRefinedOpenEdgeBlocks.translate_refinedDeck
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    {l : List FKRectIntegralSquareDart}
    (hl : FKRectRefinedOpenEdgeBlocks R F l) (v : Int × Int) :
    FKRectRefinedOpenEdgeBlocks R F
      (l.map (fkRectIntegralSquareDartTranslate
        (fkRectRefinedDeckTranslation R v))) := by
  induction hl with
  | nil => simpa using (FKRectRefinedOpenEdgeBlocks.nil (R := R) (F := F))
  | consForward e u he tail ih =>
      rw [List.map_append, fkRectIntegralSquareDartList_translate_comp]
      change FKRectRefinedOpenEdgeBlocks R F
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartTranslate
            ((fkRectRefinedDeckTranslation R u).1 +
                (fkRectRefinedDeckTranslation R v).1,
              (fkRectRefinedDeckTranslation R u).2 +
                (fkRectRefinedDeckTranslation R v).2)) ++ _)
      rw [fkRectRefinedDeckTranslation_add]
      exact .consForward e (u.1 + v.1, u.2 + v.2) he ih
  | consReverse e u he tail ih =>
      rw [List.map_append, fkRectIntegralSquareDartList_translate_comp]
      change FKRectRefinedOpenEdgeBlocks R F
        ((fkRectIntegralSquareDartListReverse
          (fkRectRefinedPrimalEdgeDarts R e)).map
            (fkRectIntegralSquareDartTranslate
              ((fkRectRefinedDeckTranslation R u).1 +
                  (fkRectRefinedDeckTranslation R v).1,
                (fkRectRefinedDeckTranslation R u).2 +
                  (fkRectRefinedDeckTranslation R v).2)) ++ _)
      rw [fkRectRefinedDeckTranslation_add]
      exact .consReverse e (u.1 + v.1, u.2 + v.2) he ih

private theorem FKRectRefinedOpenEdgeBlocks.repeatTranslated_refinedDeck
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    {l : List FKRectIntegralSquareDart}
    (hl : FKRectRefinedOpenEdgeBlocks R F l)
    (v : Int × Int) (n : Nat) :
    FKRectRefinedOpenEdgeBlocks R F
      (fkRectRepeatTranslatedDartPath l
        (fkRectRefinedDeckTranslation R v) n) := by
  induction n with
  | zero => simpa [fkRectRepeatTranslatedDartPath] using
      (FKRectRefinedOpenEdgeBlocks.nil (R := R) (F := F))
  | succ n ih =>
      rw [fkRectRepeatTranslatedDartPath]
      apply ih.append R F
      rw [fkRectNatScale_refinedDeckTranslation]
      exact hl.translate_refinedDeck R F
        ((n : Int) * v.1, (n : Int) * v.2)

private theorem FKRectSquareWalkLift.refined_end_sub_eq_deck_winding
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x : R.Vertex} {w : G.Walk x x} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    fkRectRefinedScalePoint (fkRectSquareDevelopPoint q) -
        fkRectRefinedScalePoint (fkRectSquareDevelopPoint p) =
      fkRectRefinedDeckTranslation R (fkRectWalkWinding R w) := by
  have hd := h.closed_develop_sub_eq_deck_winding R
  apply Prod.ext
  · have hx := congrArg Prod.fst hd
    simp only [Prod.fst_sub] at hx
    change 4 * (fkRectSquareDevelopPoint q).1 -
      4 * (fkRectSquareDevelopPoint p).1 =
        4 * (fkRectSquareDeckTranslation R (fkRectWalkWinding R w)).1
    linear_combination 4 * hx
  · have hy := congrArg Prod.snd hd
    simp only [Prod.snd_sub] at hy
    change 4 * (fkRectSquareDevelopPoint q).2 -
      4 * (fkRectSquareDevelopPoint p).2 =
        4 * (fkRectSquareDeckTranslation R (fkRectWalkWinding R w)).2
    linear_combination 4 * hy

private theorem FKRectSquareWalkLift.end_fst_eq_val_of_support_columnZeroBand
    (R : FKRectTorus) (right : Nat) (hproper : right + 1 < R.width)
    {G : SimpleGraph R.Vertex} {x y : R.Vertex}
    {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q)
    (hsupport : ∀ v ∈ w.support, v.1.val ≤ right)
    (hpcol : p.1 = (x.1.val : Int)) :
    q.1 = (y.1.val : Int) := by
  induction h with
  | nil p hp => simpa using hpcol
  | @cons x y z hxy w p q r hp hq hdisp haxis tail ih =>
      have hxright := hsupport x (by simp)
      have hyright := hsupport y (by simp)
      have hnot : ¬ fkRectCrossesHorizontalSeam R s(x, y) := by
        rw [fkRectCrossesHorizontalSeam_mk]
        push Not
        constructor <;> omega
      have hinc : fkRectHorizontalSeamIncrement R x y = 0 := by
        unfold fkRectHorizontalSeamIncrement
        by_cases hxy' : x.1.val + 1 = R.width ∧ y.1.val = 0
        · exact (hnot (Or.inr ⟨hxy'.2, hxy'.1⟩)).elim
        · by_cases hyx : x.1.val = 0 ∧ y.1.val + 1 = R.width
          · exact (hnot (Or.inl hyx)).elim
          · simp [hxy', hyx]
      have hfirst := congrArg Prod.fst hdisp
      simp only [Prod.fst_sub, fkRectDevelopedStep] at hfirst
      rw [hinc] at hfirst
      simp only [mul_zero, add_zero] at hfirst
      have hqcol : q.1 = (y.1.val : Int) := by omega
      apply ih
      · intro v hv
        exact hsupport v (by simp [hv])
      · exact hqcol

private theorem fkRectFaithfulWalks_supportDisjoint_of_route_provenance
    (R : FKRectTorus) (omega : R.Configuration)
    (F : Finset R.EdgeIndex)
    (hF : ∀ e, e ∈ F ↔ omega e = true)
    {p q a b : Int × Int}
    {l k : List FKRectIntegralSquareDart}
    (hlblocks : FKRectRefinedDualOpenEdgeBlocks R omega l)
    (hkblocks : FKRectRefinedOpenEdgeBlocks R F k)
    (V : (hypercubicLattice 2).Walk
      (fkRectFaithfulShearPoint p) (fkRectFaithfulShearPoint q))
    (W : (hypercubicLattice 2).Walk
      (fkRectFaithfulShearPoint a) (fkRectFaithfulShearPoint b))
    (hV : ∀ z ∈ V.support,
      ∃ d ∈ l, ∃ r ∈ fkRectFaithfulShearDartRoute d,
        z = fkRectPairSite r)
    (hW : ∀ z ∈ W.support,
      ∃ d ∈ k, ∃ r ∈ fkRectFaithfulShearDartRoute d,
        z = fkRectPairSite r) :
    ∀ z, z ∈ V.support → z ∈ W.support → False := by
  intro z hzV hzW
  obtain ⟨d, hdl, r, hr, hzVr⟩ := hV z hzV
  obtain ⟨e, hek, s, hs, hzWs⟩ := hW z hzW
  have hincident :=
    fkRectIntegralSquareDartsIncident_of_faithfulRouteSite d e r s hr hs
      (hzVr.symm.trans hzWs)
  exact (hlblocks.not_incident_of_mem_edgeBlocks
    R omega F hF hkblocks hdl hek) hincident




theorem fkRectLocalizedVerticalCycle_mem_dualPreimage_noLeftStripCrossing
    (R : FKRectTorus) (right : Nat) (hright : 1 ≤ right)
    (hproper : right + 1 < R.width)
    (forced : R.Configuration)
    (z : (fkRectOpenGraph R forced).Walk
      (fkRectRowOneVertex R (fkRectUnitGapColumn R))
      (fkRectRowOneVertex R (fkRectUnitGapColumn R)))
    (hzWinding : fkRectWalkWinding R z = (0, 1))
    (hzSupport : ∀ v ∈ z.support,
      1 ≤ v.1.val ∧ v.1.val ≤ right) :
    forced ∈ fkRectDualPreimageEvent R
      (fkRectNoLeftStripCrossingEvent R right) := by
  change fkRectDualConfigurationEquiv R forced ∈
    fkRectNoLeftStripCrossingEvent R right
  intro hcross
  rcases hcross with ⟨x, hxColumn, y, hyColumn, hreach⟩
  obtain ⟨wStrip⟩ := hreach
  let strip := fkRectLeftStrip R right
  let inclusion :
      (fkRectOpenGraph R
        (fkRectDualConfigurationEquiv R forced)).induce strip ↪g
        fkRectOpenGraph R (fkRectDualConfigurationEquiv R forced) :=
    SimpleGraph.Embedding.induce strip
  let w := wStrip.map inclusion.toHom
  change (fkRectOpenGraph R
    (fkRectDualConfigurationEquiv R forced)).Walk x.1 y.1 at w
  have hwSupport : ∀ v ∈ w.support, v.1.val ≤ right := by
    intro v hv
    change v ∈ (wStrip.map inclusion.toHom).support at hv
    rw [Walk.support_map] at hv
    obtain ⟨v', hv', rfl⟩ := List.mem_map.mp hv
    exact v'.property
  let p : Int × Int := ((x.1.1.val : Int), (x.1.2.val : Int))
  have hp : fkRectLiftedVertex R p = x.1 := by
    apply Prod.ext <;> simp [p, fkRectLiftedVertex]
  obtain ⟨q, l, hq, hwlift, hlpath, hlblocks, hlalong⟩ :=
    exists_fkRectRefinedDualOpenWalkCarrierAlong R forced w p hp
  have hpcol : p.1 = (x.1.1.val : Int) := rfl
  have hqcol : q.1 = (y.1.1.val : Int) :=
    hwlift.end_fst_eq_val_of_support_columnZeroBand
      R right hproper hwSupport hpcol
  have hpcolZero : p.1 = 0 := by
    rw [hpcol]
    change x.1.1.val = 0 at hxColumn
    exact_mod_cast hxColumn
  have hqcolRight : q.1 = (right : Int) := by
    rw [hqcol, hyColumn]
  let DP := fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)
  let DQ := fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint q)
  have hDPx :
      8 ≤ (fkRectFaithfulShearPoint DP) 0 ∧
        (fkRectFaithfulShearPoint DP) 0 ≤ 16 := by
    simpa [DP, hpcolZero] using
      (fkRectFaithfulShearPoint_refinedDualScale_develop_fst_bounds
        p 0 (by omega) (by omega))
  have hDQx :
      16 * (right : Int) + 8 ≤
          (fkRectFaithfulShearPoint DQ) 0 ∧
        (fkRectFaithfulShearPoint DQ) 0 ≤
          16 * (right : Int) + 16 := by
    rw [show DQ = fkRectRefinedDualScalePoint
      (fkRectSquareDevelopPoint q) by rfl,
      fkRectFaithfulShearPoint_refinedDualScale_eq]
    have h :=
      fkRectFaithfulShearPoint_refinedScale_develop_fst_bounds
        q right right (by omega) (by omega)
    simp only [Matrix.cons_val_zero]
    omega
  have hlne : l ≠ [] := by
    apply hlpath.ne_nil_of_ne
    intro hEq
    have hfaithful := congrArg fkRectFaithfulShearPoint hEq
    have hxEq := congrFun hfaithful 0
    change (fkRectFaithfulShearPoint DP) 0 =
      (fkRectFaithfulShearPoint DQ) 0 at hxEq
    omega
  obtain ⟨W, hWroute⟩ :=
    hlpath.exists_faithfulShearWalk_of_ne_nil hlne
  have hWfst : ∀ z ∈ W.support,
      8 ≤ z 0 ∧ z 0 ≤ 16 * (right : Int) + 16 := by
    intro z hz
    obtain ⟨d, hdl, r, hr, rfl⟩ := hWroute z hz
    simpa [fkRectPairSite] using
      hlalong.faithfulRoute_fst_bounds R forced right hproper
        hwSupport hpcol hdl hr
  obtain ⟨M, hWvertical⟩ :=
    exists_fkRectFaithfulWalk_vertical_natAbs_bound W

  let F := fkRectOpenEdges R forced
  have hconfiguration : fkRectConfigurationOfEdges R F = forced := by
    simp [F]
  have hle : fkRectOpenGraph R forced ≤
      fkRectOpenGraph R (fkRectConfigurationOfEdges R F) := by
    rw [hconfiguration]
  let zF := z.mapLe hle
  let a : Int × Int :=
    (((fkRectRowOneVertex R (fkRectUnitGapColumn R)).1.val : Int),
      ((fkRectRowOneVertex R (fkRectUnitGapColumn R)).2.val : Int))
  have ha : fkRectLiftedVertex R a =
      fkRectRowOneVertex R (fkRectUnitGapColumn R) := by
    apply Prod.ext <;> simp [a, fkRectLiftedVertex]
  obtain ⟨b, k, hb, hzlift, hkpath, hkblocks, hkalong⟩ :=
    exists_fkRectRefinedOpenWalkCarrierAlong R F zF a ha
  have hzFWinding : fkRectWalkWinding R zF = (0, 1) := by
    simpa [zF, fkRectWalkWinding_mapLe] using hzWinding
  let P := fkRectRefinedScalePoint (fkRectSquareDevelopPoint a)
  let Q := fkRectRefinedScalePoint (fkRectSquareDevelopPoint b)
  let deck := fkRectRefinedDeckTranslation R ((0, 1) : Int × Int)
  have hQPsub : Q - P = deck := by
    simpa [P, Q, deck, hzFWinding] using
      hzlift.refined_end_sub_eq_deck_winding R
  have hQ : Q = (P.1 + deck.1, P.2 + deck.2) := by
    apply Prod.ext
    · have hx := congrArg Prod.fst hQPsub
      simp only [Prod.fst_sub] at hx ⊢
      omega
    · have hy := congrArg Prod.snd hQPsub
      simp only [Prod.snd_sub] at hy ⊢
      omega
  have hkne : k ≠ [] := by
    apply hkpath.ne_nil_of_ne
    intro hPQ
    have hdeckZero : deck = (0, 0) := by
      calc
        deck = Q - P := hQPsub.symm
        _ = (0, 0) := by
          change P = Q at hPQ
          apply Prod.ext <;> simp [hPQ]
    have hhalf : 0 < R.height / 2 :=
      Nat.div_pos R.height_gt_two.le (by norm_num)
    have hhalfInt : 0 < (R.height / 2 : Nat) := hhalf
    have hx := congrArg Prod.fst hdeckZero
    simp [deck, fkRectRefinedDeckTranslation,
      fkRectSquareDeckTranslation] at hx
    exact (by omega)
  have hkpath' : FKRectIntegralSquareDartPath P
      (P.1 + deck.1, P.2 + deck.2) k := by
    simpa [P, Q, hQ] using hkpath
  let s := (fkRectFaithfulShearPoint P) 1
  let m : Nat := M + s.natAbs + 1
  let n : Nat := 2 * m
  let shiftWinding : Int × Int := (0, -(m : Int))
  let shift := fkRectRefinedDeckTranslation R shiftWinding
  let repeated := fkRectRepeatTranslatedDartPath k deck n
  let translated := repeated.map (fkRectIntegralSquareDartTranslate shift)
  have hrepeatedPath := hkpath'.repeatTranslated n
  have htranslatedPath := hrepeatedPath.translate shift
  have hrepeatedNe : repeated ≠ [] := by
    apply fkRectRepeatTranslatedDartPath_ne_nil k deck n hkne
    simp [n, m]
  have htranslatedNe : translated ≠ [] := by
    simp [translated, hrepeatedNe]
  obtain ⟨V, hVroute⟩ :=
    htranslatedPath.exists_faithfulShearWalk_of_ne_nil htranslatedNe
  have hshiftHorizontal : shiftWinding.1 + shiftWinding.2 = -(m : Int) := by
    simp [shiftWinding]
  have hdeckHorizontal : ((0 : Int), (1 : Int)).1 +
      ((0 : Int), (1 : Int)).2 = 1 := by norm_num
  have hVfst : ∀ z ∈ V.support,
      16 ≤ z 0 ∧ z 0 ≤ 16 * (right : Int) + 8 := by
    intro v hv
    obtain ⟨d, hdtranslated, r, hr, rfl⟩ := hVroute v hv
    obtain ⟨d0, hd0repeated, rfl⟩ :=
      List.mem_map.mp hdtranslated
    obtain ⟨r0, hr0, hrfst⟩ :=
      fkRectFaithfulShearDartRoute_translate_fst shift d0 r hr
    have hshiftSum : shift.1 + shift.2 = 0 := by
      simp [shift, shiftWinding, fkRectRefinedDeckTranslation,
        fkRectSquareDeckTranslation]
    have hbase : ∀ d ∈ k, ∀ r ∈ fkRectFaithfulShearDartRoute d,
        16 ≤ r.1 ∧ r.1 ≤ 16 * (right : Int) + 8 := by
      intro d hdk r hr
      exact hkalong.faithfulRoute_fst_bounds R F right
        (by
          intro v hv
          have hvz : v ∈ z.support := by
            change v ∈ (z.map (SimpleGraph.Hom.ofLE hle)).support at hv
            rw [Walk.support_map] at hv
            obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
            exact hu
          exact hzSupport v hvz)
        rfl hdk hr
    have hrepeat :=
      fkRectRepeatTranslatedDartPath_faithfulRoute_fst_bounds
        k deck n (by
          simp [deck, fkRectRefinedDeckTranslation,
            fkRectSquareDeckTranslation])
        16 (16 * (right : Int) + 8) hbase hd0repeated hr0
    simpa [fkRectPairSite] using (show
      16 ≤ r.1 ∧ r.1 ≤ 16 * (right : Int) + 8 by
        rw [hrfst, hshiftSum]
        simpa using hrepeat)

  have hrepBlocks : FKRectRefinedOpenEdgeBlocks R F repeated := by
    simpa [repeated, deck] using
      hkblocks.repeatTranslated_refinedDeck R F ((0, 1) : Int × Int) n
  have htranslatedBlocks :
      FKRectRefinedOpenEdgeBlocks R F translated := by
    simpa [translated, shift] using
      hrepBlocks.translate_refinedDeck R F shiftWinding
  have hF : ∀ e, e ∈ F ↔ forced e = true := by
    intro e
    simp [F, fkRectOpenEdges]
  have hWVdisjoint : ∀ u, u ∈ W.support →
      u ∈ V.support → False :=
    fkRectFaithfulWalks_supportDisjoint_of_route_provenance
      R forced F hF hlblocks htranslatedBlocks W V hWroute hVroute

  let H : Int := 8 * (R.height : Int)
  have hH : 1 ≤ H := by
    dsimp [H]
    have := R.height_pos
    omega
  have hsAbs : |s| ≤ (s.natAbs : Int) := by
    rw [Int.natCast_natAbs]
  have hsBounds : -(s.natAbs : Int) ≤ s ∧
      s ≤ (s.natAbs : Int) :=
    ⟨neg_le_of_abs_le hsAbs, le_of_abs_le hsAbs⟩
  have hmNonneg : 0 ≤ (m : Int) := by positivity
  have hmMul : (m : Int) ≤ (m : Int) * H := by
    nlinarith
  have hstartY :
      (fkRectFaithfulShearPoint
        (P.1 + shift.1, P.2 + shift.2)) 1 =
        s - (m : Int) * H := by
    have h := congrFun
      (fkRectFaithfulShearPoint_add_refinedDeck R P shiftWinding) 1
    change 2 * (P.1 + shift.1 - (P.2 + shift.2)) =
      2 * (P.1 - P.2) - (m : Int) * (8 * (R.height : Int))
    simp [shiftWinding] at h
    dsimp [shift]
    linear_combination h
  let E : Int × Int :=
    ((P.1 + (n : Int) * deck.1, P.2 + (n : Int) * deck.2).1 +
        shift.1,
      (P.1 + (n : Int) * deck.1, P.2 + (n : Int) * deck.2).2 +
        shift.2)
  have hE : E =
      (P.1 + (fkRectRefinedDeckTranslation R ((0, (m : Int)))).1,
        P.2 + (fkRectRefinedDeckTranslation R ((0, (m : Int)))).2) := by
    apply Prod.ext <;>
      simp [E, n, deck, shift, shiftWinding,
        fkRectRefinedDeckTranslation, fkRectSquareDeckTranslation] <;> ring
  have hendY : (fkRectFaithfulShearPoint E) 1 =
      s + (m : Int) * H := by
    rw [hE]
    have h := congrFun
      (fkRectFaithfulShearPoint_add_refinedDeck
        R P ((0, (m : Int)))) 1
    change 2 *
        (P.1 + (fkRectRefinedDeckTranslation R ((0, (m : Int)))).1 -
          (P.2 + (fkRectRefinedDeckTranslation R ((0, (m : Int)))).2)) =
      2 * (P.1 - P.2) + (m : Int) * (8 * (R.height : Int))
    simp at h
    linear_combination h
  have hmDef : (m : Int) =
      (M : Int) + (s.natAbs : Int) + 1 := by
    simp [m]
  have hstartBelow :
      (fkRectFaithfulShearPoint
        (P.1 + shift.1, P.2 + shift.2)) 1 ≤ -(M : Int) := by
    rw [hstartY]
    omega
  have hendAbove : (M : Int) ≤
      (fkRectFaithfulShearPoint E) 1 := by
    rw [hendY]
    omega
  change (hypercubicLattice 2).Walk
    (fkRectFaithfulShearPoint (P.1 + shift.1, P.2 + shift.2))
    (fkRectFaithfulShearPoint E) at V
  obtain ⟨lower, upper, bottom, top, Vcore,
      hbottomRow, htopRow, hVvertical, hVcore⟩ :=
    exists_fkRectFaithfulWalk_verticalExtremaSubwalk V
  have hlowerM : lower ≤ -(M : Int) :=
    (hVvertical _ V.start_mem_support).1.trans hstartBelow
  have hMupper : (M : Int) ≤ upper :=
    hendAbove.trans (hVvertical _ V.end_mem_support).2
  have hLowerUpper : lower ≤ upper :=
    (hVvertical _ V.start_mem_support).1.trans
      (hVvertical _ V.start_mem_support).2
  have hVcoreFst : ∀ u ∈ Vcore.support,
      16 ≤ u 0 ∧ u 0 ≤ 16 * (right : Int) + 8 := by
    intro u hu
    exact hVfst u (hVcore u hu)
  have hVcoreRect : ∀ u ∈ Vcore.support,
      u ∈ rect 8 (16 * (right : Int) + 16) lower upper := by
    intro u hu
    rw [mem_rect]
    have hx := hVcoreFst u hu
    have hy := hVvertical u (hVcore u hu)
    omega
  let Vcross : (hypercubicLattice 2).Walk
      ![bottom 0, lower] ![top 0, upper] :=
    Vcore.copy (by
      funext i
      fin_cases i <;> simp [hbottomRow]) (by
      funext i
      fin_cases i <;> simp [htopRow])
  have hVcrossRect : ∀ u ∈ Vcross.support,
      u ∈ rect 8 (16 * (right : Int) + 16) lower upper := by
    intro u hu
    apply hVcoreRect u
    simpa [Vcross] using hu
  have hbottomFst := hVcoreFst bottom Vcore.start_mem_support
  have htopFst := hVcoreFst top Vcore.end_mem_support

  let beta : Int := 16 * (right : Int) + 16
  let Wcross := fkRectFaithfulHorizontalExtension 8 beta W
  have hWrect : ∀ u ∈ W.support,
      u ∈ rect 8 beta lower upper := by
    intro u hu
    rw [mem_rect]
    have hx := hWfst u hu
    have hy := hWvertical u hu
    dsimp [beta]
    omega
  have hWcrossRect : ∀ u ∈ Wcross.support,
      u ∈ rect 8 beta lower upper := by
    apply fkRectFaithfulHorizontalExtension_support_rect
      8 beta lower upper W
    · simpa [DP] using hDPx.1
    · simpa [DQ, beta] using hDQx.2
    · exact hWrect
  have hWcoreDisjoint : ∀ u, u ∈ W.support →
      u ∈ Vcore.support → False := by
    intro u huW huV
    exact hWVdisjoint u huW (hVcore u huV)
  have hWcrossDisjoint : ∀ u, u ∈ Wcross.support →
      u ∈ Vcore.support → False := by
    apply fkRectFaithfulHorizontalExtension_support_disjoint_of_core_bounds
      8 beta 16 (16 * (right : Int) + 8) W Vcore
    · simpa [DP] using hDPx.1
    · simpa [DP] using hDPx.2
    · simpa [DQ] using hDQx.1
    · simpa [DQ, beta] using hDQx.2
    · exact hVcoreFst
    · exact hWcoreDisjoint
  have hWstartRect := hWcrossRect _ Wcross.start_mem_support
  have hWendRect := hWcrossRect _ Wcross.end_mem_support
  obtain ⟨u, huW, huV⟩ :=
    fkRectFaithful_bottomTop_leftRight_support_intersects
      8 beta lower upper (bottom 0) (top 0)
      (by dsimp [beta]; omega) hLowerUpper
      (by omega) (by dsimp [beta]; omega)
      (by omega) (by dsimp [beta]; omega)
      Vcross hVcrossRect
      hWstartRect hWendRect (by simp) (by simp)
      Wcross hWcrossRect
  apply hWcrossDisjoint u huW
  simpa [Vcross] using huV




theorem fkRectForceDualPullbackUnitPattern_mem_dualPreimage_noLeftStripCrossing
    (R : FKRectTorus) (right : Nat) (hright : 1 ≤ right)
    (hproper : right + 1 < R.width)
    (omega : R.Configuration)
    (t : Finset
      (FKRectColumnBandVertex R 1 right 1 (R.height - 1) ×
        FKRectColumnBandVertex R 1 right 1 (R.height - 1)))
    (hspans : FKRectColumnBandConnectionChainSpans R 1 right
      (fkRectUnitGapColumn R) (by rfl) hright t)
    (haux : fkRectUnitDualBarrierAuxiliary R right t omega) :
    let forced := fkRectForceIndexedPattern R
      (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
      (fkRectDualPullbackConfiguration R
        (fkRectAllButOneOpenConfiguration R
          (fkRectUnitLeftBarrierGap R))) omega
    forced ∈ fkRectDualPreimageEvent R
      (fkRectNoLeftStripCrossingEvent R right) := by
  dsimp only
  let forced := fkRectForceIndexedPattern R
    (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
    (fkRectDualPullbackConfiguration R
      (fkRectAllButOneOpenConfiguration R
        (fkRectUnitLeftBarrierGap R))) omega
  obtain ⟨z, hzWinding, hzSupport⟩ :=
    exists_fkRectForceDualPullbackUnitPattern_localizedVerticalCycle
      R right hright hproper omega t hspans haux
  exact fkRectLocalizedVerticalCycle_mem_dualPreimage_noLeftStripCrossing
    R right hright hproper forced z hzWinding hzSupport

end

end StatMech.FrontierD
