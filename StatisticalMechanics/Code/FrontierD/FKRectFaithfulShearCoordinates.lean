/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectFaithfulShearEmbedding
import Code.FrontierD.FKRectRefinedDualPrimalInteractionAlgebra



namespace StatMech.FrontierD

noncomputable section

theorem fkRectRowParityTerm_bounds (y : Int) :
    0 ≤ (y + 1) / 2 - y / 2 ∧
      (y + 1) / 2 - y / 2 ≤ 1 := by
  omega

@[simp] theorem fkRectFaithfulShearPoint_apply_zero (p : Int × Int) :
    (fkRectFaithfulShearPoint p) 0 = 2 * (p.1 + p.2) := by
  simp [fkRectFaithfulShearPoint, fkRectFaithfulShearPair,
    fkRectPairSite]

@[simp] theorem fkRectFaithfulShearPoint_apply_one (p : Int × Int) :
    (fkRectFaithfulShearPoint p) 1 = 2 * (p.1 - p.2) := by
  simp [fkRectFaithfulShearPoint, fkRectFaithfulShearPair,
    fkRectPairSite]



theorem fkRectFaithfulShearPoint_refinedScale_develop_fst
    (p : Int × Int) :
    (fkRectFaithfulShearPoint
      (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 0 =
        16 * p.1 + 8 * ((p.2 + 1) / 2 - p.2 / 2) := by
  simp [fkRectRefinedScalePoint, fkRectSquareDevelopPoint]
  ring



theorem fkRectFaithfulShearPoint_refinedScale_develop_snd
    (p : Int × Int) :
    (fkRectFaithfulShearPoint
      (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 1 =
        8 * p.2 := by
  rw [fkRectFaithfulShearPoint_apply_one]
  simp only [fkRectRefinedScalePoint, Prod.fst, Prod.snd]
  have h := fkRectSquareDevelopPoint_fst_sub_snd p
  linear_combination 8 * h



theorem fkRectFaithfulShearPoint_refinedDualScale_eq
    (p : Int × Int) :
    fkRectFaithfulShearPoint (fkRectRefinedDualScalePoint p) =
      ![(fkRectFaithfulShearPoint (fkRectRefinedScalePoint p)) 0 + 8,
        (fkRectFaithfulShearPoint (fkRectRefinedScalePoint p)) 1] := by
  funext i
  fin_cases i <;>
    simp [fkRectRefinedDualScalePoint, fkRectRefinedScalePoint] <;> ring



theorem fkRectFaithfulShearPoint_refinedScale_develop_fst_bounds
    (p : Int × Int) (left right : Int)
    (hleft : left ≤ p.1) (hright : p.1 ≤ right) :
    16 * left ≤
        (fkRectFaithfulShearPoint
          (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 0 ∧
      (fkRectFaithfulShearPoint
          (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 0 ≤
        16 * right + 8 := by
  rw [fkRectFaithfulShearPoint_refinedScale_develop_fst]
  have hparity := fkRectRowParityTerm_bounds p.2
  omega



theorem fkRectFaithfulShearDartRoute_fst_between
    (d : FKRectIntegralSquareDart) (r : Int × Int)
    (hr : r ∈ fkRectFaithfulShearDartRoute d) :
    min (fkRectFaithfulShearPair d.1).1
          (fkRectFaithfulShearPair
            (fkRectIntegralSquareDartEnd d)).1 ≤ r.1 ∧
      r.1 ≤ max (fkRectFaithfulShearPair d.1).1
          (fkRectFaithfulShearPair
            (fkRectIntegralSquareDartEnd d)).1 := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  rcases r with ⟨a, b⟩
  fin_cases mu <;>
    simp [fkRectFaithfulShearDartRoute, fkRectFaithfulShearPair,
      fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] at hr ⊢ <;>
    omega



theorem fkRectFaithfulShearDartRoute_reverse_iff
    (d : FKRectIntegralSquareDart) (r : Int × Int) :
    r ∈ fkRectFaithfulShearDartRoute
        (fkRectIntegralSquareDartReverse d) ↔
      r ∈ fkRectFaithfulShearDartRoute d := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  rcases r with ⟨a, b⟩
  fin_cases mu <;>
    simp [fkRectIntegralSquareDartReverse,
      fkRectFaithfulShearDartRoute, fkRectFaithfulShearPair,
      fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY, Prod.ext_iff] <;> omega


theorem fkRectRefinedPrimalEdgeEnd_eq_start_axis
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectRefinedPrimalEdgeEnd R e =
      if fkRectClosedPairingAtEdge e then
        ((fkRectRefinedPrimalEdgeStart R e).1 - 4,
          (fkRectRefinedPrimalEdgeStart R e).2)
      else
        ((fkRectRefinedPrimalEdgeStart R e).1,
          (fkRectRefinedPrimalEdgeStart R e).2 + 4) := by
  have h := fkRectCanonicalSquareEdgeStep_eq R e
  by_cases hp : fkRectClosedPairingAtEdge e = true
  · simp [hp] at h ⊢
    unfold fkRectRefinedPrimalEdgeStart fkRectRefinedPrimalEdgeEnd
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at h1 h2
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega
  · have hp' : fkRectClosedPairingAtEdge e = false :=
      Bool.eq_false_of_not_eq_true hp
    simp [hp, hp'] at h ⊢
    unfold fkRectRefinedPrimalEdgeStart fkRectRefinedPrimalEdgeEnd
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at h1 h2
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega



theorem fkRectRefinedPrimalEdgeBlock_faithfulRoute_fst_between
    (R : FKRectTorus) (e : R.EdgeIndex) (t : Int × Int)
    (d : FKRectIntegralSquareDart) (r : Int × Int)
    (hd : d ∈ (fkRectRefinedPrimalEdgeDarts R e).map
      (fkRectIntegralSquareDartTranslate t))
    (hr : r ∈ fkRectFaithfulShearDartRoute d) :
    min (fkRectFaithfulShearPair
          ((fkRectRefinedPrimalEdgeStart R e).1 + t.1,
            (fkRectRefinedPrimalEdgeStart R e).2 + t.2)).1
        (fkRectFaithfulShearPair
          ((fkRectRefinedPrimalEdgeEnd R e).1 + t.1,
            (fkRectRefinedPrimalEdgeEnd R e).2 + t.2)).1 ≤ r.1 ∧
      r.1 ≤
        max (fkRectFaithfulShearPair
          ((fkRectRefinedPrimalEdgeStart R e).1 + t.1,
            (fkRectRefinedPrimalEdgeStart R e).2 + t.2)).1
        (fkRectFaithfulShearPair
          ((fkRectRefinedPrimalEdgeEnd R e).1 + t.1,
            (fkRectRefinedPrimalEdgeEnd R e).2 + t.2)).1 := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
  rw [fkRectRefinedPrimalEdgeEnd_eq_start_axis]
  by_cases hp : fkRectClosedPairingAtEdge e
  · simp only [hp, if_true]
    simp [fkRectRefinedPrimalEdgeDarts, hp] at ha
    rcases ha with rfl | rfl | rfl | rfl
    all_goals
      rcases r with ⟨x, y⟩
      simp [fkRectIntegralSquareDartTranslate,
        fkRectFaithfulShearDartRoute, fkRectFaithfulShearPair,
        fkRectIntegralSquareDartEnd,
        StatMech.Onsager.ons_dirExponentX,
        StatMech.Onsager.ons_dirExponentY] at hr ⊢ <;> omega
  · have hp' : fkRectClosedPairingAtEdge e = false :=
      Bool.eq_false_of_not_eq_true hp
    simp [hp, hp']
    simp [fkRectRefinedPrimalEdgeDarts, hp, hp'] at ha
    rcases ha with rfl | rfl | rfl | rfl
    all_goals
      rcases r with ⟨x, y⟩
      simp [fkRectIntegralSquareDartTranslate,
        fkRectFaithfulShearDartRoute, fkRectFaithfulShearPair,
        fkRectIntegralSquareDartEnd,
        StatMech.Onsager.ons_dirExponentX,
        StatMech.Onsager.ons_dirExponentY] at hr ⊢ <;> omega


theorem fkRectRefinedPrimalEdgeReverseBlock_faithfulRoute_fst_between
    (R : FKRectTorus) (e : R.EdgeIndex) (t : Int × Int)
    (d : FKRectIntegralSquareDart) (r : Int × Int)
    (hd : d ∈ (fkRectIntegralSquareDartListReverse
      (fkRectRefinedPrimalEdgeDarts R e)).map
        (fkRectIntegralSquareDartTranslate t))
    (hr : r ∈ fkRectFaithfulShearDartRoute d) :
    min (fkRectFaithfulShearPair
          ((fkRectRefinedPrimalEdgeStart R e).1 + t.1,
            (fkRectRefinedPrimalEdgeStart R e).2 + t.2)).1
        (fkRectFaithfulShearPair
          ((fkRectRefinedPrimalEdgeEnd R e).1 + t.1,
            (fkRectRefinedPrimalEdgeEnd R e).2 + t.2)).1 ≤ r.1 ∧
      r.1 ≤
        max (fkRectFaithfulShearPair
          ((fkRectRefinedPrimalEdgeStart R e).1 + t.1,
            (fkRectRefinedPrimalEdgeStart R e).2 + t.2)).1
        (fkRectFaithfulShearPair
          ((fkRectRefinedPrimalEdgeEnd R e).1 + t.1,
            (fkRectRefinedPrimalEdgeEnd R e).2 + t.2)).1 := by
  rw [← fkRectIntegralSquareDartListReverse_translate] at hd
  unfold fkRectIntegralSquareDartListReverse at hd
  obtain ⟨a, ha, hda⟩ := List.mem_map.mp hd
  rw [List.mem_reverse] at ha
  have hr' : r ∈ fkRectFaithfulShearDartRoute a := by
    rw [← fkRectFaithfulShearDartRoute_reverse_iff a r]
    rw [hda]
    exact hr
  exact fkRectRefinedPrimalEdgeBlock_faithfulRoute_fst_between
    R e t a r ha hr'


theorem fkRectRefinedDualEdgeEnd_eq_start_axis
    (R : FKRectTorus) (d : R.EdgeIndex) :
    fkRectRefinedDualEdgeEnd R d =
      if fkRectClosedPairingAtEdge d then
        ((fkRectRefinedDualEdgeStart R d).1 - 4,
          (fkRectRefinedDualEdgeStart R d).2)
      else
        ((fkRectRefinedDualEdgeStart R d).1,
          (fkRectRefinedDualEdgeStart R d).2 + 4) := by
  have h := fkRectCanonicalSquareEdgeStep_eq R d
  by_cases hp : fkRectClosedPairingAtEdge d = true
  · simp [hp] at h ⊢
    unfold fkRectRefinedDualEdgeStart fkRectRefinedDualEdgeEnd
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at h1 h2
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega
  · have hp' : fkRectClosedPairingAtEdge d = false :=
      Bool.eq_false_of_not_eq_true hp
    simp [hp, hp'] at h ⊢
    unfold fkRectRefinedDualEdgeStart fkRectRefinedDualEdgeEnd
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at h1 h2
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega



theorem fkRectRefinedDualEdgeBlock_faithfulRoute_fst_between
    (R : FKRectTorus) (e : R.EdgeIndex) (t : Int × Int)
    (d : FKRectIntegralSquareDart) (r : Int × Int)
    (hd : d ∈ (fkRectRefinedDualEdgeDarts R e).map
      (fkRectIntegralSquareDartTranslate t))
    (hr : r ∈ fkRectFaithfulShearDartRoute d) :
    min (fkRectFaithfulShearPair
          ((fkRectRefinedDualEdgeStart R e).1 + t.1,
            (fkRectRefinedDualEdgeStart R e).2 + t.2)).1
        (fkRectFaithfulShearPair
          ((fkRectRefinedDualEdgeEnd R e).1 + t.1,
            (fkRectRefinedDualEdgeEnd R e).2 + t.2)).1 ≤ r.1 ∧
      r.1 ≤
        max (fkRectFaithfulShearPair
          ((fkRectRefinedDualEdgeStart R e).1 + t.1,
            (fkRectRefinedDualEdgeStart R e).2 + t.2)).1
        (fkRectFaithfulShearPair
          ((fkRectRefinedDualEdgeEnd R e).1 + t.1,
            (fkRectRefinedDualEdgeEnd R e).2 + t.2)).1 := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
  rw [fkRectRefinedDualEdgeEnd_eq_start_axis]
  by_cases hp : fkRectClosedPairingAtEdge e
  · simp only [hp, if_true]
    simp [fkRectRefinedDualEdgeDarts, hp] at ha
    rcases ha with rfl | rfl | rfl | rfl
    all_goals
      rcases r with ⟨x, y⟩
      simp [fkRectIntegralSquareDartTranslate,
        fkRectFaithfulShearDartRoute, fkRectFaithfulShearPair,
        fkRectIntegralSquareDartEnd,
        StatMech.Onsager.ons_dirExponentX,
        StatMech.Onsager.ons_dirExponentY] at hr ⊢ <;> omega
  · have hp' : fkRectClosedPairingAtEdge e = false :=
      Bool.eq_false_of_not_eq_true hp
    simp [hp, hp']
    simp [fkRectRefinedDualEdgeDarts, hp, hp'] at ha
    rcases ha with rfl | rfl | rfl | rfl
    all_goals
      rcases r with ⟨x, y⟩
      simp [fkRectIntegralSquareDartTranslate,
        fkRectFaithfulShearDartRoute, fkRectFaithfulShearPair,
        fkRectIntegralSquareDartEnd,
        StatMech.Onsager.ons_dirExponentX,
        StatMech.Onsager.ons_dirExponentY] at hr ⊢ <;> omega


theorem fkRectRefinedDualEdgeReverseBlock_faithfulRoute_fst_between
    (R : FKRectTorus) (e : R.EdgeIndex) (t : Int × Int)
    (d : FKRectIntegralSquareDart) (r : Int × Int)
    (hd : d ∈ (fkRectIntegralSquareDartListReverse
      (fkRectRefinedDualEdgeDarts R e)).map
        (fkRectIntegralSquareDartTranslate t))
    (hr : r ∈ fkRectFaithfulShearDartRoute d) :
    min (fkRectFaithfulShearPair
          ((fkRectRefinedDualEdgeStart R e).1 + t.1,
            (fkRectRefinedDualEdgeStart R e).2 + t.2)).1
        (fkRectFaithfulShearPair
          ((fkRectRefinedDualEdgeEnd R e).1 + t.1,
            (fkRectRefinedDualEdgeEnd R e).2 + t.2)).1 ≤ r.1 ∧
      r.1 ≤
        max (fkRectFaithfulShearPair
          ((fkRectRefinedDualEdgeStart R e).1 + t.1,
            (fkRectRefinedDualEdgeStart R e).2 + t.2)).1
        (fkRectFaithfulShearPair
          ((fkRectRefinedDualEdgeEnd R e).1 + t.1,
            (fkRectRefinedDualEdgeEnd R e).2 + t.2)).1 := by
  rw [← fkRectIntegralSquareDartListReverse_translate] at hd
  unfold fkRectIntegralSquareDartListReverse at hd
  obtain ⟨a, ha, hda⟩ := List.mem_map.mp hd
  rw [List.mem_reverse] at ha
  have hr' : r ∈ fkRectFaithfulShearDartRoute a := by
    rw [← fkRectFaithfulShearDartRoute_reverse_iff a r]
    rw [hda]
    exact hr
  exact fkRectRefinedDualEdgeBlock_faithfulRoute_fst_between
    R e t a r ha hr'



theorem fkRectFaithfulShearPoint_add (p u : Int × Int) :
    fkRectFaithfulShearPoint (p.1 + u.1, p.2 + u.2) =
      ![(fkRectFaithfulShearPoint p) 0 + 2 * (u.1 + u.2),
        (fkRectFaithfulShearPoint p) 1 + 2 * (u.1 - u.2)] := by
  funext i
  fin_cases i <;> simp <;> ring



theorem fkRectFaithfulShearPoint_add_refinedDeck
    (R : FKRectTorus) (p u : Int × Int) :
    fkRectFaithfulShearPoint
        (p.1 + (fkRectRefinedDeckTranslation R u).1,
          p.2 + (fkRectRefinedDeckTranslation R u).2) =
      ![(fkRectFaithfulShearPoint p) 0 +
          16 * (R.width : Int) * u.1,
        (fkRectFaithfulShearPoint p) 1 +
          8 * (R.height : Int) * u.2] := by
  have hhNat : 2 * (R.height / 2) = R.height :=
    Nat.two_mul_div_two_of_even R.height_even
  have hh : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    exact_mod_cast hhNat
  rw [fkRectFaithfulShearPoint_add]
  funext i
  fin_cases i
  · simp [fkRectRefinedDeckTranslation,
      fkRectSquareDeckTranslation]
    ring
  · simp [fkRectRefinedDeckTranslation, fkRectSquareDeckTranslation]
    have hcast : ((R.height / 2 : Nat) : Int) =
        (R.height : Int) / (2 : Int) :=
      Int.natCast_ediv R.height 2
    rw [← hcast]
    linear_combination (8 * u.2) * hh



theorem FKRectSquareWalkLift.closed_faithfulRefined_end_of_verticalOne
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x : R.Vertex} {w : G.Walk x x} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q)
    (hw : fkRectWalkWinding R w = (0, 1)) :
    fkRectFaithfulShearPoint
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q)) =
      ![(fkRectFaithfulShearPoint
          (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 0,
        (fkRectFaithfulShearPoint
          (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 1 +
            8 * (R.height : Int)] := by
  have hend := h.closed_end_eq_period_winding R
  rw [hw] at hend
  have hq1 : q.1 = p.1 := by
    have := congrArg Prod.fst hend
    simpa using this
  have hq2 : q.2 = p.2 + (R.height : Int) := by
    have := congrArg Prod.snd hend
    simpa using this
  funext i
  fin_cases i
  · change
      (fkRectFaithfulShearPoint
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q))) 0 =
      (fkRectFaithfulShearPoint
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 0
    rw [fkRectFaithfulShearPoint_refinedScale_develop_fst,
      fkRectFaithfulShearPoint_refinedScale_develop_fst, hq1, hq2]
    obtain ⟨m, hm⟩ := R.height_even
    have hmInt : (R.height : Int) = (m : Int) + (m : Int) := by
      exact_mod_cast hm
    rw [hmInt]
    omega
  · change
      (fkRectFaithfulShearPoint
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q))) 1 =
      (fkRectFaithfulShearPoint
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 1 +
        8 * (R.height : Int)
    rw [fkRectFaithfulShearPoint_refinedScale_develop_snd,
      fkRectFaithfulShearPoint_refinedScale_develop_snd, hq2]
    ring

end

end StatMech.FrontierD
