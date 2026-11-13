/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectHorizontalCylinderExploration
import Code.FrontierD.FKFreeConnectionBoxEmbedding
import Code.FrontierD.FKRectTorusWindingEvent
import Code.FrontierD.FKRectFaithfulHorizontalExtension
import Code.FrontierD.FKRectFaithfulCarrierDisjoint
import Code.FrontierD.FKRectFaithfulShearCoordinates
import Code.FrontierD.FKRectFaithfulWalkVerticalBound
import Code.FrontierD.FKRectTorusDisjointWinding










open Finset SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

private theorem not_fkRectCrossesVerticalSeam_indexedEdge_of_not_horizontalCut
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∉ fkRectHorizontalCutEdges R) :
    ¬ fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a) := by
  rw [mem_fkRectHorizontalCutEdges_iff] at ha
  rcases a with ⟨b, x, y⟩
  change y.val ≠ 0 at ha
  have hh := R.height_gt_two
  have hylt := y.isLt
  intro hcross
  cases b
  · by_cases hy : Even y.val <;>
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
        hy, if_true, fkRectCrossesVerticalSeam_mk] at hcross
    all_goals rw [fkRectCyclicPred_val] at hcross
    all_goals split at hcross <;> omega
  · simp only [fkRectTorusIndexedEdge, if_true,
      fkRectCrossesVerticalSeam_mk] at hcross
    rw [fkRectCyclicPred_val] at hcross
    split at hcross <;> omega

private theorem fkRectCrossesVerticalSeam_indexedEdge_of_horizontalCut_planarization
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∈ fkRectHorizontalCutEdges R) :
    fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a) := by
  rw [mem_fkRectHorizontalCutEdges_iff] at ha
  rcases a with ⟨b, x, y⟩
  change y.val = 0 at ha
  have hlast : R.height - 1 + 1 = R.height := by omega
  cases b
  · by_cases hy : Even y.val <;>
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
        hy, if_true, fkRectCrossesVerticalSeam_mk]
    all_goals rw [fkRectCyclicPred_val]
    all_goals simp only [ha, if_true]
    all_goals exact Or.inl ⟨True.intro, hlast⟩
  · simp only [fkRectTorusIndexedEdge, if_true,
      fkRectCrossesVerticalSeam_mk]
    rw [fkRectCyclicPred_val]
    simp only [ha, if_true]
    exact Or.inl ⟨True.intro, hlast⟩



theorem fkRectHorizontalCylinderGraph_not_crossesVerticalSeam
    (R : FKRectTorus) {x y : R.Vertex}
    (hxy : (fkRectHorizontalCylinderGraph R).Adj x y) :
    ¬ fkRectCrossesVerticalSeam R s(x, y) := by
  obtain ⟨htorus, hcut⟩ :=
    (fkRectHorizontalCylinderGraph_adj_iff R x y).mp hxy
  obtain ⟨a, ha⟩ := htorus
  have hacut : a ∉ fkRectHorizontalCutEdges R := by
    intro hacut
    apply hcut
    rw [← ha]
    exact (mem_fkRectHorizontalCutGraphEdges R a).2 hacut
  rw [← ha]
  exact not_fkRectCrossesVerticalSeam_indexedEdge_of_not_horizontalCut
    R a hacut



theorem fkRectHorizontalCylinderWalk_winding_snd_eq_zero
    (R : FKRectTorus) {x y : R.Vertex}
    (p : (fkRectHorizontalCylinderGraph R).Walk x y) :
    (fkRectWalkWinding R p).2 = 0 := by
  induction p with
  | nil => rfl
  | @cons u v w huv p ih =>
      simp only [fkRectWalkWinding]
      rw [fkRectVerticalSeamIncrement_eq_zero_of_not_crosses R u v
        (fkRectHorizontalCylinderGraph_not_crossesVerticalSeam R huv),
        ih, zero_add]

private theorem fkRectFaithfulShearDartRoute_snd_between
    (d : FKRectIntegralSquareDart) (r : Int × Int)
    (hr : r ∈ fkRectFaithfulShearDartRoute d) :
    min ((fkRectFaithfulShearPoint d.1) 1)
          ((fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1) ≤
        (fkRectPairSite r) 1 ∧
      (fkRectPairSite r) 1 ≤
        max ((fkRectFaithfulShearPoint d.1) 1)
          ((fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  rcases r with ⟨a, b⟩
  fin_cases mu <;>
    simp [fkRectFaithfulShearDartRoute, fkRectFaithfulShearPoint,
      fkRectFaithfulShearPair, fkRectPairSite,
      fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] at hr ⊢ <;>
    omega

private theorem fkRectFaithfulShearDartRoute_bounds
    {lower upper : Int} (d : FKRectIntegralSquareDart)
    (hstart : lower ≤ (fkRectFaithfulShearPoint d.1) 1 ∧
      (fkRectFaithfulShearPoint d.1) 1 ≤ upper)
    (hend : lower ≤
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartEnd d)) 1 ∧
      (fkRectFaithfulShearPoint
        (fkRectIntegralSquareDartEnd d)) 1 ≤ upper)
    {z : StatMech.Lattice.Site 2} {r : Int × Int}
    (hr : r ∈ fkRectFaithfulShearDartRoute d)
    (hz : z = fkRectPairSite r) :
    lower ≤ z 1 ∧ z 1 ≤ upper := by
  subst z
  have hbetween := fkRectFaithfulShearDartRoute_snd_between d r hr
  constructor
  · exact le_trans (le_min hstart.1 hend.1) hbetween.1
  · exact le_trans hbetween.2 (max_le hstart.2 hend.2)

private theorem FKRectIntegralSquareDartPath.exists_faithfulShearWalk_bounds
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) (hl : l ≠ [])
    {lower upper : Int}
    (hbounds : ∀ d ∈ l,
      (lower ≤ (fkRectFaithfulShearPoint d.1) 1 ∧
        (fkRectFaithfulShearPoint d.1) 1 ≤ upper) ∧
      (lower ≤
          (fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1 ∧
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartEnd d)) 1 ≤ upper)) :
    ∃ V : (StatMech.Lattice.hypercubicLattice 2).Walk
        (fkRectFaithfulShearPoint p) (fkRectFaithfulShearPoint q),
      ∀ z ∈ V.support, lower ≤ z 1 ∧ z 1 ≤ upper := by
  obtain ⟨V, hV⟩ := h.exists_faithfulShearWalk_of_ne_nil hl
  refine ⟨V, ?_⟩
  intro z hz
  obtain ⟨d, hdl, r, hr, hz⟩ := hV z hz
  exact fkRectFaithfulShearDartRoute_bounds d
    (hbounds d hdl).1 (hbounds d hdl).2 hr hz

private theorem FKRectSquareWalkLift.end_snd_eq_val_of_cylinder
    (R : FKRectTorus) {x y : R.Vertex}
    {w : (fkRectHorizontalCylinderGraph R).Walk x y}
    {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q)
    (hpRow : p.2 = (x.2.val : Int)) :
    q.2 = (y.2.val : Int) := by
  induction h with
  | nil => exact hpRow
  | @cons a b c hab tail p q r hpa hqb hdisp haxis hlift ih =>
      have hno := fkRectHorizontalCylinderGraph_not_crossesVerticalSeam R hab
      have hinc : fkRectVerticalSeamIncrement R a b = 0 :=
        fkRectVerticalSeamIncrement_eq_zero_of_not_crosses R a b hno
      have hqRow : q.2 = (b.2.val : Int) := by
        have hsnd := congrArg Prod.snd hdisp
        simp only [Prod.snd_sub, fkRectDevelopedStep] at hsnd
        rw [hinc] at hsnd
        simp only [mul_zero, add_zero] at hsnd
        omega
      exact ih hqRow

private theorem FKRectSquareWalkLift.exists_cylinderSupportedIntegralDartPath
    (R : FKRectTorus) {x y : R.Vertex}
    {w : (fkRectHorizontalCylinderGraph R).Walk x y}
    {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q)
    (hpRow : p.2 = (x.2.val : Int)) :
    ∃ l : List FKRectIntegralSquareDart,
      FKRectIntegralSquareDartPath
        (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q) l ∧
      FKRectIntegralDartListSupportedOn R l (fun v => v ∈ w.support) ∧
      (∀ d ∈ l,
        (0 ≤ (fkRectFaithfulShearPoint d.1) 1 ∧
          (fkRectFaithfulShearPoint d.1) 1 ≤ 2 * (R.height - 1)) ∧
        (0 ≤
            (fkRectFaithfulShearPoint
              (fkRectIntegralSquareDartEnd d)) 1 ∧
          (fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1 ≤
              2 * (R.height - 1))) := by
  induction h with
  | nil p hp =>
      exact ⟨[], FKRectIntegralSquareDartPath.nil _,
        by simp [FKRectIntegralDartListSupportedOn],
        by simp⟩
  | @cons a b c hab tail p q r hpa hqb hdisp haxis hlift ih =>
      have hno := fkRectHorizontalCylinderGraph_not_crossesVerticalSeam R hab
      have hinc : fkRectVerticalSeamIncrement R a b = 0 :=
        fkRectVerticalSeamIncrement_eq_zero_of_not_crosses R a b hno
      have hqRow : q.2 = (b.2.val : Int) := by
        have hsnd := congrArg Prod.snd hdisp
        simp only [Prod.snd_sub, fkRectDevelopedStep] at hsnd
        rw [hinc] at hsnd
        simp only [mul_zero, add_zero] at hsnd
        omega
      obtain ⟨l, hlpath, hlsupp, hlbounds⟩ := ih hqRow
      obtain ⟨mu, hmu⟩ := haxis.exists_direction
      let d : FKRectIntegralSquareDart :=
        (fkRectSquareDevelopPoint p, mu)
      have hdend : fkRectIntegralSquareDartEnd d =
          fkRectSquareDevelopPoint q := by
        exact hmu
      refine ⟨d :: l,
        FKRectIntegralSquareDartPath.cons d hdend hlpath, ?_, ?_⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · constructor
          · rw [fkRectSquareRepresentativeVertex_developPoint, hpa]
            simp
          · rw [hdend, fkRectSquareRepresentativeVertex_developPoint, hqb]
            simp
        · obtain ⟨hstart, hend⟩ := hlsupp e he
          constructor <;>
            rw [SimpleGraph.Walk.support_cons] <;>
            exact List.mem_cons_of_mem a (by assumption)
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · have haLt := a.2.isLt
          have hbLt := b.2.isLt
          have hstartY :
              (fkRectFaithfulShearPoint
                (fkRectSquareDevelopPoint p)) 1 = 2 * p.2 := by
            rw [fkRectFaithfulShearPoint_apply_one]
            linear_combination 2 *
              (fkRectSquareDevelopPoint_fst_sub_snd p)
          have hendY :
              (fkRectFaithfulShearPoint
                (fkRectIntegralSquareDartEnd d)) 1 = 2 * q.2 := by
            rw [hdend, fkRectFaithfulShearPoint_apply_one]
            linear_combination 2 *
              (fkRectSquareDevelopPoint_fst_sub_snd q)
          rw [hstartY, hendY, hpRow, hqRow]
          constructor <;> constructor <;> omega
        · exact hlbounds e he

private theorem fkRectFaithfulShearPoint_translate_snd_of_eq
    (d u : Int × Int) (hu : u.1 = u.2) :
    (fkRectFaithfulShearPoint (d.1 + u.1, d.2 + u.2)) 1 =
      (fkRectFaithfulShearPoint d) 1 := by
  simp only [fkRectFaithfulShearPoint_apply_one]
  omega

private theorem fkRectFaithfulDartBounds_translate_of_eq
    {lower upper : Int} (u : Int × Int) (hu : u.1 = u.2)
    (d : FKRectIntegralSquareDart)
    (h : (lower ≤ (fkRectFaithfulShearPoint d.1) 1 ∧
        (fkRectFaithfulShearPoint d.1) 1 ≤ upper) ∧
      (lower ≤
          (fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1 ∧
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartEnd d)) 1 ≤ upper)) :
    (lower ≤
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartTranslate u d).1) 1 ∧
      (fkRectFaithfulShearPoint
        (fkRectIntegralSquareDartTranslate u d).1) 1 ≤ upper) ∧
    (lower ≤
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartEnd
            (fkRectIntegralSquareDartTranslate u d))) 1 ∧
      (fkRectFaithfulShearPoint
        (fkRectIntegralSquareDartEnd
          (fkRectIntegralSquareDartTranslate u d))) 1 ≤ upper) := by
  have hstart := fkRectFaithfulShearPoint_translate_snd_of_eq d.1 u hu
  have hend := fkRectFaithfulShearPoint_translate_snd_of_eq
    (fkRectIntegralSquareDartEnd d) u hu
  rw [fkRectIntegralSquareDartEnd_translate]
  simpa [fkRectIntegralSquareDartTranslate, hstart, hend] using h

private theorem fkRectRepeatTranslatedDartPath_faithfulBounds
    {lower upper : Int} (l : List FKRectIntegralSquareDart)
    (u : Int × Int) (hu : u.1 = u.2)
    (hl : ∀ d ∈ l,
      (lower ≤ (fkRectFaithfulShearPoint d.1) 1 ∧
        (fkRectFaithfulShearPoint d.1) 1 ≤ upper) ∧
      (lower ≤
          (fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1 ∧
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartEnd d)) 1 ≤ upper)) :
    ∀ n d, d ∈ fkRectRepeatTranslatedDartPath l u n →
      (lower ≤ (fkRectFaithfulShearPoint d.1) 1 ∧
        (fkRectFaithfulShearPoint d.1) 1 ≤ upper) ∧
      (lower ≤
          (fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1 ∧
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartEnd d)) 1 ≤ upper) := by
  intro n
  induction n with
  | zero => simp [fkRectRepeatTranslatedDartPath]
  | succ n ih =>
      intro d hd
      rw [fkRectRepeatTranslatedDartPath, List.mem_append] at hd
      rcases hd with hd | hd
      · exact ih d hd
      · obtain ⟨e, hel, rfl⟩ := List.mem_map.mp hd
        apply fkRectFaithfulDartBounds_translate_of_eq
          (fkRectNatScale n u)
        · simp [fkRectNatScale, hu]
        · exact hl e hel

private theorem FKRectIntegralDartListSupportedOn.translate_deck
    (R : FKRectTorus) {l : List FKRectIntegralSquareDart}
    {S : R.Vertex → Prop}
    (h : FKRectIntegralDartListSupportedOn R l S) (u : Int × Int) :
    FKRectIntegralDartListSupportedOn R
      (l.map (fkRectIntegralSquareDartTranslate
        (fkRectSquareDeckTranslation R u))) S := by
  intro d hd
  obtain ⟨e, hel, rfl⟩ := List.mem_map.mp hd
  constructor
  · rw [fkRectSquareRepresentativeVertex_dartTranslate_deck]
    exact (h e hel).1
  · rw [fkRectSquareRepresentativeVertex_dartTranslateEnd_deck]
    exact (h e hel).2

private theorem FKRectIntegralDartListSupportedOn.common_of_incident
    (R : FKRectTorus) {l k : List FKRectIntegralSquareDart}
    {S T : R.Vertex → Prop}
    (hl : FKRectIntegralDartListSupportedOn R l S)
    (hk : FKRectIntegralDartListSupportedOn R k T)
    {d e : FKRectIntegralSquareDart} (hdl : d ∈ l) (hek : e ∈ k)
    (hde : FKRectIntegralSquareDartsIncident d e) :
    ∃ v, S v ∧ T v := by
  rcases hde with h | h | h | h
  · exact ⟨fkRectSquareRepresentativeVertex R d.1,
      (hl d hdl).1, h ▸ (hk e hek).1⟩
  · exact ⟨fkRectSquareRepresentativeVertex R d.1,
      (hl d hdl).1, h ▸ (hk e hek).2⟩
  · exact ⟨fkRectSquareRepresentativeVertex R
        (fkRectIntegralSquareDartEnd d),
      (hl d hdl).2, h ▸ (hk e hek).1⟩
  · exact ⟨fkRectSquareRepresentativeVertex R
        (fkRectIntegralSquareDartEnd d),
      (hl d hdl).2, h ▸ (hk e hek).2⟩

private theorem exists_fkRectFaithfulWalk_horizontal_natAbs_bound
    {x y : StatMech.Lattice.Site 2}
    (W : (StatMech.Lattice.hypercubicLattice 2).Walk x y) :
    ∃ M : Nat, ∀ z ∈ W.support,
      -(M : Int) ≤ z 0 ∧ z 0 ≤ (M : Int) := by
  let swap : StatMech.Lattice.Site 2 → StatMech.Lattice.Site 2 :=
    fun z => ![z 1, z 0]
  have hswap : ∀ {a b},
      (StatMech.Lattice.hypercubicLattice 2).Adj a b →
        (StatMech.Lattice.hypercubicLattice 2).Adj (swap a) (swap b) := by
    intro a b hab
    rw [StatMech.Lattice.hypercubicLattice_adj,
      Fin.sum_univ_two] at hab ⊢
    simp [swap]
    omega
  let f : StatMech.Lattice.hypercubicLattice 2 →g
      StatMech.Lattice.hypercubicLattice 2 := ⟨swap, hswap⟩
  obtain ⟨M, hM⟩ :=
    exists_fkRectFaithfulWalk_vertical_natAbs_bound (W.map f)
  refine ⟨M, ?_⟩
  intro z hz
  have hzmap : swap z ∈ (W.map f).support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨z, hz, rfl⟩
  simpa [swap] using hM (swap z) hzmap

private theorem fkRectHorizontalCylinder_support_intersects_bottomTop_of_pos
    (R : FKRectTorus) (bottomX topX : Fin R.width)
    (V : (fkRectHorizontalCylinderGraph R).Walk
      (bottomX, fkRectBottomRow R) (topX, fkRectTopRow R))
    {x : R.Vertex}
    (W : (fkRectHorizontalCylinderGraph R).Walk x x)
    (hwind : 0 < (fkRectWalkWinding R W).1) :
    ∃ v, v ∈ W.support ∧ v ∈ V.support := by
  let hsub : fkRectHorizontalCylinderGraph R ≤ fkRectTorusGraph R := by
    intro a b hab
    exact (fkRectHorizontalCylinderGraph_adj_iff R a b).mp hab |>.1
  let pv : Int × Int := ((bottomX.val : Int), 0)
  let pw : Int × Int := ((x.1.val : Int), (x.2.val : Int))
  have hpv : fkRectLiftedVertex R pv =
      (bottomX, fkRectBottomRow R) := by
    apply Prod.ext
    · simp [pv, fkRectLiftedVertex]
    · change fkRectIntModFin R.height_pos 0 = fkRectBottomRow R
      rw [show (0 : Int) = ((fkRectBottomRow R).val : Int) by
        simp [fkRectBottomRow]]
      exact fkRectIntModFin_natCast R.height_pos _
  have hpw : fkRectLiftedVertex R pw = x := by
    apply Prod.ext <;> simp [pw, fkRectLiftedVertex]
  obtain ⟨qv, hVlift⟩ :=
    fkRectWalk_exists_squareLift R hsub V pv hpv
  obtain ⟨qw, hWlift⟩ :=
    fkRectWalk_exists_squareLift R hsub W pw hpw
  have hpvRow : pv.2 =
      (((bottomX, fkRectBottomRow R) : R.Vertex).2.val : Int) := by
    simp [pv, fkRectBottomRow]
  have hpwRow : pw.2 = (x.2.val : Int) := by rfl
  have hqvRow : qv.2 =
      (((topX, fkRectTopRow R) : R.Vertex).2.val : Int) :=
    hVlift.end_snd_eq_val_of_cylinder R hpvRow
  have hqwRow : qw.2 = (x.2.val : Int) :=
    hWlift.end_snd_eq_val_of_cylinder R hpwRow
  obtain ⟨lv, hLvPath, hLvSupp, hLvBounds⟩ :=
    hVlift.exists_cylinderSupportedIntegralDartPath R hpvRow
  obtain ⟨lw, hLwPath, hLwSupp, hLwBounds⟩ :=
    hWlift.exists_cylinderSupportedIntegralDartPath R hpwRow
  have hpvqv : fkRectSquareDevelopPoint pv ≠
      fkRectSquareDevelopPoint qv := by
    intro heq
    have hpq : pv = qv := fkRectSquareDevelopPoint_injective heq
    have hh := R.height_gt_two
    have hsnd := congrArg Prod.snd hpq
    rw [hpvRow, hqvRow] at hsnd
    simp [fkRectBottomRow, fkRectTopRow] at hsnd
    omega
  have hlv : lv ≠ [] := hLvPath.ne_nil_of_ne hpvqv
  obtain ⟨Vfaithful, hVfaithful⟩ :=
    hLvPath.exists_faithfulShearWalk_of_ne_nil hlv
  let H : Int := 2 * (R.height - 1)
  have hVvertical : ∀ z ∈ Vfaithful.support,
      0 ≤ z 1 ∧ z 1 ≤ H := by
    intro z hz
    obtain ⟨d, hdl, r, hr, hz⟩ := hVfaithful z hz
    exact fkRectFaithfulShearDartRoute_bounds d
      (hLvBounds d hdl).1 (hLvBounds d hdl).2 hr hz
  obtain ⟨B, hVB⟩ :=
    exists_fkRectFaithfulWalk_horizontal_natAbs_bound Vfaithful
  let wind := fkRectWalkWinding R W
  have hwindSnd : wind.2 = 0 := by
    exact fkRectHorizontalCylinderWalk_winding_snd_eq_zero R W
  let u := fkRectSquareDeckTranslation R wind
  have huEq : u.1 = u.2 := by
    simp [u, wind, fkRectSquareDeckTranslation, hwindSnd]
  have hqwDevelop : fkRectSquareDevelopPoint qw =
      ((fkRectSquareDevelopPoint pw).1 + u.1,
        (fkRectSquareDevelopPoint pw).2 + u.2) := by
    have h := hWlift.closed_develop_sub_eq_deck_winding R
    apply Prod.ext
    · have hx := congrArg Prod.fst h
      simp only [Prod.fst_sub] at hx ⊢
      dsimp [u, wind]
      omega
    · have hy := congrArg Prod.snd h
      simp only [Prod.snd_sub] at hy ⊢
      dsimp [u, wind]
      omega
  have hpwqw : fkRectSquareDevelopPoint pw ≠
      fkRectSquareDevelopPoint qw := by
    intro heq
    have hx := congrArg (fun z : Int × Int => z.1) heq
    rw [hqwDevelop] at hx
    have huPos : 0 < u.1 := by
      have hwpos : (0 : Int) < R.width := by
        exact_mod_cast R.width_pos
      simpa [u, wind, fkRectSquareDeckTranslation, hwindSnd] using
        mul_pos hwpos hwind
    change (fkRectSquareDevelopPoint pw).1 =
      (fkRectSquareDevelopPoint pw).1 + u.1 at hx
    omega
  have hlw : lw ≠ [] := hLwPath.ne_nil_of_ne hpwqw
  let X : Int := (fkRectFaithfulShearPoint
    (fkRectSquareDevelopPoint pw)) 0
  let m : Nat := B + X.natAbs + 1
  let shiftWind : Int × Int :=
    (-((m : Int) * wind.1), 0)
  let shift := fkRectSquareDeckTranslation R shiftWind
  let ps : Int × Int :=
    ((fkRectSquareDevelopPoint pw).1 + shift.1,
      (fkRectSquareDevelopPoint pw).2 + shift.2)
  let lshift := lw.map (fkRectIntegralSquareDartTranslate shift)
  have hShiftPath : FKRectIntegralSquareDartPath ps
      (ps.1 + u.1, ps.2 + u.2) lshift := by
    rw [hqwDevelop] at hLwPath
    have ht := hLwPath.translate shift
    have hend :
        (((fkRectSquareDevelopPoint pw).1 + u.1 + shift.1,
            (fkRectSquareDevelopPoint pw).2 + u.2 + shift.2)) =
          (ps.1 + u.1, ps.2 + u.2) := by
      apply Prod.ext <;> simp [ps] <;> ring
    rw [hend] at ht
    exact ht
  have hShiftSupp : FKRectIntegralDartListSupportedOn R lshift
      (fun v => v ∈ W.support) := by
    simpa [lshift, shift] using hLwSupp.translate_deck R shiftWind
  have hShiftBounds : ∀ d ∈ lshift,
      (0 ≤ (fkRectFaithfulShearPoint d.1) 1 ∧
        (fkRectFaithfulShearPoint d.1) 1 ≤ H) ∧
      (0 ≤
          (fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1 ∧
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartEnd d)) 1 ≤ H) := by
    intro d hd
    obtain ⟨e, hel, rfl⟩ := List.mem_map.mp hd
    apply fkRectFaithfulDartBounds_translate_of_eq shift
    · simp [shift, shiftWind, fkRectSquareDeckTranslation]
    · exact hLwBounds e hel
  let n : Nat := 2 * m
  let lrep := fkRectRepeatTranslatedDartPath lshift u n
  have hRepPath : FKRectIntegralSquareDartPath ps
      (ps.1 + (n : Int) * u.1, ps.2 + (n : Int) * u.2) lrep := by
    exact hShiftPath.repeatTranslated n
  have hRepSupp : FKRectIntegralDartListSupportedOn R lrep
      (fun v => v ∈ W.support) := by
    have h := hShiftSupp.repeatTranslated_deck R wind n
    simpa [lrep, u] using h
  have hRepBounds : ∀ d ∈ lrep,
      (0 ≤ (fkRectFaithfulShearPoint d.1) 1 ∧
        (fkRectFaithfulShearPoint d.1) 1 ≤ H) ∧
      (0 ≤
          (fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1 ∧
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartEnd d)) 1 ≤ H) := by
    exact fkRectRepeatTranslatedDartPath_faithfulBounds
      lshift u huEq hShiftBounds n
  have hmp : 0 < m := by simp [m]
  have hnp : 0 < n := by simp [n, hmp]
  have huPos : 0 < u.1 := by
    have hwpos : (0 : Int) < R.width := by
      exact_mod_cast R.width_pos
    simpa [u, wind, fkRectSquareDeckTranslation, hwindSnd] using
      mul_pos hwpos hwind
  have hRepEndpoints : ps ≠
      (ps.1 + (n : Int) * u.1, ps.2 + (n : Int) * u.2) := by
    intro heq
    have hx := congrArg Prod.fst heq
    change ps.1 = ps.1 + (n : Int) * u.1 at hx
    have hnInt : (0 : Int) < n := by exact_mod_cast hnp
    nlinarith
  have hlrep : lrep ≠ [] := hRepPath.ne_nil_of_ne hRepEndpoints
  obtain ⟨Wfaithful, hWfaithful⟩ :=
    hRepPath.exists_faithfulShearWalk_of_ne_nil hlrep
  have hWvertical : ∀ z ∈ Wfaithful.support,
      0 ≤ z 1 ∧ z 1 ≤ H := by
    intro z hz
    obtain ⟨d, hdl, r, hr, hz⟩ := hWfaithful z hz
    exact fkRectFaithfulShearDartRoute_bounds d
      (hRepBounds d hdl).1 (hRepBounds d hdl).2 hr hz
  have hshiftEq : shift =
      (-((m : Int) * u.1), -((m : Int) * u.2)) := by
    apply Prod.ext <;>
      simp [shift, shiftWind, u, wind, fkRectSquareDeckTranslation,
        hwindSnd] <;>
      ring
  have hWstart : (fkRectFaithfulShearPoint ps) 0 ≤ -(B : Int) := by
    have hX : -(X.natAbs : Int) ≤ X := by
      rw [Int.natCast_natAbs]
      exact neg_abs_le X
    have huOne : 1 ≤ 2 * (u.1 + u.2) := by
      rw [huEq]
      omega
    have hmInt : (m : Int) = B + X.natAbs + 1 := by
      simp [m]
    have hcoord : (fkRectFaithfulShearPoint ps) 0 =
        X - (m : Int) * (2 * (u.1 + u.2)) := by
      rw [fkRectFaithfulShearPoint_apply_zero]
      dsimp [ps]
      rw [hshiftEq]
      dsimp [X]
      rw [fkRectFaithfulShearPoint_apply_zero]
      ring
    rw [hcoord]
    have hmul := mul_le_mul_of_nonneg_left huOne
      (show (0 : Int) ≤ m by positivity)
    omega
  have hWend : (B : Int) ≤
      (fkRectFaithfulShearPoint
        (ps.1 + (n : Int) * u.1,
          ps.2 + (n : Int) * u.2)) 0 := by
    have hX : X ≤ (X.natAbs : Int) := by
      rw [Int.natCast_natAbs]
      exact le_abs_self X
    have huOne : 1 ≤ 2 * (u.1 + u.2) := by
      rw [huEq]
      omega
    have hmInt : (m : Int) = B + X.natAbs + 1 := by
      simp [m]
    have hcoord :
        (fkRectFaithfulShearPoint
          (ps.1 + (n : Int) * u.1,
            ps.2 + (n : Int) * u.2)) 0 =
          X + (m : Int) * (2 * (u.1 + u.2)) := by
      rw [fkRectFaithfulShearPoint_apply_zero]
      dsimp [ps, n]
      rw [hshiftEq]
      dsimp [X]
      rw [fkRectFaithfulShearPoint_apply_zero]
      ring
    rw [hcoord]
    have hmul := mul_le_mul_of_nonneg_left huOne
      (show (0 : Int) ≤ m by positivity)
    omega
  obtain ⟨M, hWM⟩ :=
    exists_fkRectFaithfulWalk_horizontal_natAbs_bound Wfaithful
  let K : Nat := max B M + 1
  let alpha : Int := -(K : Int)
  let beta : Int := K
  have hKpos : (0 : Int) < K := by simp [K]
  have hBK : (B : Int) ≤ K := by
    exact_mod_cast (Nat.le_trans (Nat.le_max_left B M) (Nat.le_add_right _ _))
  have hMK : (M : Int) ≤ K := by
    exact_mod_cast (Nat.le_trans (Nat.le_max_right B M) (Nat.le_add_right _ _))
  have hVrect : ∀ z ∈ Vfaithful.support,
      z ∈ rect alpha beta 0 H := by
    intro z hz
    rw [mem_rect]
    have hx := hVB z hz
    have hy := hVvertical z hz
    dsimp [alpha, beta]
    omega
  have hWrect : ∀ z ∈ Wfaithful.support,
      z ∈ rect alpha beta 0 H := by
    intro z hz
    rw [mem_rect]
    have hx := hWM z hz
    have hy := hWvertical z hz
    dsimp [alpha, beta]
    omega
  have hpvY :
      (fkRectFaithfulShearPoint (fkRectSquareDevelopPoint pv)) 1 = 0 := by
    rw [fkRectFaithfulShearPoint_apply_one]
    have h := fkRectSquareDevelopPoint_fst_sub_snd pv
    simp [pv] at h ⊢
    omega
  have hqvY :
      (fkRectFaithfulShearPoint (fkRectSquareDevelopPoint qv)) 1 = H := by
    rw [fkRectFaithfulShearPoint_apply_one]
    have h := fkRectSquareDevelopPoint_fst_sub_snd qv
    simp [fkRectTopRow] at hqvRow
    dsimp [H]
    omega
  let Vcross : (hypercubicLattice 2).Walk
      ![(fkRectFaithfulShearPoint
          (fkRectSquareDevelopPoint pv)) 0, 0]
      ![(fkRectFaithfulShearPoint
          (fkRectSquareDevelopPoint qv)) 0, H] :=
    Vfaithful.copy (by
      funext i
      fin_cases i <;> simp [hpvY]) (by
      funext i
      fin_cases i <;> simp [hqvY])
  have hVcrossRect : ∀ z ∈ Vcross.support,
      z ∈ rect alpha beta 0 H := by
    intro z hz
    apply hVrect z
    simpa [Vcross] using hz
  have hfaithfulIntersection : ∃ z,
      z ∈ Wfaithful.support ∧ z ∈ Vfaithful.support := by
    by_contra hnone
    push Not at hnone
    let Wcross := fkRectFaithfulHorizontalExtension alpha beta Wfaithful
    have hWcrossRect : ∀ z ∈ Wcross.support,
        z ∈ rect alpha beta 0 H := by
      apply fkRectFaithfulHorizontalExtension_support_rect
        alpha beta 0 H Wfaithful
      · have := hWM (fkRectFaithfulShearPoint ps)
          Wfaithful.start_mem_support
        dsimp [alpha]
        omega
      · have := hWM
          (fkRectFaithfulShearPoint
            (ps.1 + (n : Int) * u.1,
              ps.2 + (n : Int) * u.2))
          Wfaithful.end_mem_support
        dsimp [beta]
        omega
      · exact hWrect
    have hWcrossDisjoint : ∀ z, z ∈ Wcross.support →
        z ∈ Vfaithful.support → False := by
      apply fkRectFaithfulHorizontalExtension_support_disjoint_of_core_bounds
        alpha beta (-(B : Int)) (B : Int) Wfaithful Vfaithful
      · have := hWM (fkRectFaithfulShearPoint ps)
          Wfaithful.start_mem_support
        dsimp [alpha]
        omega
      · exact hWstart
      · exact hWend
      · have := hWM
          (fkRectFaithfulShearPoint
            (ps.1 + (n : Int) * u.1,
              ps.2 + (n : Int) * u.2))
          Wfaithful.end_mem_support
        dsimp [beta]
        omega
      · exact hVB
      · exact fun z hzW hzV => hnone z hzW hzV
    have hWstartRect := hWcrossRect
      ![alpha, (fkRectFaithfulShearPoint ps) 1]
      Wcross.start_mem_support
    have hWendRect := hWcrossRect
      ![beta,
        (fkRectFaithfulShearPoint
          (ps.1 + (n : Int) * u.1,
            ps.2 + (n : Int) * u.2)) 1]
      Wcross.end_mem_support
    obtain ⟨z, hzW, hzV⟩ :=
      fkRectFaithful_bottomTop_leftRight_support_intersects
        alpha beta 0 H
        ((fkRectFaithfulShearPoint
          (fkRectSquareDevelopPoint pv)) 0)
        ((fkRectFaithfulShearPoint
          (fkRectSquareDevelopPoint qv)) 0)
        (by dsimp [alpha, beta]; omega) (by dsimp [H]; omega)
        (by have := hVB
              (fkRectFaithfulShearPoint (fkRectSquareDevelopPoint pv))
              Vfaithful.start_mem_support
            dsimp [alpha, beta] at *; omega)
        (by have := hVB
              (fkRectFaithfulShearPoint (fkRectSquareDevelopPoint pv))
              Vfaithful.start_mem_support
            dsimp [alpha, beta] at *; omega)
        (by have := hVB
              (fkRectFaithfulShearPoint (fkRectSquareDevelopPoint qv))
              Vfaithful.end_mem_support
            dsimp [alpha, beta] at *; omega)
        (by have := hVB
              (fkRectFaithfulShearPoint (fkRectSquareDevelopPoint qv))
              Vfaithful.end_mem_support
            dsimp [alpha, beta] at *; omega)
        Vcross hVcrossRect hWstartRect hWendRect
        rfl rfl Wcross hWcrossRect
    apply hWcrossDisjoint z hzW
    simpa [Vcross] using hzV
  obtain ⟨z, hzW, hzV⟩ := hfaithfulIntersection
  obtain ⟨d, hdl, rd, hrd, hzd⟩ := hWfaithful z hzW
  obtain ⟨e, hel, re, hre, hze⟩ := hVfaithful z hzV
  have hde : FKRectIntegralSquareDartsIncident d e :=
    fkRectIntegralSquareDartsIncident_of_faithfulRouteSite
      d e rd re hrd hre (hzd.symm.trans hze)
  exact hRepSupp.common_of_incident R hLvSupp hdl hel hde



theorem fkRectHorizontalCylinder_support_intersects_bottomTop
    (R : FKRectTorus) (bottomX topX : Fin R.width)
    (V : (fkRectHorizontalCylinderGraph R).Walk
      (bottomX, fkRectBottomRow R) (topX, fkRectTopRow R))
    {x : R.Vertex}
    (W : (fkRectHorizontalCylinderGraph R).Walk x x)
    (hwind : (fkRectWalkWinding R W).1 ≠ 0) :
    ∃ v, v ∈ W.support ∧ v ∈ V.support := by
  rcases lt_or_gt_of_ne hwind with hneg | hpos
  · obtain ⟨v, hvW, hvV⟩ :=
      fkRectHorizontalCylinder_support_intersects_bottomTop_of_pos
        R bottomX topX V W.reverse (by
          rw [fkRectWalkWinding_reverse]
          omega)
    exact ⟨v, by simpa using hvW, hvV⟩
  · exact fkRectHorizontalCylinder_support_intersects_bottomTop_of_pos
      R bottomX topX V W hpos


def fkRectHorizontalCylinderUnexploredInclusion
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) :
    FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
        (fkRectHorizontalCylinderBottomRoots R S) →g
      fkRectHorizontalCylinderGraph R where
  toFun := Subtype.val
  map_rel' := fun h => h



def fkRectHorizontalCylinderUnexploredWalkWinding
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) {x y}
    (p : (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Walk x y) : Int × Int :=
  fkRectWalkWinding R
    (p.map (fkRectHorizontalCylinderUnexploredInclusion R rho S))



def FKRectHorizontalCylinderUnexploredNoHorizontalWinding
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) : Prop :=
  ∀ (x : FKRectHorizontalCylinderUnexploredVertex R rho S)
    (p : (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Walk x x),
    (fkRectHorizontalCylinderUnexploredWalkWinding R rho S p).1 = 0



def FKRectHorizontalCylinderCrosscutSeparatesHorizontalWinding
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) : Prop :=
  ∀ {x : R.Vertex} (p : (fkRectHorizontalCylinderGraph R).Walk x x),
    (fkRectWalkWinding R p).1 ≠ 0 →
      ∃ v ∈ p.support,
        FKRectHorizontalCylinderExploredVertex R rho S v




theorem fkRectHorizontalCylinder_crosscutSeparates_of_crossingRoot
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) {bottomX : Fin R.width}
    (hbottomS : bottomX ∈ S)
    (hcross : FKRectHorizontalCylinderCrossingSource R rho bottomX) :
    FKRectHorizontalCylinderCrosscutSeparatesHorizontalWinding R rho S := by
  obtain ⟨topX, hreach⟩ := hcross
  obtain ⟨Vopen⟩ := hreach
  let inclusion : FK.openSub (fkRectHorizontalCylinderGraph R) rho →g
      fkRectHorizontalCylinderGraph R :=
    { toFun := id
      map_rel' := by
        intro a b h
        exact (FK.openSub_le (fkRectHorizontalCylinderGraph R) rho) h }
  let V := Vopen.map inclusion
  intro x p hwind
  obtain ⟨v, hvp, hvV⟩ :=
    fkRectHorizontalCylinder_support_intersects_bottomTop
      R bottomX topX V p hwind
  refine ⟨v, hvp, ?_⟩
  rw [fkRectHorizontalCylinderExploredVertex_iff]
  refine ⟨bottomX, hbottomS, ?_⟩
  have hvOpen : v ∈ Vopen.support := by
    change v ∈ (Vopen.map inclusion).support at hvV
    rw [SimpleGraph.Walk.support_map] at hvV
    obtain ⟨z, hz, hzv⟩ := List.mem_map.mp hvV
    simpa [inclusion] using hzv ▸ hz
  exact (Vopen.takeUntil v hvOpen).reachable



theorem fkRectHorizontalCylinder_crosscutSeparates_of_pairedWitness
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (pair : Fin R.width → Fin R.width) (S : Finset (Fin R.width))
    (hS : S.Nonempty)
    (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair S rho) :
    FKRectHorizontalCylinderCrosscutSeparatesHorizontalWinding R rho S := by
  obtain ⟨x, hx⟩ := hS
  apply fkRectHorizontalCylinder_crosscutSeparates_of_crossingRoot
    R rho S hx
  exact ⟨pair x, hW.1 x hx⟩

theorem fkRectHorizontalCylinderUnexploredWalk_winding_snd_eq_zero
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) {x y}
    (p : (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Walk x y) :
    (fkRectHorizontalCylinderUnexploredWalkWinding R rho S p).2 = 0 := by
  exact fkRectHorizontalCylinderWalk_winding_snd_eq_zero R
    (p.map (fkRectHorizontalCylinderUnexploredInclusion R rho S))



theorem fkRectHorizontalCylinder_noHorizontalWinding_of_crosscutSeparation
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (hsep : FKRectHorizontalCylinderCrosscutSeparatesHorizontalWinding
      R rho S) :
    FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S := by
  intro x p
  by_contra hwind
  obtain ⟨v, hvp, hvExplored⟩ := hsep
    (p.map (fkRectHorizontalCylinderUnexploredInclusion R rho S)) hwind
  rw [SimpleGraph.Walk.support_map] at hvp
  obtain ⟨v', hv'p, hv'v⟩ := List.mem_map.mp hvp
  have hvUnexplored :
      ¬ FKRectHorizontalCylinderExploredVertex R rho S v'.1 := v'.2
  apply hvUnexplored
  have hvEq : v'.1 = v := by
    simpa [fkRectHorizontalCylinderUnexploredInclusion] using hv'v
  exact hvEq.symm ▸ hvExplored



theorem fkRectHorizontalCylinder_noHorizontalWinding_of_pairedWitness
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (pair : Fin R.width → Fin R.width) (S : Finset (Fin R.width))
    (hS : S.Nonempty)
    (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair S rho) :
    FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S := by
  apply fkRectHorizontalCylinder_noHorizontalWinding_of_crosscutSeparation
  exact fkRectHorizontalCylinder_crosscutSeparates_of_pairedWitness
    R rho pair S hS hW

private theorem fkRectWalkDevelopedDisplacement_append
    (R : FKRectTorus) {G : SimpleGraph R.Vertex} {x y z : R.Vertex}
    (p : G.Walk x y) (q : G.Walk y z) :
    fkRectWalkDevelopedDisplacement R (p.append q) =
      fkRectWalkDevelopedDisplacement R p +
        fkRectWalkDevelopedDisplacement R q := by
  induction p with
  | nil => simp [fkRectWalkDevelopedDisplacement]
  | @cons a b c hab p ih =>
      simp only [SimpleGraph.Walk.cons_append,
        fkRectWalkDevelopedDisplacement]
      rw [ih]
      apply Prod.ext <;> simp <;> ring

private theorem fkRectWalkDevelopedDisplacement_reverse
    (R : FKRectTorus) {G : SimpleGraph R.Vertex} {x y : R.Vertex}
    (p : G.Walk x y) :
    fkRectWalkDevelopedDisplacement R p.reverse =
      -fkRectWalkDevelopedDisplacement R p := by
  induction p with
  | nil => simp [fkRectWalkDevelopedDisplacement]
  | @cons a b c hab p ih =>
      rw [SimpleGraph.Walk.reverse_cons,
        fkRectWalkDevelopedDisplacement_append, ih]
      simp only [fkRectWalkDevelopedDisplacement, neg_add_rev]
      rw [fkRectDevelopedStep_swap]
      simp

private theorem fkRectWalkDevelopedDisplacement_copy
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y x' y' : R.Vertex} (p : G.Walk x y)
    (hx : x = x') (hy : y = y') :
    fkRectWalkDevelopedDisplacement R (p.copy hx hy) =
      fkRectWalkDevelopedDisplacement R p := by
  subst x'
  subst y'
  rfl



noncomputable def fkRectHorizontalCylinderUnexploredComponentRoot
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S) :
    FKRectHorizontalCylinderUnexploredVertex R rho S :=
  Quot.out
    ((FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).connectedComponentMk x)

theorem fkRectHorizontalCylinderUnexploredComponentRoot_component
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S) :
    (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
        (fkRectHorizontalCylinderBottomRoots R S)).connectedComponentMk
      (fkRectHorizontalCylinderUnexploredComponentRoot R rho S x) =
    (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
        (fkRectHorizontalCylinderBottomRoots R S)).connectedComponentMk x := by
  exact Quot.out_eq _



noncomputable def fkRectHorizontalCylinderUnexploredRootWalk
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S) :
    (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Walk
        (fkRectHorizontalCylinderUnexploredComponentRoot R rho S x) x :=
  Classical.choice (SimpleGraph.ConnectedComponent.exact
    (fkRectHorizontalCylinderUnexploredComponentRoot_component R rho S x))



noncomputable def fkRectHorizontalCylinderUnexploredLiftPoint
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S) : Int × Int :=
  let root := fkRectHorizontalCylinderUnexploredComponentRoot R rho S x
  let p : Int × Int := ((root.1.1.val : Int), (root.1.2.val : Int))
  p + fkRectWalkDevelopedDisplacement R
    ((fkRectHorizontalCylinderUnexploredRootWalk R rho S x).map
      (fkRectHorizontalCylinderUnexploredInclusion R rho S))

theorem fkRectHorizontalCylinderUnexploredLiftPoint_project
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S) :
    fkRectLiftedVertex R
      (fkRectHorizontalCylinderUnexploredLiftPoint R rho S x) = x.1 := by
  let root := fkRectHorizontalCylinderUnexploredComponentRoot R rho S x
  let p : Int × Int := ((root.1.1.val : Int), (root.1.2.val : Int))
  let w := (fkRectHorizontalCylinderUnexploredRootWalk R rho S x).map
    (fkRectHorizontalCylinderUnexploredInclusion R rho S)
  have hp : fkRectLiftedVertex R p = root.1 := by
    apply Prod.ext <;> simp [p, fkRectLiftedVertex]
  have hsub : fkRectHorizontalCylinderGraph R ≤ fkRectTorusGraph R := by
    intro a b hab
    exact (fkRectHorizontalCylinderGraph_adj_iff R a b).mp hab |>.1
  obtain ⟨q, hq⟩ := fkRectWalk_exists_squareLift R hsub w p hp
  have hdisp := hq.sub_eq_developedDisplacement R
  have hqEq : q = p + fkRectWalkDevelopedDisplacement R w := by
    apply Prod.ext
    · have h := congrArg Prod.fst hdisp
      simp only [Prod.fst_sub, Prod.fst_add] at h ⊢
      omega
    · have h := congrArg Prod.snd hdisp
      simp only [Prod.snd_sub, Prod.snd_add] at h ⊢
      omega
  change fkRectLiftedVertex R
      (p + fkRectWalkDevelopedDisplacement R w) = x.1
  rw [← hqEq]
  exact hq.end_project R

theorem fkRectHorizontalCylinderUnexploredLiftPoint_snd_eq_val
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S) :
    (fkRectHorizontalCylinderUnexploredLiftPoint R rho S x).2 =
      (x.1.2.val : Int) := by
  let root := fkRectHorizontalCylinderUnexploredComponentRoot R rho S x
  let p : Int × Int := ((root.1.1.val : Int), (root.1.2.val : Int))
  let w := (fkRectHorizontalCylinderUnexploredRootWalk R rho S x).map
    (fkRectHorizontalCylinderUnexploredInclusion R rho S)
  have hp : fkRectLiftedVertex R p = root.1 := by
    apply Prod.ext <;> simp [p, fkRectLiftedVertex]
  have hsub : fkRectHorizontalCylinderGraph R ≤ fkRectTorusGraph R := by
    intro a b hab
    exact (fkRectHorizontalCylinderGraph_adj_iff R a b).mp hab |>.1
  obtain ⟨q, hq⟩ := fkRectWalk_exists_squareLift R hsub w p hp
  have hdisp := hq.sub_eq_developedDisplacement R
  have hqEq : q = p + fkRectWalkDevelopedDisplacement R w := by
    apply Prod.ext
    · have h := congrArg Prod.fst hdisp
      simp only [Prod.fst_sub, Prod.fst_add] at h ⊢
      omega
    · have h := congrArg Prod.snd hdisp
      simp only [Prod.snd_sub, Prod.snd_add] at h ⊢
      omega
  have hqRow : q.2 = (x.1.2.val : Int) :=
    hq.end_snd_eq_val_of_cylinder R rfl
  change (p + fkRectWalkDevelopedDisplacement R w).2 =
    (x.1.2.val : Int)
  rw [← hqEq]
  exact hqRow

private theorem fkRectHorizontalCylinderUnexploredRoot_eq_of_reachable
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    {x y : FKRectHorizontalCylinderUnexploredVertex R rho S}
    (hxy : (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Reachable x y) :
    fkRectHorizontalCylinderUnexploredComponentRoot R rho S x =
      fkRectHorizontalCylinderUnexploredComponentRoot R rho S y := by
  apply congrArg Quot.out
  exact SimpleGraph.ConnectedComponent.sound hxy

private theorem fkRectHorizontalCylinderUnexploredRootWalk_displacement_eq
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (hno : FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S)
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S)
    (w : (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Walk
        (fkRectHorizontalCylinderUnexploredComponentRoot R rho S x) x) :
    fkRectWalkDevelopedDisplacement R
        ((fkRectHorizontalCylinderUnexploredRootWalk R rho S x).map
          (fkRectHorizontalCylinderUnexploredInclusion R rho S)) =
      fkRectWalkDevelopedDisplacement R
        (w.map (fkRectHorizontalCylinderUnexploredInclusion R rho S)) := by
  let chosen := fkRectHorizontalCylinderUnexploredRootWalk R rho S x
  let c := chosen.append w.reverse
  have hcFst := hno _ c
  have hcSnd :=
    fkRectHorizontalCylinderUnexploredWalk_winding_snd_eq_zero
      R rho S c
  have hwindChosen : fkRectWalkWinding R
      (chosen.map (fkRectHorizontalCylinderUnexploredInclusion R rho S)) =
    fkRectWalkWinding R
      (w.map (fkRectHorizontalCylinderUnexploredInclusion R rho S)) := by
    apply Prod.ext
    · change (fkRectWalkWinding R
          (c.map (fkRectHorizontalCylinderUnexploredInclusion R rho S))).1 = 0
        at hcFst
      simp only [c, SimpleGraph.Walk.map_append] at hcFst
      rw [← SimpleGraph.Walk.reverse_map,
        fkRectWalkWinding_append, fkRectWalkWinding_reverse] at hcFst
      change (fkRectWalkWinding R
          (chosen.map (fkRectHorizontalCylinderUnexploredInclusion R rho S))).1 +
        -(fkRectWalkWinding R
          (w.map (fkRectHorizontalCylinderUnexploredInclusion R rho S))).1 = 0
        at hcFst
      omega
    · change (fkRectWalkWinding R
          (c.map (fkRectHorizontalCylinderUnexploredInclusion R rho S))).2 = 0
        at hcSnd
      simp only [c, SimpleGraph.Walk.map_append] at hcSnd
      rw [← SimpleGraph.Walk.reverse_map,
        fkRectWalkWinding_append, fkRectWalkWinding_reverse] at hcSnd
      change (fkRectWalkWinding R
          (chosen.map (fkRectHorizontalCylinderUnexploredInclusion R rho S))).2 +
        -(fkRectWalkWinding R
          (w.map (fkRectHorizontalCylinderUnexploredInclusion R rho S))).2 = 0
        at hcSnd
      omega
  rw [fkRectWalkDevelopedDisplacement_eq,
    fkRectWalkDevelopedDisplacement_eq, hwindChosen]



noncomputable def fkRectHorizontalCylinderUnexploredLiftSite
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S) : Site 2 :=
  fkRectSquareSiteOfPair (fkRectSquareDevelopPoint
    (fkRectHorizontalCylinderUnexploredLiftPoint R rho S x))

theorem fkRectHorizontalCylinderUnexploredLiftSite_injective
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) :
    Function.Injective
      (fkRectHorizontalCylinderUnexploredLiftSite R rho S) := by
  intro x y hxy
  have hdev : fkRectSquareDevelopPoint
      (fkRectHorizontalCylinderUnexploredLiftPoint R rho S x) =
    fkRectSquareDevelopPoint
      (fkRectHorizontalCylinderUnexploredLiftPoint R rho S y) :=
    fkRectSquareSiteOfPair_injective hxy
  have hlift := fkRectSquareDevelopPoint_injective hdev
  apply Subtype.ext
  rw [← fkRectHorizontalCylinderUnexploredLiftPoint_project R rho S x,
    ← fkRectHorizontalCylinderUnexploredLiftPoint_project R rho S y,
    hlift]

private theorem fkRectHorizontalCylinderUnexploredLiftPoint_step
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (hno : FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S)
    {x y : FKRectHorizontalCylinderUnexploredVertex R rho S}
    (hxy : (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Adj x y) :
    fkRectHorizontalCylinderUnexploredLiftPoint R rho S y -
        fkRectHorizontalCylinderUnexploredLiftPoint R rho S x =
      fkRectDevelopedStep R x.1 y.1 := by
  let wx := fkRectHorizontalCylinderUnexploredRootWalk R rho S x
  have hroot := fkRectHorizontalCylinderUnexploredRoot_eq_of_reachable
    R rho S hxy.reachable
  let candidate :
      (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
        (fkRectHorizontalCylinderBottomRoots R S)).Walk
          (fkRectHorizontalCylinderUnexploredComponentRoot R rho S y) y :=
    (wx.concat hxy).copy hroot rfl
  have hdisp :=
    fkRectHorizontalCylinderUnexploredRootWalk_displacement_eq
      R rho S hno y candidate
  let inclusion := fkRectHorizontalCylinderUnexploredInclusion R rho S
  have hOne : fkRectWalkDevelopedDisplacement R
      ((SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil).map inclusion) =
        fkRectDevelopedStep R x.1 y.1 := by
    simp [fkRectWalkDevelopedDisplacement, inclusion,
      fkRectHorizontalCylinderUnexploredInclusion]
  have hcandidate : fkRectWalkDevelopedDisplacement R
      (candidate.map inclusion) =
    fkRectWalkDevelopedDisplacement R (wx.map inclusion) +
      fkRectDevelopedStep R x.1 y.1 := by
    change fkRectWalkDevelopedDisplacement R
        (((wx.concat hxy).copy hroot rfl).map inclusion) = _
    rw [SimpleGraph.Walk.map_copy,
      fkRectWalkDevelopedDisplacement_copy,
      SimpleGraph.Walk.concat_eq_append,
      SimpleGraph.Walk.map_append,
      fkRectWalkDevelopedDisplacement_append]
    rw [hOne]
  rw [hcandidate] at hdisp
  unfold fkRectHorizontalCylinderUnexploredLiftPoint
  dsimp only
  have hrootPoint :
      (((fkRectHorizontalCylinderUnexploredComponentRoot R rho S y).1.1.val : Int),
        ((fkRectHorizontalCylinderUnexploredComponentRoot R rho S y).1.2.val : Int)) =
      (((fkRectHorizontalCylinderUnexploredComponentRoot R rho S x).1.1.val : Int),
        ((fkRectHorizontalCylinderUnexploredComponentRoot R rho S x).1.2.val : Int)) := by
    rw [← hroot]
  rw [hrootPoint, hdisp]
  apply Prod.ext
  · simp only [Prod.fst_sub, Prod.fst_add]
    ring
  · simp only [Prod.snd_sub, Prod.snd_add]
    ring

theorem fkRectHorizontalCylinderUnexploredLiftSite_adj_of_adj
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (hno : FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S)
    {x y : FKRectHorizontalCylinderUnexploredVertex R rho S}
    (hxy : (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Adj x y) :
    (hypercubicLattice 2).Adj
      (fkRectHorizontalCylinderUnexploredLiftSite R rho S x)
      (fkRectHorizontalCylinderUnexploredLiftSite R rho S y) := by
  have hcyl : (fkRectHorizontalCylinderGraph R).Adj x.1 y.1 := hxy
  have htorus := (fkRectHorizontalCylinderGraph_adj_iff R x.1 y.1).mp hcyl |>.1
  let px := fkRectHorizontalCylinderUnexploredLiftPoint R rho S x
  have hpx : fkRectLiftedVertex R px = x.1 :=
    fkRectHorizontalCylinderUnexploredLiftPoint_project R rho S x
  obtain ⟨q, hq, hqstep, haxis⟩ :=
    fkRectTorusGraph_adj_squareLift R htorus px hpx
  have hstep := fkRectHorizontalCylinderUnexploredLiftPoint_step
    R rho S hno hxy
  have hqEq : q =
      fkRectHorizontalCylinderUnexploredLiftPoint R rho S y := by
    dsimp [px] at hqstep
    apply Prod.ext
    · have h1 := congrArg Prod.fst hqstep
      have h2 := congrArg Prod.fst hstep
      simp only [Prod.fst_sub] at h1 h2 ⊢
      omega
    · have h1 := congrArg Prod.snd hqstep
      have h2 := congrArg Prod.snd hstep
      simp only [Prod.snd_sub] at h1 h2 ⊢
      omega
  rw [hqEq] at haxis
  exact (fkRectSquareAxisStep_iff_hypercubicAdj _ _).mp haxis

private theorem fkRectIntModFin_sub_one
    {N : Nat} (hN : 0 < N) (z : Int) :
    fkRectIntModFin hN (z - 1) =
      SixVertexArrows.cyclicPred hN (fkRectIntModFin hN z) := by
  apply Fin.ext
  rw [fkRectCyclicPred_val]
  let r := z % (N : Int)
  have hN0 : (N : Int) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hr0 : 0 ≤ r := Int.emod_nonneg z hN0
  have hrN : r < (N : Int) := by
    simpa using Int.emod_lt z hN0
  have hzmod : (z - 1) % (N : Int) = (r - 1) % (N : Int) := by
    rw [Int.sub_emod]
    simp [r]
  by_cases hr : r = 0
  · have hrepr : (r - 1) = ((N - 1 : Nat) : Int) + (N : Int) * (-1) := by
      rw [hr]
      omega
    have hnonneg : (0 : Int) ≤ ((N - 1 : Nat) : Int) := by omega
    have hlt : ((N - 1 : Nat) : Int) < N := by omega
    have hmod : (z - 1) % (N : Int) = (N - 1 : Nat) := by
      rw [hzmod, hrepr, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt hnonneg hlt]
    simp only [fkRectIntModFin, Fin.val_mk, Int.natMod]
    rw [hmod, Int.toNat_natCast]
    have hval : (z % (N : Int)).toNat = 0 := by
      change r.toNat = 0
      rw [hr]
      rfl
    rw [hval, if_pos rfl]
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hrsub0 : 0 ≤ r - 1 := by omega
    have hrsubN : r - 1 < (N : Int) := by omega
    have hmod : (z - 1) % (N : Int) = r - 1 := by
      rw [hzmod, Int.emod_eq_of_lt hrsub0 hrsubN]
    simp only [fkRectIntModFin, Fin.val_mk, Int.natMod]
    rw [hmod]
    have hrnat : ((r - 1).toNat : Int) = r - 1 :=
      Int.natCast_toNat_eq_self.mpr hrsub0
    have hzNat : (((z % (N : Int)).toNat : Nat) : Int) = r := by
      rw [Int.natCast_toNat_eq_self.mpr hr0]
    have hval0 : (z % (N : Int)).toNat ≠ 0 := by
      intro hzero
      have : r = 0 := by
        rw [← hzNat]
        simp [hzero]
      exact hr this
    rw [if_neg hval0]
    omega

private theorem fkRectTorusGraph_adj_of_squareDownStep_lifts
    (R : FKRectTorus) (p q : Int × Int)
    (hpRow : p.2 = ((fkRectLiftedVertex R p).2.val : Int))
    (hqRow : q.2 = ((fkRectLiftedVertex R q).2.val : Int))
    (hstep :
      fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p = (-1, 0) ∨
      fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p = (0, 1)) :
    (fkRectTorusGraph R).Adj
      (fkRectLiftedVertex R p) (fkRectLiftedVertex R q) := by
  let x := fkRectLiftedVertex R p
  let y := fkRectLiftedVertex R q
  have hrowRecoverP := fkRectSquareDevelopPoint_fst_sub_snd p
  have hrowRecoverQ := fkRectSquareDevelopPoint_fst_sub_snd q
  have hcolRecoverP := fkRectSquareDevelopPoint_snd_add_rowHalf p
  have hcolRecoverQ := fkRectSquareDevelopPoint_snd_add_rowHalf q
  have hrowOfStep (hs :
      fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p = (-1, 0) ∨
      fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p = (0, 1)) :
      q.2 = p.2 - 1 := by
    rcases hs with hs | hs <;>
      have hu := congrArg Prod.fst hs <;>
      have hv := congrArg Prod.snd hs <;>
      simp only [Prod.fst_sub, Prod.snd_sub] at hu hv <;>
      omega
  have hrow : q.2 = p.2 - 1 := hrowOfStep hstep
  have hxrow0 : x.2.val ≠ 0 := by
    intro hx0
    have hyNonneg : (0 : Int) ≤ y.2.val := by positivity
    dsimp [x, y] at hx0 hyNonneg
    rw [hpRow, hqRow] at hrow
    simp only [hx0, Nat.cast_zero] at hrow
    omega
  have hpredRow :
      SixVertexArrows.cyclicPred R.height_pos x.2 = y.2 := by
    apply Fin.ext
    rw [fkRectCyclicPred_val]
    simp only [if_neg hxrow0]
    have hrowVal : (y.2.val : Int) = (x.2.val : Int) - 1 := by
      dsimp [x, y]
      rw [← hpRow, ← hqRow]
      exact hrow
    omega
  rcases hstep with hstep | hstep
  · have hu := congrArg Prod.fst hstep
    have hv := congrArg Prod.snd hstep
    simp only [Prod.fst_sub, Prod.snd_sub] at hu hv
    by_cases heven : Even x.2.val
    · obtain ⟨k, hk⟩ := heven
      have hevenX : Even x.2.val := ⟨k, hk⟩
      have hpY : p.2 = 2 * (k : Int) := by
        have hkP : (fkRectLiftedVertex R p).2.val = k + k := by
          simpa [x] using hk
        have hkInt : ((fkRectLiftedVertex R p).2.val : Int) =
            (k : Int) + k := by exact_mod_cast hkP
        rw [hpRow]
        omega
      have hqY : q.2 = 2 * (k : Int) - 1 := by omega
      have hpHalf : p.2 / 2 = (k : Int) := by rw [hpY]; omega
      have hqHalf : q.2 / 2 = (k : Int) - 1 := by rw [hqY]; omega
      have hcol : q.1 = p.1 - 1 := by
        rw [hpHalf] at hcolRecoverP
        rw [hqHalf] at hcolRecoverQ
        omega
      have hpredCol :
          SixVertexArrows.cyclicPred R.width_pos x.1 = y.1 := by
        dsimp [x, y, fkRectLiftedVertex]
        rw [← fkRectIntModFin_sub_one R.width_pos p.1]
        congr 1
        omega
      let e : R.EdgeIndex := (false, x)
      refine ⟨e, ?_⟩
      change fkRectTorusIndexedEdge R e = s(x, y)
      dsimp [e]
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true,
        if_false, hevenX, if_true]
      rw [hpredCol, hpredRow]
    · have hodd : Odd x.2.val := Nat.not_even_iff_odd.mp heven
      obtain ⟨k, hk⟩ := hodd
      have hpY : p.2 = 2 * (k : Int) + 1 := by
        have hkP : (fkRectLiftedVertex R p).2.val = 2 * k + 1 := by
          simpa [x] using hk
        have hkInt : ((fkRectLiftedVertex R p).2.val : Int) =
            2 * (k : Int) + 1 := by exact_mod_cast hkP
        rw [hpRow]
        omega
      have hqY : q.2 = 2 * (k : Int) := by omega
      have hpHalf : p.2 / 2 = (k : Int) := by rw [hpY]; omega
      have hqHalf : q.2 / 2 = (k : Int) := by rw [hqY]; omega
      have hcol : q.1 = p.1 := by
        rw [hpHalf] at hcolRecoverP
        rw [hqHalf] at hcolRecoverQ
        omega
      have hcolFin : y.1 = x.1 := by
        dsimp [x, y, fkRectLiftedVertex]
        rw [hcol]
      let e : R.EdgeIndex := (true, x)
      refine ⟨e, ?_⟩
      change fkRectTorusIndexedEdge R e = s(x, y)
      dsimp [e]
      simp only [fkRectTorusIndexedEdge, if_true]
      rw [hpredRow]
      exact congrArg (fun z => s(x, z)) (Prod.ext hcolFin.symm rfl)
  · have hu := congrArg Prod.fst hstep
    have hv := congrArg Prod.snd hstep
    simp only [Prod.fst_sub, Prod.snd_sub] at hu hv
    by_cases heven : Even x.2.val
    · obtain ⟨k, hk⟩ := heven
      have hpY : p.2 = 2 * (k : Int) := by
        have hkP : (fkRectLiftedVertex R p).2.val = k + k := by
          simpa [x] using hk
        have hkInt : ((fkRectLiftedVertex R p).2.val : Int) =
            (k : Int) + k := by exact_mod_cast hkP
        rw [hpRow]
        omega
      have hqY : q.2 = 2 * (k : Int) - 1 := by omega
      have hpHalf : p.2 / 2 = (k : Int) := by rw [hpY]; omega
      have hqHalf : q.2 / 2 = (k : Int) - 1 := by rw [hqY]; omega
      have hcol : q.1 = p.1 := by
        rw [hpHalf] at hcolRecoverP
        rw [hqHalf] at hcolRecoverQ
        omega
      have hcolFin : y.1 = x.1 := by
        dsimp [x, y, fkRectLiftedVertex]
        rw [hcol]
      let e : R.EdgeIndex := (true, x)
      refine ⟨e, ?_⟩
      change fkRectTorusIndexedEdge R e = s(x, y)
      dsimp [e]
      simp only [fkRectTorusIndexedEdge, if_true]
      rw [hpredRow]
      exact congrArg (fun z => s(x, z)) (Prod.ext hcolFin.symm rfl)
    · have hodd : Odd x.2.val := Nat.not_even_iff_odd.mp heven
      obtain ⟨k, hk⟩ := hodd
      have hoddX : Odd x.2.val := ⟨k, hk⟩
      have hpY : p.2 = 2 * (k : Int) + 1 := by
        have hkP : (fkRectLiftedVertex R p).2.val = 2 * k + 1 := by
          simpa [x] using hk
        have hkInt : ((fkRectLiftedVertex R p).2.val : Int) =
            2 * (k : Int) + 1 := by exact_mod_cast hkP
        rw [hpRow]
        omega
      have hqY : q.2 = 2 * (k : Int) := by omega
      have hpHalf : p.2 / 2 = (k : Int) := by rw [hpY]; omega
      have hqHalf : q.2 / 2 = (k : Int) := by rw [hqY]; omega
      have hcol : q.1 = p.1 + 1 := by
        rw [hpHalf] at hcolRecoverP
        rw [hqHalf] at hcolRecoverQ
        omega
      have hpredCol :
          SixVertexArrows.cyclicPred R.width_pos y.1 = x.1 := by
        dsimp [x, y, fkRectLiftedVertex]
        rw [← fkRectIntModFin_sub_one R.width_pos q.1]
        congr 1
        omega
      let e : R.EdgeIndex := (false, (y.1, x.2))
      refine ⟨e, ?_⟩
      change fkRectTorusIndexedEdge R e = s(x, y)
      dsimp [e]
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true,
        if_false, heven, if_false]
      rw [hpredCol, hpredRow]

private theorem fkRectHorizontalCylinderUnexplored_adj_of_liftSite_adj
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    {x y : FKRectHorizontalCylinderUnexploredVertex R rho S}
    (hxy : (hypercubicLattice 2).Adj
      (fkRectHorizontalCylinderUnexploredLiftSite R rho S x)
      (fkRectHorizontalCylinderUnexploredLiftSite R rho S y)) :
    (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Adj x y := by
  let px := fkRectHorizontalCylinderUnexploredLiftPoint R rho S x
  let py := fkRectHorizontalCylinderUnexploredLiftPoint R rho S y
  have haxis : FKRectSquareAxisStep
      (fkRectSquareDevelopPoint px) (fkRectSquareDevelopPoint py) :=
    (fkRectSquareAxisStep_iff_hypercubicAdj _ _).mpr hxy
  have hpxRow : px.2 = ((fkRectLiftedVertex R px).2.val : Int) := by
    rw [fkRectHorizontalCylinderUnexploredLiftPoint_project R rho S x]
    exact fkRectHorizontalCylinderUnexploredLiftPoint_snd_eq_val R rho S x
  have hpyRow : py.2 = ((fkRectLiftedVertex R py).2.val : Int) := by
    rw [fkRectHorizontalCylinderUnexploredLiftPoint_project R rho S y]
    exact fkRectHorizontalCylinderUnexploredLiftPoint_snd_eq_val R rho S y
  have htorus : (fkRectTorusGraph R).Adj
      (fkRectLiftedVertex R px) (fkRectLiftedVertex R py) := by
    rcases haxis with h | h | h | h
    · exact fkRectTorusGraph_adj_of_squareDownStep_lifts
        R px py hpxRow hpyRow (Or.inl h)
    · exact fkRectTorusGraph_adj_of_squareDownStep_lifts
        R px py hpxRow hpyRow (Or.inr h)
    · apply (fkRectTorusGraph R).symm
      apply fkRectTorusGraph_adj_of_squareDownStep_lifts
        R py px hpyRow hpxRow
      left
      apply Prod.ext <;>
        have h' := congrArg Prod.fst h <;>
        have h'' := congrArg Prod.snd h <;>
        simp only [Prod.fst_sub, Prod.snd_sub] at h' h'' ⊢ <;>
        omega
    · apply (fkRectTorusGraph R).symm
      apply fkRectTorusGraph_adj_of_squareDownStep_lifts
        R py px hpyRow hpxRow
      right
      apply Prod.ext <;>
        have h' := congrArg Prod.fst h <;>
        have h'' := congrArg Prod.snd h <;>
        simp only [Prod.fst_sub, Prod.snd_sub] at h' h'' ⊢ <;>
        omega
  have hrowDiff :
      (((fkRectLiftedVertex R py).2.val : Int) -
        (fkRectLiftedVertex R px).2.val).natAbs = 1 := by
    have hpRecover := fkRectSquareDevelopPoint_fst_sub_snd px
    have hqRecover := fkRectSquareDevelopPoint_fst_sub_snd py
    rw [hpxRow] at hpRecover
    rw [hpyRow] at hqRecover
    rcases haxis with h | h | h | h <;>
      have h' := congrArg Prod.fst h <;>
      have h'' := congrArg Prod.snd h <;>
      simp only [Prod.fst_sub, Prod.snd_sub] at h' h'' <;>
      omega
  have hnotSeam : ¬ fkRectCrossesVerticalSeam R
      s(fkRectLiftedVertex R px, fkRectLiftedVertex R py) := by
    rw [fkRectCrossesVerticalSeam_mk]
    intro hcross
    have hh := R.height_gt_two
    rcases hcross with ⟨hx0, hylast⟩ | ⟨hy0, hxlast⟩ <;>
      omega
  apply (fkRectHorizontalCylinderGraph_adj_iff R x.1 y.1).mpr
  refine ⟨?_, ?_⟩
  · simpa [px, py,
      fkRectHorizontalCylinderUnexploredLiftPoint_project] using htorus
  · intro hcut
    rw [fkRectHorizontalCutGraphEdges, Finset.mem_image] at hcut
    obtain ⟨a, ha, hea⟩ := hcut
    apply hnotSeam
    have hpair : s(fkRectLiftedVertex R px, fkRectLiftedVertex R py) =
        s(x.1, y.1) := by
      rw [fkRectHorizontalCylinderUnexploredLiftPoint_project R rho S x,
        fkRectHorizontalCylinderUnexploredLiftPoint_project R rho S y]
    rw [hpair, ← hea]
    exact fkRectCrossesVerticalSeam_indexedEdge_of_horizontalCut_planarization
      R a ha



noncomputable def fkRectHorizontalCylinderUnexploredLiftRadius
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) : Nat :=
  Finset.univ.sup fun x : FKRectHorizontalCylinderUnexploredVertex R rho S =>
    max ((fkRectHorizontalCylinderUnexploredLiftSite R rho S x 0).natAbs)
      ((fkRectHorizontalCylinderUnexploredLiftSite R rho S x 1).natAbs)

private theorem fkRectHorizontalCylinderUnexploredLiftSite_mem_box
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S) :
    fkRectHorizontalCylinderUnexploredLiftSite R rho S x ∈
      box 2 (fkRectHorizontalCylinderUnexploredLiftRadius R rho S) := by
  intro i
  have hmax : max
      ((fkRectHorizontalCylinderUnexploredLiftSite R rho S x 0).natAbs)
      ((fkRectHorizontalCylinderUnexploredLiftSite R rho S x 1).natAbs) ≤
      fkRectHorizontalCylinderUnexploredLiftRadius R rho S := by
    exact Finset.le_sup (s := Finset.univ) (f := fun y =>
      max ((fkRectHorizontalCylinderUnexploredLiftSite R rho S y 0).natAbs)
        ((fkRectHorizontalCylinderUnexploredLiftSite R rho S y 1).natAbs))
      (Finset.mem_univ x)
  fin_cases i
  · exact (le_max_left _ _).trans hmax
  · exact (le_max_right _ _).trans hmax



noncomputable def fkRectHorizontalCylinderUnexploredBoxEmbedding
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) :
    FKRectHorizontalCylinderUnexploredVertex R rho S →
      FK.boxVerts 2
        (fkRectHorizontalCylinderUnexploredLiftRadius R rho S) :=
  fun x => ⟨fkRectHorizontalCylinderUnexploredLiftSite R rho S x,
    fkRectHorizontalCylinderUnexploredLiftSite_mem_box R rho S x⟩

theorem fkRectHorizontalCylinderUnexploredBoxEmbedding_injective
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) :
    Function.Injective
      (fkRectHorizontalCylinderUnexploredBoxEmbedding R rho S) := by
  intro x y hxy
  apply fkRectHorizontalCylinderUnexploredLiftSite_injective R rho S
  exact congrArg Subtype.val hxy

theorem fkRectHorizontalCylinderUnexploredBox_adjMatch
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (hno : FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S) :
    FK.ocd_AdjMatch
      (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
        (fkRectHorizontalCylinderBottomRoots R S))
      (FK.boxGraph 2
        (fkRectHorizontalCylinderUnexploredLiftRadius R rho S))
      (fkRectHorizontalCylinderUnexploredBoxEmbedding R rho S) := by
  intro x y
  constructor
  · intro hxy
    exact fkRectHorizontalCylinderUnexploredLiftSite_adj_of_adj
      R rho S hno hxy
  · intro hxy
    exact fkRectHorizontalCylinderUnexplored_adj_of_liftSite_adj
      R rho S hxy




structure FKRectHorizontalCylinderUnexploredPlanarization
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) where
  radius : Nat
  embedding : FKRectHorizontalCylinderUnexploredVertex R rho S →
    FK.boxVerts 2 radius
  injective : Function.Injective embedding
  adjMatch : FK.ocd_AdjMatch
    (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S))
    (FK.boxGraph 2 radius) embedding



noncomputable def FKRectHorizontalCylinderUnexploredPlanarization.ofNoWinding
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (hno : FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S) :
    FKRectHorizontalCylinderUnexploredPlanarization R rho S where
  radius := fkRectHorizontalCylinderUnexploredLiftRadius R rho S
  embedding := fkRectHorizontalCylinderUnexploredBoxEmbedding R rho S
  injective :=
    fkRectHorizontalCylinderUnexploredBoxEmbedding_injective R rho S
  adjMatch := fkRectHorizontalCylinderUnexploredBox_adjMatch R rho S hno



noncomputable def FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (pair : Fin R.width → Fin R.width) (S : Finset (Fin R.width))
    (hS : S.Nonempty)
    (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair S rho) :
    FKRectHorizontalCylinderUnexploredPlanarization R rho S :=
  .ofNoWinding R rho S
    (fkRectHorizontalCylinder_noHorizontalWinding_of_pairedWitness
      R rho pair S hS hW)



theorem fkRectHorizontalCylinderUnexploredConnection_freeMass_le_boxConn
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (P : FKRectHorizontalCylinderUnexploredPlanarization R rho S)
    (source target : FKRectHorizontalCylinderUnexploredVertex R rho S)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (∑ omega,
        (FKFiniteConnectionEvent
          (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
            (fkRectHorizontalCylinderBottomRoots R S)) source target).indicator
          (fun _ => (1 : Real)) omega *
        FK.fkProb
          (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
            (fkRectHorizontalCylinderBottomRoots R S)) p q omega) ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure
          (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real
        (FK.boxConnEvent 2 P.radius
          (P.embedding source) (P.embedding target)) := by
  exact fkFiniteConnection_freeMass_le_boxConn _ P.radius P.embedding
    P.injective P.adjMatch source target hp hp1 hq




theorem fkRectHorizontalCylinder_conditionalConnection_le_boxConn
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (P : FKRectHorizontalCylinderUnexploredPlanarization R rho S)
    (source target : FKRectHorizontalCylinderUnexploredVertex R rho S)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (∑ sigma : ConfigSpace (Sym2 R.Vertex),
        (FK.ocd_innerRestrict
          (Subtype.val :
            FKRectHorizontalCylinderUnexploredVertex R rho S → R.Vertex) ⁻¹'
          FKFiniteConnectionEvent
            (FK.clusterUnexploredGraph
              (fkRectHorizontalCylinderGraph R) rho
              (fkRectHorizontalCylinderBottomRoots R S))
            source target).indicator (fun _ => (1 : Real)) sigma *
        FK.condBcProb (fkRectHorizontalCylinderGraph R)
          (StatMech.Lattice.boundaryCliqueGraph
            (fun _ : R.Vertex => False)) p q
          (FK.clusterUnexploredPairEdges
            (fkRectHorizontalCylinderGraph R) rho
            (fkRectHorizontalCylinderBottomRoots R S)) rho sigma) ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure
          (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real
        (FK.boxConnEvent 2 P.radius
          (P.embedding source) (P.embedding target)) := by
  rw [fkRectHorizontalCylinder_condBcProb_innerEvent_eq_freeUnexplored
    R rho S hp hp1 (zero_lt_one.trans_le hq)]
  exact fkRectHorizontalCylinderUnexploredConnection_freeMass_le_boxConn
    R rho S P source target hp hp1 hq



theorem fkRectHorizontalCylinder_bottom_top_verticalDisplacement
    (R : FKRectTorus) (x y : Fin R.width) :
    ((y, fkRectTopRow R).2.val : Int) -
        ((x, fkRectBottomRow R).2.val : Int) = R.height - 1 := by
  have hh := R.height_pos
  simp [fkRectTopRow, fkRectBottomRow]
  omega

end

end StatMech.FrontierD
