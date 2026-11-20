/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































































import Code.Percolation.DctDifferentialFull
import Code.Percolation.DctDifferential
import Code.Percolation.Exploration
import Code.Percolation.LastExit

open MeasureTheory Function Set SimpleGraph
open scoped NNReal ENNReal
open StatMech

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}










def pivotalEvent (e : Sym2 (Site d)) (A : Set (ConfigSpace (Sym2 (Site d)))) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | IsPivotal e A ω}

@[simp]
theorem mem_pivotalEvent {e : Sym2 (Site d)} {A : Set (ConfigSpace (Sym2 (Site d)))}
    {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ pivotalEvent e A ↔ IsPivotal e A ω := Iff.rfl





theorem pivotalEvent_dependsOn (A : Set (ConfigSpace (Sym2 (Site d)))) (F : Finset (Sym2 (Site d)))
    (e : Sym2 (Site d))
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set (Sym2 (Site d)))) :
    DependsOn ((pivotalEvent e A).indicator (fun _ => (1 : ℝ))) (F : Set (Sym2 (Site d))) := by
  intro ω ω' h
  have hAiff : ∀ a b : ConfigSpace (Sym2 (Site d)),
      (∀ i ∈ (F : Set (Sym2 (Site d))), a i = b i) → (a ∈ A ↔ b ∈ A) := by
    intro a b hab
    by_cases ha : a ∈ A
    · refine ⟨fun _ => ?_, fun _ => ha⟩
      by_contra hb
      have := hA hab
      rw [Set.indicator_of_mem ha, Set.indicator_of_notMem hb] at this; norm_num at this
    · refine ⟨fun hc => absurd hc ha, fun hb => ?_⟩
      by_contra
      have := hA hab
      rw [Set.indicator_of_notMem ha, Set.indicator_of_mem hb] at this; norm_num at this
  have h1 : (setOpen e ω ∈ A ↔ setOpen e ω' ∈ A) := by
    apply hAiff; intro i hi
    by_cases hie : i = e
    · subst hie; simp [setOpen]
    · rw [setOpen_of_ne hie, setOpen_of_ne hie, h i hi]
  have h2 : (setClosed e ω ∈ A ↔ setClosed e ω' ∈ A) := by
    apply hAiff; intro i hi
    by_cases hie : i = e
    · subst hie; simp [setClosed]
    · rw [setClosed_of_ne hie, setClosed_of_ne hie, h i hi]
  have hpiv : IsPivotal e A ω ↔ IsPivotal e A ω' := by
    unfold IsPivotal
    rw [(propext h1 : (setOpen e ω ∈ A) = (setOpen e ω' ∈ A)),
        (propext h2 : (setClosed e ω ∈ A) = (setClosed e ω' ∈ A))]
  by_cases hmem : ω ∈ pivotalEvent e A
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hpiv.mp hmem)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun hc => hmem (hpiv.mpr hc))]



theorem restrict_setOpen (F : Finset (Sym2 (Site d))) (e : Sym2 (Site d)) (he : e ∈ F)
    (ω : ConfigSpace (Sym2 (Site d))) :
    F.restrict (setOpen e ω) = setOpen (⟨e, he⟩ : ↥F) (F.restrict ω) := by
  funext j
  by_cases hj : j = (⟨e, he⟩ : ↥F)
  · subst hj; simp [setOpen, Finset.restrict]
  · have hje : (j : Sym2 (Site d)) ≠ e := fun hc => hj (Subtype.ext hc)
    simp only [setOpen_of_ne hj]
    show (setOpen e ω) (j : Sym2 (Site d)) = _
    rw [setOpen_of_ne hje]; rfl



theorem restrict_setClosed (F : Finset (Sym2 (Site d))) (e : Sym2 (Site d)) (he : e ∈ F)
    (ω : ConfigSpace (Sym2 (Site d))) :
    F.restrict (setClosed e ω) = setClosed (⟨e, he⟩ : ↥F) (F.restrict ω) := by
  funext j
  by_cases hj : j = (⟨e, he⟩ : ↥F)
  · subst hj; simp [setClosed, Finset.restrict]
  · have hje : (j : Sym2 (Site d)) ≠ e := fun hc => hj (Subtype.ext hc)
    simp only [setClosed_of_ne hj]
    show (setClosed e ω) (j : Sym2 (Site d)) = _
    rw [setClosed_of_ne hje]; rfl






theorem restrict_image_pivotalEvent (A : Set (ConfigSpace (Sym2 (Site d))))
    (F : Finset (Sym2 (Site d))) (e : Sym2 (Site d)) (he : e ∈ F)
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set (Sym2 (Site d)))) :
    F.restrict '' (pivotalEvent e A)
      = {η : ConfigSpace ↥F | IsPivotal (⟨e, he⟩ : ↥F) (F.restrict '' A) η} := by
  have hcyl : A = cylinder F (F.restrict '' A) := eq_cylinder_restrict_image A F hA
  have memA : ∀ ω : ConfigSpace (Sym2 (Site d)), ω ∈ A ↔ F.restrict ω ∈ F.restrict '' A := by
    intro ω; conv_lhs => rw [hcyl]; rw [mem_cylinder]
  ext η
  constructor
  · rintro ⟨ω, hω, rfl⟩
    show IsPivotal (⟨e, he⟩ : ↥F) (F.restrict '' A) (F.restrict ω)
    have hω' : IsPivotal e A ω := hω
    unfold IsPivotal at hω' ⊢
    rw [← restrict_setOpen F e he ω, ← restrict_setClosed F e he ω, ← memA, ← memA]
    exact hω'
  · intro hη
    refine ⟨extendOff F (fun _ => false) η, ?_, restrict_extendOff F _ η⟩
    show IsPivotal e A (extendOff F (fun _ => false) η)
    unfold IsPivotal at hη ⊢
    rw [memA, memA, restrict_setOpen F e he, restrict_setClosed F e he, restrict_extendOff]
    exact hη






theorem pivotalProb_eq_realPivotal (p : ℝ≥0) (hp : p ≤ 1)
    (A : Set (ConfigSpace (Sym2 (Site d)))) (F : Finset (Sym2 (Site d))) (e : Sym2 (Site d))
    (he : e ∈ F)
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set (Sym2 (Site d)))) :
    pivotalProb (p : ℝ) (F.restrict '' A) (⟨e, he⟩ : ↥F)
      = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (pivotalEvent e A) := by
  rw [realProb_cylinder_eq_prob p hp (pivotalEvent e A) F (pivotalEvent_dependsOn A F e hA),
      restrict_image_pivotalEvent A F e he hA]
  unfold pivotalProb prob
  rfl











theorem deriv_boxCrossProb_inf (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    deriv (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) (p : ℝ)
      = ∑ e : ↥(boxEdgeFinset d n),
          (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
            (pivotalEvent (↑e : Sym2 (Site d)) (boxCrossingEvent d n)) := by
  rw [deriv_boxCrossProb]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  have hbridge := pivotalProb_eq_realPivotal p hp (boxCrossingEvent d n)
    (boxEdgeFinset d n) (↑e : Sym2 (Site d)) e.2 (boxCrossingEvent_dependsOn n)
  simpa using hbridge











def connBdry (d n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  ∃ (hx : x ∈ box d n) (y : Site d) (hy : y ∈ box d n),
    y ∈ vertexBoundary d n ∧ ConnectedWithin d ω (box d n) ⟨x, hx⟩ ⟨y, hy⟩



noncomputable def surfaceSet (d n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) : Finset (Site d) := by
  classical
  exact (boxFinset d n).filter (fun x => ¬ connBdry d n ω x)

theorem mem_surfaceSet {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))} {x : Site d} :
    x ∈ surfaceSet d n ω ↔ x ∈ box d n ∧ ¬ connBdry d n ω x := by
  classical
  rw [surfaceSet, Finset.mem_filter, mem_boxFinset]


theorem surfaceSet_subset_box (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) :
    surfaceSet d n ω ⊆ boxFinset d n := by
  intro x hx
  rw [mem_boxFinset]; exact (mem_surfaceSet.mp hx).1


def surfaceEvent (d n : ℕ) (S : Finset (Site d)) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | surfaceSet d n ω = S}




theorem surfaceSet_congr (n : ℕ) {ω ω' : ConfigSpace (Sym2 (Site d))}
    (h : ∀ e ∈ (boxEdgeFinset d n : Set (Sym2 (Site d))), ω e = ω' e) :
    surfaceSet d n ω = surfaceSet d n ω' := by
  classical
  have hcoord : ∀ x y : Site d, x ∈ box d n → y ∈ box d n → ω s(x, y) = ω' s(x, y) :=
    coord_of_agree n h
  have hG := openSubgraphInduce_box_congr n hcoord
  unfold surfaceSet connBdry ConnectedWithin
  rw [hG]



theorem surfaceEvent_dependsOn (n : ℕ) (S : Finset (Site d)) :
    DependsOn ((surfaceEvent d n S).indicator (fun _ => (1 : ℝ)))
      ((boxEdgeFinset d n : Set (Sym2 (Site d)))) := by
  intro ω ω' h
  have hiff : ω ∈ surfaceEvent d n S ↔ ω' ∈ surfaceEvent d n S := by
    unfold surfaceEvent; simp only [Set.mem_setOf_eq, surfaceSet_congr n h]
  by_cases hω : ω ∈ surfaceEvent d n S
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (hiff.mp hω)]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun hc => hω (hiff.mpr hc))]




theorem measurableSet_surfaceEvent (n : ℕ) (S : Finset (Site d)) :
    MeasurableSet (surfaceEvent d n S) := by
  rw [eq_cylinder_restrict_image _ _ (surfaceEvent_dependsOn n S)]
  exact MeasurableSet.cylinder _ (S := _) MeasurableSet.of_discrete








theorem sum_surfaceProb (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    ∑ S ∈ (boxFinset d n).powerset,
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (surfaceEvent d n S) = 1 := by
  classical
  have hcover : (⋃ S ∈ (boxFinset d n).powerset, surfaceEvent d n S) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨surfaceSet d n ω, Finset.mem_powerset.mpr (surfaceSet_subset_box n ω), rfl⟩
  have hdisj : ((boxFinset d n).powerset : Set (Finset (Site d))).PairwiseDisjoint
      (surfaceEvent d n) := by
    intro S _ S' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω hωS hωS'
    exact hne (by rw [← (hωS : surfaceSet d n ω = S), ← (hωS' : surfaceSet d n ω = S')])
  have hmeas : ∀ S ∈ (boxFinset d n).powerset, MeasurableSet (surfaceEvent d n S) :=
    fun S _ => measurableSet_surfaceEvent n S
  rw [← measureReal_biUnion_finset hdisj hmeas, hcover]
  exact probReal_univ












noncomputable def boxEdgesOutside (d n : ℕ) (S : Finset (Site d)) : Finset (Sym2 (Site d)) :=
  (boxEdgeFinset d n) \ (edgesWithinFinset S)


theorem disjoint_boxEdgesOutside (n : ℕ) (S : Finset (Site d)) :
    Disjoint (edgesWithinFinset S) (boxEdgesOutside d n S) := by
  rw [boxEdgesOutside]; exact disjoint_sdiff_self_right



theorem pair_mem_boxEdgesOutside {n : ℕ} {S : Finset (Site d)} {a z : Site d}
    (ha : a ∈ box d n) (hz : z ∈ box d n) (hor : a ∉ S ∨ z ∉ S) :
    s(a, z) ∈ boxEdgesOutside d n S := by
  classical
  rw [boxEdgesOutside, Finset.mem_sdiff]
  refine ⟨mem_boxEdgeFinset.mpr ⟨a, z, ha, hz, rfl⟩, ?_⟩
  rw [mem_edgesWithinFinset]
  rintro ⟨x, hx, y, hy, hxy⟩
  rw [Sym2.eq_iff] at hxy
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (rcases hor with h | h) <;> first | exact h hx | exact h hy




theorem walk_vertex_connBdry {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))}
    {a y : ↥(box d n)} (hy : (y : Site d) ∈ vertexBoundary d n)
    (w : (openSubgraphInduce d ω (box d n)).Walk a y)
    (v : ↥(box d n)) (hv : v ∈ w.support) :
    connBdry d n ω (v : Site d) :=
  ⟨v.2, y, y.2, hy, (w.dropUntil v hv).reachable⟩




theorem walk_transfer_avoidS {n : ℕ} {ω ω' : ConfigSpace (Sym2 (Site d))} {S : Finset (Site d)}
    (hagree : ∀ x z : Site d, x ∈ box d n → z ∈ box d n →
       (x ∉ S ∨ z ∉ S) → ω s(x, z) = ω' s(x, z))
    {a b : ↥(box d n)} (w : (openSubgraphInduce d ω (box d n)).Walk a b)
    (hsupp : ∀ v ∈ w.support, (v : Site d) ∉ S) :
    Nonempty ((openSubgraphInduce d ω' (box d n)).Walk a b) := by
  induction w with
  | nil => exact ⟨Walk.nil⟩
  | @cons u v t hadj p ih =>
    have huS : (u : Site d) ∉ S := hsupp u (by simp)
    have hsupp' : ∀ z ∈ p.support, (z : Site d) ∉ S := fun z hz =>
      hsupp z (by simp only [Walk.support_cons, List.mem_cons]; right; exact hz)
    have heq : ω s((u : Site d), (v : Site d)) = ω' s((u : Site d), (v : Site d)) :=
      hagree u v u.2 v.2 (Or.inl huS)
    have hadj' : (openSubgraphInduce d ω' (box d n)).Adj u v := by
      simp only [openSubgraphInduce_adj, openSubgraph_adj]
      exact ⟨hadj.1, by rw [← heq]; exact hadj.2⟩
    obtain ⟨w'⟩ := ih hsupp'
    exact ⟨Walk.cons hadj' w'⟩



theorem connBdry_of_mem_boundary {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))} {y : Site d}
    (hy : y ∈ box d n) (hyb : y ∈ vertexBoundary d n) : connBdry d n ω y :=
  ⟨hy, y, hy, hyb, connectedWithin_refl ω (box d n) ⟨y, hy⟩⟩




theorem connBdry_of_open_edge {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))} {u w : Site d}
    (hu : u ∈ box d n) (hw : w ∈ box d n) (hopen : IsOpenEdge d ω u w)
    (hcbw : connBdry d n ω w) : connBdry d n ω u := by
  obtain ⟨_, y, hy, hyb, hreach⟩ := hcbw
  have hadj : (openSubgraphInduce d ω (box d n)).Adj ⟨u, hu⟩ ⟨w, hw⟩ := by
    simp only [openSubgraphInduce_adj, openSubgraph_adj]; exact hopen
  exact ⟨hu, y, hy, hyb, (SimpleGraph.Adj.reachable hadj).trans hreach⟩














theorem connBdry_transfer {n : ℕ} {ω ω' : ConfigSpace (Sym2 (Site d))}
    {S : Finset (Site d)} (hS : surfaceSet d n ω = S)
    (hagree : ∀ a z : Site d, a ∈ box d n → z ∈ box d n →
       (a ∉ S ∨ z ∉ S) → ω s(a, z) = ω' s(a, z))
    {x : Site d} (hxbox : x ∈ box d n) :
    connBdry d n ω x ↔ connBdry d n ω' x := by
  classical
  constructor
  · 
    intro hcb
    obtain ⟨hx, y, hy, hyb, hreach⟩ := hcb
    obtain ⟨w⟩ := hreach
    have hsupp : ∀ v ∈ w.support, (v : Site d) ∉ surfaceSet d n ω := by
      intro v hv; rw [mem_surfaceSet]; rintro ⟨_, hnc⟩
      exact hnc (walk_vertex_connBdry hyb w v hv)
    have hsuppS : ∀ v ∈ w.support, (v : Site d) ∉ S := fun v hv => hS ▸ hsupp v hv
    obtain ⟨w'⟩ := walk_transfer_avoidS hagree w hsuppS
    exact ⟨hx, y, hy, hyb, ⟨w'⟩⟩
  · 
    intro hcb'
    by_cases hxS : x ∈ S
    · exfalso
      obtain ⟨hx, y, hy, hyb, hreach'⟩ := hcb'
      obtain ⟨w⟩ := hreach'
      have hyS : (⟨y, hy⟩ : ↥(box d n)) ∉ ({v : ↥(box d n) | (v : Site d) ∈ S}) := by
        simp only [Set.mem_setOf_eq]
        intro hyc
        exact (mem_surfaceSet.mp (hS ▸ hyc)).2 (connBdry_of_mem_boundary hy hyb)
      have hxSset : (⟨x, hx⟩ : ↥(box d n)) ∈ ({v : ↥(box d n) | (v : Site d) ∈ S}) := hxS
      obtain ⟨u, ww, huS, hwwS, hadj, _⟩ :=
        exists_lastExit w ({v : ↥(box d n) | (v : Site d) ∈ S}) hxSset hyS
      have hwwSset : (ww : Site d) ∉ S := hwwS
      have hopen' : IsOpenEdge d ω' (u : Site d) (ww : Site d) := by
        have := hadj
        simp only [openSubgraphInduce_adj, openSubgraph_adj] at this; exact this
      have heq : ω s((u : Site d), (ww : Site d)) = ω' s((u : Site d), (ww : Site d)) :=
        hagree u ww u.2 ww.2 (Or.inr hwwSset)
      have hopen : IsOpenEdge d ω (u : Site d) (ww : Site d) :=
        ⟨hopen'.1, by rw [heq]; exact hopen'.2⟩
      have hcbww : connBdry d n ω (ww : Site d) := by
        by_contra hnc
        exact hwwSset (hS ▸ (mem_surfaceSet.mpr ⟨ww.2, hnc⟩))
      exact (mem_surfaceSet.mp (hS ▸ (huS : (u : Site d) ∈ S))).2
        (connBdry_of_open_edge u.2 ww.2 hopen hcbww)
    · 
      by_contra hnc
      exact hxS (hS ▸ (mem_surfaceSet.mpr ⟨hxbox, hnc⟩))






theorem surfaceSet_congr_outside (n : ℕ) {ω ω' : ConfigSpace (Sym2 (Site d))}
    {S : Finset (Site d)} (hS : surfaceSet d n ω = S)
    (h : ∀ e ∈ (boxEdgesOutside d n S : Set (Sym2 (Site d))), ω e = ω' e) :
    surfaceSet d n ω' = S := by
  classical
  have hagree : ∀ a z : Site d, a ∈ box d n → z ∈ box d n →
      (a ∉ S ∨ z ∉ S) → ω s(a, z) = ω' s(a, z) := by
    intro a z ha hz hor
    exact h s(a, z) (by rw [Finset.mem_coe]; exact pair_mem_boxEdgesOutside ha hz hor)
  rw [← hS]
  ext x
  rw [mem_surfaceSet, mem_surfaceSet]
  by_cases hxbox : x ∈ box d n
  · simp only [hxbox, true_and]
    rw [connBdry_transfer hS hagree hxbox]
  · simp only [hxbox, false_and]





theorem surfaceEvent_dependsOn_outside (n : ℕ) (S : Finset (Site d)) :
    DependsOn ((surfaceEvent d n S).indicator (fun _ => (1 : ℝ)))
      ((boxEdgesOutside d n S : Set (Sym2 (Site d)))) := by
  intro ω ω' h
  have hiff : ω ∈ surfaceEvent d n S ↔ ω' ∈ surfaceEvent d n S := by
    constructor
    · intro hω; exact surfaceSet_congr_outside n hω h
    · intro hω'
      exact surfaceSet_congr_outside n hω' (fun e he => (h e he).symm)
  by_cases hω : ω ∈ surfaceEvent d n S
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (hiff.mp hω)]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun hc => hω (hiff.mpr hc))]















theorem surface_withinConn_indep (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) (S : Finset (Site d))
    (o x : Site d) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (withinConnEvent d (S : Set (Site d)) o x ∩ surfaceEvent d n S)
      = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (withinConnEvent d (S : Set (Site d)) o x)
        * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (surfaceEvent d n S) :=
  withinConn_indep p hp S o x (surfaceEvent d n S) (boxEdgesOutside d n S)
    (disjoint_boxEdgesOutside n S) (surfaceEvent_dependsOn_outside n S)

end Percolation

end StatMech
