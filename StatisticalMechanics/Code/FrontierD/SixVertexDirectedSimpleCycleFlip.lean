/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDirectedCycleFlip
import Code.FrontierD.SixVertexPairTwoCycleRelation










namespace StatMech.FrontierD

noncomputable section

local instance sixVertexSimpleCycleFlipPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p


def SixVertexDirectedTorusEdge.Follows
    {T : EvenTorus} (edge : SixVertexDirectedTorusEdge T)
    (omega : SixVertexArrows T) : Prop :=
  match edge with
  | .horizontal base positive => omega.horizontal base = positive
  | .vertical base positive => omega.vertical base = positive


def SixVertexDirectedSimpleCycle.Follows
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (omega : SixVertexArrows T) : Prop :=
  forall i, (cycle.edge i).Follows omega


def SixVertexDirectedSimpleCycle.mask
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T) :
    SixVertexArrows T where
  horizontal base := decide
    (exists i, (cycle.edge i).physical = (false, base))
  vertical base := decide
    (exists i, (cycle.edge i).physical = (true, base))

@[simp] theorem SixVertexDirectedSimpleCycle.mask_horizontal
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (base : T.Vertex) :
    cycle.mask.horizontal base = true <->
      exists i, (cycle.edge i).physical = (false, base) := by
  simp [SixVertexDirectedSimpleCycle.mask]

@[simp] theorem SixVertexDirectedSimpleCycle.mask_vertical
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (base : T.Vertex) :
    cycle.mask.vertical base = true <->
      exists i, (cycle.edge i).physical = (true, base) := by
  simp [SixVertexDirectedSimpleCycle.mask]


theorem sixVertexDirectedTorusEdge_divergence
    {T : EvenTorus} (edge : SixVertexDirectedTorusEdge T) (v : T.Vertex) :
    edge.horizontalFlow
          (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) +
        edge.verticalFlow
          (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) -
        edge.horizontalFlow v - edge.verticalFlow v =
      (if edge.head = v then 1 else 0) -
        (if edge.tail = v then 1 else 0) := by
  have hx (base x : Fin T.width) :
      SixVertexArrows.cyclicPred T.width_pos x = base <->
        x = finitePeriodicSucc T.width_pos base := by
    constructor
    · intro h
      rw [← finitePeriodicSucc_cyclicPred T.width_pos x, h]
    · intro h
      rw [h, svCyclicPred_finitePeriodicSucc]
  have hy (base y : Fin T.height) :
      SixVertexArrows.cyclicPred T.height_pos y = base <->
        y = finitePeriodicSucc T.height_pos base := by
    constructor
    · intro h
      rw [← finitePeriodicSucc_cyclicPred T.height_pos y, h]
    · intro h
      rw [h, svCyclicPred_finitePeriodicSucc]
  have hx' (base x : Fin T.width) :
      base = SixVertexArrows.cyclicPred T.width_pos x <->
        x = finitePeriodicSucc T.width_pos base := by
    rw [eq_comm]
    exact hx base x
  have hy' (base y : Fin T.height) :
      base = SixVertexArrows.cyclicPred T.height_pos y <->
        y = finitePeriodicSucc T.height_pos base := by
    rw [eq_comm]
    exact hy base y
  rcases edge with ⟨base, positive⟩ | ⟨base, positive⟩
  · rcases base with ⟨column, row⟩
    rcases v with ⟨x, y⟩
    cases positive <;>
      simp [SixVertexDirectedTorusEdge.horizontalFlow,
        SixVertexDirectedTorusEdge.verticalFlow,
        SixVertexDirectedTorusEdge.head,
        SixVertexDirectedTorusEdge.tail, Prod.ext_iff,
        hx, hy, hx', hy'] <;>
      split <;> split <;> omega
  · rcases base with ⟨column, row⟩
    rcases v with ⟨x, y⟩
    cases positive <;>
      simp [SixVertexDirectedTorusEdge.horizontalFlow,
        SixVertexDirectedTorusEdge.verticalFlow,
        SixVertexDirectedTorusEdge.head,
        SixVertexDirectedTorusEdge.tail, Prod.ext_iff,
        hx, hy, hx', hy'] <;>
      split <;> split <;> omega


theorem SixVertexDirectedSimpleCycle.isCirculation
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T) :
    SixVertexTorusCirculation T cycle.horizontalFlow cycle.verticalFlow := by
  intro v
  have hdiv :
      (∑ i, ((cycle.edge i).horizontalFlow
            (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) +
          (cycle.edge i).verticalFlow
            (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) -
          (cycle.edge i).horizontalFlow v -
          (cycle.edge i).verticalFlow v)) = 0 := by
    rw [show (∑ i, ((cycle.edge i).horizontalFlow
            (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) +
          (cycle.edge i).verticalFlow
            (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) -
          (cycle.edge i).horizontalFlow v -
          (cycle.edge i).verticalFlow v)) =
        ∑ i, ((if (cycle.edge i).head = v then 1 else 0) -
          (if (cycle.edge i).tail = v then 1 else 0)) by
      apply Finset.sum_congr rfl
      intro i _
      exact sixVertexDirectedTorusEdge_divergence (cycle.edge i) v]
    rw [Finset.sum_sub_distrib]
    have hhead :
        (∑ i, if (cycle.edge i).head = v then (1 : Int) else 0) =
          ∑ i, if (cycle.edge i).tail = v then (1 : Int) else 0 := by
      calc
        (∑ i, if (cycle.edge i).head = v then (1 : Int) else 0) =
            ∑ i, if (cycle.edge (finitePeriodicSucc cycle.length_pos i)).tail = v
              then (1 : Int) else 0 := by
                apply Finset.sum_congr rfl
                intro i _
                rw [cycle.head_eq_next_tail]
        _ = ∑ i, if (cycle.edge i).tail = v then (1 : Int) else 0 := by
          exact (svFinitePeriodicSuccEquiv cycle.length_pos).sum_comp
            (fun i => if (cycle.edge i).tail = v then (1 : Int) else 0)
    rw [hhead, sub_self]
  unfold SixVertexDirectedSimpleCycle.horizontalFlow
    SixVertexDirectedSimpleCycle.verticalFlow
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hdiv
  omega


theorem sixVertexIceRule_of_flowConservation
    {T : EvenTorus} (omega : SixVertexArrows T)
    (hflow : SixVertexTorusCirculation T
      (fun v => (omega.horizontal v).toNat)
      (fun v => (omega.vertical v).toNat)) :
    omega.IceRule := by
  intro v
  have h := hflow v
  unfold SixVertexArrows.incomingCount
  generalize hw : omega.horizontal
    (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w at h ⊢
  generalize he : omega.horizontal v = e at h ⊢
  generalize hs : omega.vertical
    (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = s at h ⊢
  generalize hn : omega.vertical v = n at h ⊢
  cases w <;> cases e <;> cases s <;> cases n
  all_goals norm_num [hw, he, hs, hn] at h
  all_goals norm_num [hw, he, hs, hn]



theorem SixVertexDirectedSimpleCycle.flip_horizontal_toNat
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (omega : SixVertexArrows T) (hfollows : cycle.Follows omega)
    (base : T.Vertex) :
    ((sixVertexTorusFlip cycle.mask omega).horizontal base).toNat =
      (omega.horizontal base).toNat - cycle.horizontalFlow base := by
  classical
  by_cases hsupport : exists i,
      (cycle.edge i).physical = (false, base)
  · obtain ⟨index, hindex⟩ := hsupport
    have hedge : exists positive,
        cycle.edge index = .horizontal base positive := by
      cases h : cycle.edge index with
      | horizontal edgeBase positive =>
          simp [h, SixVertexDirectedTorusEdge.physical] at hindex
          exact ⟨positive, by simpa [hindex] using h⟩
      | vertical edgeBase positive =>
          simp [h, SixVertexDirectedTorusEdge.physical] at hindex
    obtain ⟨positive, hedge⟩ := hedge
    have hother : forall other,
        other ∈ Finset.univ -> other ≠ index ->
          (cycle.edge other).horizontalFlow base = 0 := by
      intro other _ hne
      cases h : cycle.edge other with
      | horizontal edgeBase otherPositive =>
          have hbase : edgeBase ≠ base := by
            intro heq
            apply hne
            apply cycle.physical_injective
            simp [h, hedge, heq,
              SixVertexDirectedTorusEdge.physical]
          simp [h, SixVertexDirectedTorusEdge.horizontalFlow, hbase,
            Ne.symm hbase]
      | vertical edgeBase otherPositive =>
          simp [h, SixVertexDirectedTorusEdge.horizontalFlow]
    have hflow : cycle.horizontalFlow base =
        (cycle.edge index).horizontalFlow base := by
      unfold SixVertexDirectedSimpleCycle.horizontalFlow
      exact Finset.sum_eq_single index hother (by simp)
    have hsource : omega.horizontal base = positive := by
      simpa [SixVertexDirectedSimpleCycle.Follows,
        SixVertexDirectedTorusEdge.Follows, hedge] using hfollows index
    rw [hflow, hedge]
    have hmask : cycle.mask.horizontal base = true := by
      exact (cycle.mask_horizontal base).2 ⟨index, hindex⟩
    rw [sixVertexTorusFlip_horizontal_selected cycle.mask omega base hmask]
    cases positive <;>
      simp [hsource,
        SixVertexDirectedTorusEdge.horizontalFlow]
  · have hflow : cycle.horizontalFlow base = 0 := by
      unfold SixVertexDirectedSimpleCycle.horizontalFlow
      apply Finset.sum_eq_zero
      intro index _
      cases h : cycle.edge index with
      | horizontal edgeBase positive =>
          have hbase : edgeBase ≠ base := by
            intro heq
            apply hsupport
            exact ⟨index, by
              simp [h, heq, SixVertexDirectedTorusEdge.physical]⟩
          simp [h, SixVertexDirectedTorusEdge.horizontalFlow, hbase,
            Ne.symm hbase]
      | vertical edgeBase positive =>
          simp [h, SixVertexDirectedTorusEdge.horizontalFlow]
    have hmask : cycle.mask.horizontal base = false := by
      simp [SixVertexDirectedSimpleCycle.mask, hsupport]
    rw [sixVertexTorusFlip_horizontal_unselected cycle.mask omega base hmask]
    simp [hflow]


theorem SixVertexDirectedSimpleCycle.flip_vertical_toNat
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (omega : SixVertexArrows T) (hfollows : cycle.Follows omega)
    (base : T.Vertex) :
    ((sixVertexTorusFlip cycle.mask omega).vertical base).toNat =
      (omega.vertical base).toNat - cycle.verticalFlow base := by
  classical
  by_cases hsupport : exists i,
      (cycle.edge i).physical = (true, base)
  · obtain ⟨index, hindex⟩ := hsupport
    have hedge : exists positive,
        cycle.edge index = .vertical base positive := by
      cases h : cycle.edge index with
      | horizontal edgeBase positive =>
          simp [h, SixVertexDirectedTorusEdge.physical] at hindex
      | vertical edgeBase positive =>
          simp [h, SixVertexDirectedTorusEdge.physical] at hindex
          exact ⟨positive, by simpa [hindex] using h⟩
    obtain ⟨positive, hedge⟩ := hedge
    have hother : forall other,
        other ∈ Finset.univ -> other ≠ index ->
          (cycle.edge other).verticalFlow base = 0 := by
      intro other _ hne
      cases h : cycle.edge other with
      | horizontal edgeBase otherPositive =>
          simp [h, SixVertexDirectedTorusEdge.verticalFlow]
      | vertical edgeBase otherPositive =>
          have hbase : edgeBase ≠ base := by
            intro heq
            apply hne
            apply cycle.physical_injective
            simp [h, hedge, heq,
              SixVertexDirectedTorusEdge.physical]
          simp [h, SixVertexDirectedTorusEdge.verticalFlow, hbase,
            Ne.symm hbase]
    have hflow : cycle.verticalFlow base =
        (cycle.edge index).verticalFlow base := by
      unfold SixVertexDirectedSimpleCycle.verticalFlow
      exact Finset.sum_eq_single index hother (by simp)
    have hsource : omega.vertical base = positive := by
      simpa [SixVertexDirectedSimpleCycle.Follows,
        SixVertexDirectedTorusEdge.Follows, hedge] using hfollows index
    rw [hflow, hedge]
    have hmask : cycle.mask.vertical base = true := by
      exact (cycle.mask_vertical base).2 ⟨index, hindex⟩
    rw [sixVertexTorusFlip_vertical_selected cycle.mask omega base hmask]
    cases positive <;>
      simp [hsource,
        SixVertexDirectedTorusEdge.verticalFlow]
  · have hflow : cycle.verticalFlow base = 0 := by
      unfold SixVertexDirectedSimpleCycle.verticalFlow
      apply Finset.sum_eq_zero
      intro index _
      cases h : cycle.edge index with
      | horizontal edgeBase positive =>
          simp [h, SixVertexDirectedTorusEdge.verticalFlow]
      | vertical edgeBase positive =>
          have hbase : edgeBase ≠ base := by
            intro heq
            apply hsupport
            exact ⟨index, by
              simp [h, heq, SixVertexDirectedTorusEdge.physical]⟩
          simp [h, SixVertexDirectedTorusEdge.verticalFlow, hbase,
            Ne.symm hbase]
    have hmask : cycle.mask.vertical base = false := by
      simp [SixVertexDirectedSimpleCycle.mask, hsupport]
    rw [sixVertexTorusFlip_vertical_unselected cycle.mask omega base hmask]
    simp [hflow]


theorem SixVertexDirectedSimpleCycle.flip_ice
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (omega : SixVertexArrows T) (homega : omega.IceRule)
    (hfollows : cycle.Follows omega) :
    (sixVertexTorusFlip cycle.mask omega).IceRule := by
  apply sixVertexIceRule_of_flowConservation
  have hsource : SixVertexTorusCirculation T
      (fun v => (omega.horizontal v).toNat)
      (fun v => (omega.vertical v).toNat) :=
    sixVertexFlowConservation_of_ice omega homega
  have htarget := hsource.sub cycle.isCirculation
  simpa only [cycle.flip_horizontal_toNat omega hfollows,
    cycle.flip_vertical_toNat omega hfollows] using htarget



theorem SixVertexDirectedSimpleCycle.flip_seamDelta
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (omega : SixVertexArrows T) (hfollows : cycle.Follows omega) :
    sixVertexTorusFlipSeamDelta cycle.mask omega =
      -∑ column : Fin T.width,
        cycle.verticalFlow (column, svFinLast T.height_pos) := by
  unfold sixVertexTorusFlipSeamDelta
  simp only [Int.ofNat_eq_natCast]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro column _
  rw [cycle.flip_vertical_toNat omega hfollows]
  ring




def SixVertexAtMostTwoCycleFamily.singletonCycle
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T) :
    SixVertexAtMostTwoCycleFamily T where
  count := 1
  count_le_two := by omega
  cycle := fun _ => cycle
  tail_disjoint := by
    intro first second hne
    fin_cases first
    fin_cases second
    simp at hne

@[simp] theorem SixVertexAtMostTwoCycleFamily.singletonCycle_horizontalFlow
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (base : T.Vertex) :
    (SixVertexAtMostTwoCycleFamily.singletonCycle cycle).horizontalFlow base =
      cycle.horizontalFlow base := by
  simp [SixVertexAtMostTwoCycleFamily.singletonCycle,
    SixVertexAtMostTwoCycleFamily.horizontalFlow]

@[simp] theorem SixVertexAtMostTwoCycleFamily.singletonCycle_verticalFlow
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (base : T.Vertex) :
    (SixVertexAtMostTwoCycleFamily.singletonCycle cycle).verticalFlow base =
      cycle.verticalFlow base := by
  simp [SixVertexAtMostTwoCycleFamily.singletonCycle,
    SixVertexAtMostTwoCycleFamily.verticalFlow]



theorem SixVertexDirectedSimpleCycle.flip_first_pair_related
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (omega eta : SixVertexArrows T) (hfollows : cycle.Follows omega) :
    sixVertexPairAtMostTwoCycleRelated (omega, eta)
      (sixVertexTorusFlip cycle.mask omega, eta) := by
  refine ⟨SixVertexAtMostTwoCycleFamily.singletonCycle cycle, false, ?_, ?_⟩
  · funext base
    unfold sixVertexPairUnionHorizontalDelta sixVertexPairUnionHorizontal
    rw [cycle.flip_horizontal_toNat omega hfollows]
    simp
  · funext base
    unfold sixVertexPairUnionVerticalDelta sixVertexPairUnionVertical
    rw [cycle.flip_vertical_toNat omega hfollows]
    simp



theorem SixVertexDirectedSimpleCycle.flip_second_pair_related
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (omega eta : SixVertexArrows T) (hfollows : cycle.Follows eta) :
    sixVertexPairAtMostTwoCycleRelated (omega, eta)
      (omega, sixVertexTorusFlip cycle.mask eta) := by
  refine ⟨SixVertexAtMostTwoCycleFamily.singletonCycle cycle, false, ?_, ?_⟩
  · funext base
    unfold sixVertexPairUnionHorizontalDelta sixVertexPairUnionHorizontal
    rw [cycle.flip_horizontal_toNat eta hfollows]
    simp
  · funext base
    unfold sixVertexPairUnionVerticalDelta sixVertexPairUnionVertical
    rw [cycle.flip_vertical_toNat eta hfollows]
    simp



def SixVertexAtMostTwoCycleFamily.twoCycles
    {T : EvenTorus} (first second : SixVertexDirectedSimpleCycle T)
    (hdisjoint : forall a b,
      (first.edge a).tail != (second.edge b).tail) :
    SixVertexAtMostTwoCycleFamily T where
  count := 2
  count_le_two := by omega
  cycle := ![first, second]
  tail_disjoint := by
    intro i j hne a b
    fin_cases i <;> fin_cases j
    · simp at hne
    · exact hdisjoint a b
    · simpa [bne_comm] using hdisjoint b a
    · simp at hne

@[simp] theorem SixVertexAtMostTwoCycleFamily.twoCycles_horizontalFlow
    {T : EvenTorus} (first second : SixVertexDirectedSimpleCycle T)
    (hdisjoint : forall a b,
      (first.edge a).tail != (second.edge b).tail)
    (base : T.Vertex) :
    (SixVertexAtMostTwoCycleFamily.twoCycles first second hdisjoint).horizontalFlow
        base =
      first.horizontalFlow base + second.horizontalFlow base := by
  unfold SixVertexAtMostTwoCycleFamily.horizontalFlow
  simp only [SixVertexAtMostTwoCycleFamily.twoCycles]
  change (∑ x : Fin 2, (![first, second] x).horizontalFlow base) = _
  rw [Fin.sum_univ_two]
  rfl

@[simp] theorem SixVertexAtMostTwoCycleFamily.twoCycles_verticalFlow
    {T : EvenTorus} (first second : SixVertexDirectedSimpleCycle T)
    (hdisjoint : forall a b,
      (first.edge a).tail != (second.edge b).tail)
    (base : T.Vertex) :
    (SixVertexAtMostTwoCycleFamily.twoCycles first second hdisjoint).verticalFlow
        base =
      first.verticalFlow base + second.verticalFlow base := by
  unfold SixVertexAtMostTwoCycleFamily.verticalFlow
  simp only [SixVertexAtMostTwoCycleFamily.twoCycles]
  change (∑ x : Fin 2, (![first, second] x).verticalFlow base) = _
  rw [Fin.sum_univ_two]
  rfl



theorem sixVertexDirectedSimpleCycles_flip_pair_related
    {T : EvenTorus} (first second : SixVertexDirectedSimpleCycle T)
    (omega eta : SixVertexArrows T)
    (hfirst : first.Follows omega) (hsecond : second.Follows eta)
    (hdisjoint : forall a b,
      (first.edge a).tail != (second.edge b).tail) :
    sixVertexPairAtMostTwoCycleRelated (omega, eta)
      (sixVertexTorusFlip first.mask omega,
        sixVertexTorusFlip second.mask eta) := by
  refine ⟨SixVertexAtMostTwoCycleFamily.twoCycles first second hdisjoint,
    false, ?_, ?_⟩
  · funext base
    unfold sixVertexPairUnionHorizontalDelta sixVertexPairUnionHorizontal
    rw [first.flip_horizontal_toNat omega hfirst,
      second.flip_horizontal_toNat eta hsecond]
    simp
    ring
  · funext base
    unfold sixVertexPairUnionVerticalDelta sixVertexPairUnionVertical
    rw [first.flip_vertical_toNat omega hfirst,
      second.flip_vertical_toNat eta hsecond]
    simp
    ring

end

end StatMech.FrontierD
