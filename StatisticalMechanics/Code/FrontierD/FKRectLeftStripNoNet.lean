/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectAugmentedBarrierWindingMass
import Code.FrontierD.FKRectTorusNetMonotonicity



open SimpleGraph

namespace StatMech.FrontierD

noncomputable section



theorem fkRectTorusGraph_adj_crosses_column_cut
    (R : FKRectTorus) (right : Nat) (hright : right + 1 < R.width)
    {u v : R.Vertex} (hu : u.1.val ≤ right) (hv : right < v.1.val)
    (hadj : (fkRectTorusGraph R).Adj u v)
    (hnot : ¬ fkRectCrossesHorizontalSeam R s(u, v)) :
    u.1.val = right ∧ v.1.val = right + 1 := by
  rcases hadj with ⟨⟨b, x, y⟩, hedge⟩
  cases b
  · by_cases hy : Even y.val
    · simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
        hy, if_true] at hedge
      rcases Sym2.eq_iff.mp hedge with h | h
      · have hu' := congrArg (fun z => z.1.val) h.1
        have hv' := congrArg (fun z => z.1.val) h.2
        simp only [Prod.fst] at hu' hv'
        rw [fkRectCyclicPred_val] at hv'
        split at hv'
        · exfalso
          apply hnot
          rw [fkRectCrossesHorizontalSeam_mk]
          left
          have hwidth := R.width_pos
          constructor
          · omega
          · omega
        · omega
      · have hv' := congrArg (fun z => z.1.val) h.1
        have hu' := congrArg (fun z => z.1.val) h.2
        simp only [Prod.fst] at hu' hv'
        rw [fkRectCyclicPred_val] at hu'
        split at hu'
        · exfalso
          apply hnot
          rw [fkRectCrossesHorizontalSeam_mk]
          right
          have hwidth := R.width_pos
          constructor <;> omega
        · omega
    · simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
        hy, if_false] at hedge
      rcases Sym2.eq_iff.mp hedge with h | h
      · have hu' := congrArg (fun z => z.1.val) h.1
        have hv' := congrArg (fun z => z.1.val) h.2
        simp only [Prod.fst] at hu' hv'
        rw [fkRectCyclicPred_val] at hu'
        split at hu'
        · exfalso
          apply hnot
          rw [fkRectCrossesHorizontalSeam_mk]
          right
          have hwidth := R.width_pos
          constructor <;> omega
        · omega
      · have hv' := congrArg (fun z => z.1.val) h.1
        have hu' := congrArg (fun z => z.1.val) h.2
        simp only [Prod.fst] at hu' hv'
        rw [fkRectCyclicPred_val] at hv'
        split at hv'
        · exfalso
          apply hnot
          rw [fkRectCrossesHorizontalSeam_mk]
          left
          have hwidth := R.width_pos
          constructor <;> omega
        · omega
  · simp only [fkRectTorusIndexedEdge, if_true] at hedge
    rcases Sym2.eq_iff.mp hedge with h | h
    · have huv := congrArg (fun z => z.1.val) h.1
      have hvu := congrArg (fun z => z.1.val) h.2
      simp only [Prod.fst] at huv hvu
      omega
    · have huv := congrArg (fun z => z.1.val) h.1
      have hvu := congrArg (fun z => z.1.val) h.2
      simp only [Prod.fst] at huv hvu
      omega



def FKRectLeftStripTouchesRight (R : FKRectTorus)
    (omega : R.Configuration) (right : Nat) (v : R.Vertex) : Prop :=
  ∃ hv : v ∈ fkRectLeftStrip R right,
    ∃ y : fkRectLeftStrip R right,
      y.1.1.val = right ∧
        FKRectConnectedWithin R omega (fkRectLeftStrip R right)
          ⟨v, hv⟩ y



def fkRectLeftStripRightPotential (R : FKRectTorus)
    (omega : R.Configuration) (right : Nat) (v : R.Vertex) : Int := by
  classical
  exact if v ∈ fkRectLeftStrip R right then
    if FKRectLeftStripTouchesRight R omega right v then 1 else 0
  else 1

theorem fkRectLeftStripRightPotential_outside
    (R : FKRectTorus) (omega : R.Configuration) (right : Nat)
    (v : R.Vertex) (hv : v ∉ fkRectLeftStrip R right) :
    fkRectLeftStripRightPotential R omega right v = 1 := by
  simp [fkRectLeftStripRightPotential, hv]

theorem fkRectLeftStripRightPotential_right
    (R : FKRectTorus) (omega : R.Configuration) (right : Nat)
    {v : R.Vertex} (hv : v ∈ fkRectLeftStrip R right)
    (hcol : v.1.val = right) :
    fkRectLeftStripRightPotential R omega right v = 1 := by
  rw [fkRectLeftStripRightPotential, if_pos hv, if_pos]
  exact ⟨hv, ⟨v, hv⟩, hcol, SimpleGraph.Reachable.refl _⟩

theorem fkRectLeftStripRightPotential_left_eq_zero_of_noCrossing
    (R : FKRectTorus) (omega : R.Configuration) (right : Nat)
    (hno : omega ∈ fkRectNoLeftStripCrossingEvent R right)
    (v : R.Vertex) (hcol : v.1.val = 0) :
    fkRectLeftStripRightPotential R omega right v = 0 := by
  have hv : v ∈ fkRectLeftStrip R right := by
    change v.1.val ≤ right
    omega
  rw [fkRectLeftStripRightPotential, if_pos hv, if_neg]
  rintro ⟨_, y, hycol, hreach⟩
  apply hno
  exact ⟨⟨v, hv⟩, hcol, y, hycol,
    hreach⟩

theorem fkRectLeftStripRightPotential_eq_of_connected
    (R : FKRectTorus) (omega : R.Configuration) (right : Nat)
    {u v : R.Vertex} (hu : u ∈ fkRectLeftStrip R right)
    (hv : v ∈ fkRectLeftStrip R right)
    (huv : FKRectConnectedWithin R omega (fkRectLeftStrip R right)
      ⟨u, hu⟩ ⟨v, hv⟩) :
    fkRectLeftStripRightPotential R omega right u =
      fkRectLeftStripRightPotential R omega right v := by
  unfold fkRectLeftStripRightPotential
  rw [if_pos hu, if_pos hv]
  congr 1
  apply propext
  constructor
  · rintro ⟨_, y, hy, huy⟩
    exact ⟨hv, y, hy, huv.symm.trans huy⟩
  · rintro ⟨_, y, hy, hvy⟩
    exact ⟨hu, y, hy, huv.trans hvy⟩



theorem fkRectHorizontalSeamIncrement_eq_zero_of_not_crosses_leftStrip
    (R : FKRectTorus) (u v : R.Vertex)
    (hnot : ¬ fkRectCrossesHorizontalSeam R s(u, v)) :
    fkRectHorizontalSeamIncrement R u v = 0 := by
  unfold fkRectHorizontalSeamIncrement
  by_cases huv : u.1.val + 1 = R.width ∧ v.1.val = 0
  · exfalso
    apply hnot
    exact Or.inr ⟨huv.2, huv.1⟩
  · by_cases hvu : u.1.val = 0 ∧ v.1.val + 1 = R.width
    · exfalso
      apply hnot
      exact Or.inl hvu
    · simp [huv, hvu]



theorem fkRectHorizontalIncrement_eq_leftStripPotential_sub
    (R : FKRectTorus) (omega : R.Configuration)
    (right : Nat) (hright : right + 1 < R.width)
    (hno : omega ∈ fkRectNoLeftStripCrossingEvent R right)
    {u v : R.Vertex} (huv : (fkRectOpenGraph R omega).Adj u v) :
    fkRectHorizontalSeamIncrement R u v =
      fkRectLeftStripRightPotential R omega right u -
        fkRectLeftStripRightPotential R omega right v := by
  by_cases hseam : fkRectCrossesHorizontalSeam R s(u, v)
  · rw [fkRectCrossesHorizontalSeam_mk] at hseam
    rcases hseam with hseam | hseam
    · have huin : u ∈ fkRectLeftStrip R right := by
        change u.1.val ≤ right
        omega
      have hvout : v ∉ fkRectLeftStrip R right := by
        change ¬ v.1.val ≤ right
        omega
      rw [fkRectLeftStripRightPotential_left_eq_zero_of_noCrossing
          R omega right hno u hseam.1,
        fkRectLeftStripRightPotential_outside R omega right v hvout]
      unfold fkRectHorizontalSeamIncrement
      have hwidth := R.width_gt_two
      rw [if_neg (by omega), if_pos hseam]
      ring
    · have hvout : u ∉ fkRectLeftStrip R right := by
        change ¬ u.1.val ≤ right
        omega
      rw [fkRectLeftStripRightPotential_outside R omega right u hvout,
        fkRectLeftStripRightPotential_left_eq_zero_of_noCrossing
          R omega right hno v hseam.1]
      unfold fkRectHorizontalSeamIncrement
      have hwidth := R.width_gt_two
      rw [if_pos ⟨hseam.2, hseam.1⟩]
      ring
  · by_cases hu : u ∈ fkRectLeftStrip R right
    · by_cases hv : v ∈ fkRectLeftStrip R right
      · rw [fkRectHorizontalSeamIncrement_eq_zero_of_not_crosses_leftStrip
          R u v hseam]
        have hconn : FKRectConnectedWithin R omega
            (fkRectLeftStrip R right) ⟨u, hu⟩ ⟨v, hv⟩ :=
          SimpleGraph.Adj.reachable huv
        rw [fkRectLeftStripRightPotential_eq_of_connected
          R omega right hu hv hconn]
        ring
      · have hcut := fkRectTorusGraph_adj_crosses_column_cut R right hright
          (show u.1.val ≤ right from hu) (show right < v.1.val by
            change ¬ v.1.val ≤ right at hv
            omega) ⟨huv.choose, huv.choose_spec.2⟩ hseam
        rw [fkRectHorizontalSeamIncrement_eq_zero_of_not_crosses_leftStrip
          R u v hseam,
          fkRectLeftStripRightPotential_right R omega right hu hcut.1,
          fkRectLeftStripRightPotential_outside R omega right v hv]
        ring
    · by_cases hv : v ∈ fkRectLeftStrip R right
      · have hcut := fkRectTorusGraph_adj_crosses_column_cut R right hright
          (show v.1.val ≤ right from hv) (show right < u.1.val by
            change ¬ u.1.val ≤ right at hu
            omega) ⟨huv.choose, by
              simpa only [Sym2.eq_swap] using huv.choose_spec.2⟩ (by
                simpa only [Sym2.eq_swap] using hseam)
        rw [fkRectHorizontalSeamIncrement_eq_zero_of_not_crosses_leftStrip
          R u v hseam,
          fkRectLeftStripRightPotential_outside R omega right u hu,
          fkRectLeftStripRightPotential_right R omega right hv hcut.1]
        ring
      · rw [fkRectHorizontalSeamIncrement_eq_zero_of_not_crosses_leftStrip
          R u v hseam,
          fkRectLeftStripRightPotential_outside R omega right u hu,
          fkRectLeftStripRightPotential_outside R omega right v hv]
        ring



theorem fkRectClosedWalk_winding_fst_eq_zero_of_noLeftStripCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (right : Nat) (hright : right + 1 < R.width)
    (hno : omega ∈ fkRectNoLeftStripCrossingEvent R right)
    {x : R.Vertex} (p : (fkRectOpenGraph R omega).Walk x x) :
    (fkRectWalkWinding R p).1 = 0 := by
  have htel : ∀ {u v : R.Vertex}
      (w : (fkRectOpenGraph R omega).Walk u v),
      (fkRectWalkWinding R w).1 =
        fkRectLeftStripRightPotential R omega right u -
          fkRectLeftStripRightPotential R omega right v := by
    intro u v w
    induction w with
    | nil => simp [fkRectWalkWinding]
    | @cons a b c hab w ih =>
        simp only [fkRectWalkWinding, Prod.fst]
        rw [fkRectHorizontalIncrement_eq_leftStripPotential_sub
          R omega right hright hno hab, ih]
        ring
  simpa using htel p



theorem not_fkRectHasNet_of_noLeftStripCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (right : Nat) (hright : right + 1 < R.width)
    (hno : omega ∈ fkRectNoLeftStripCrossingEvent R right) :
    ¬ FKRectHasNet R omega := by
  rintro ⟨x, p, q, hind⟩
  unfold FKRectWindingIndependent at hind
  rw [fkRectClosedWalk_winding_fst_eq_zero_of_noLeftStripCrossing
      R omega right hright hno p,
    fkRectClosedWalk_winding_fst_eq_zero_of_noLeftStripCrossing
      R omega right hright hno q] at hind
  simp at hind

end

end StatMech.FrontierD
