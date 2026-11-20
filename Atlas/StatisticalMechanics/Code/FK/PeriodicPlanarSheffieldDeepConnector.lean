/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldOpenBoundarySource










open Filter MeasureTheory Set

namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



def PeriodicPlaneEmbedding.deepOpenExitedJoinedBoundaryArmEvent
    (E : PeriodicPlaneEmbedding P) (r R c d : Real)
    (L U : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  (E.infiniteOpenBoundaryConnectionTo r (L : Set V)
      (E.lowerBoundaryRayVertices r c) ∩
    E.infiniteOpenBoundaryConnectionTo r (U : Set V)
      (E.upperBoundaryRayVertices r d)) \
    E.halfPlanePairMergeErrorUnion R L U

theorem PeriodicPlaneEmbedding.deepOpenExitedJoinedBoundaryArmEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (r R c d : Real)
    (L U : Finset V) :
    MeasurableSet
      (E.deepOpenExitedJoinedBoundaryArmEvent r R c d L U) :=
  ((E.infiniteOpenBoundaryConnectionTo_measurableSet r (L : Set V)
      (E.lowerBoundaryRayVertices r c)).inter
    (E.infiniteOpenBoundaryConnectionTo_measurableSet r (U : Set V)
      (E.upperBoundaryRayVertices r d))).diff
    (E.halfPlanePairMergeErrorUnion_measurableSet R L U)



theorem PeriodicPlaneEmbedding.deepOpenExitedJoinedBoundaryArmEvent_witnesses
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {r R c d : Real} {L U : Finset V}
    (h : omega ∈ E.deepOpenExitedJoinedBoundaryArmEvent r R c d L U) :
    ∃ x ∈ L, (P.cluster omega x).Infinite ∧
      ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ z : V,
        P.graph.Adj b z ∧ z ∉ E.rightHalfPlaneVertices r ∧
        omega s(b, z) = true ∧
        omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b ∧
      ∃ y ∈ U, (P.cluster omega y).Infinite ∧
        ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ w : V,
          P.graph.Adj u w ∧ w ∉ E.rightHalfPlaneVertices r ∧
          omega s(u, w) = true ∧
          omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) y u ∧
          omega ∈ P.connectedWithinSet
            (E.rightHalfPlaneVertices R) x y := by
  rcases h.1.1 with
    ⟨x, hxL, hxInfinite, b, hbLower, _hbBoundary,
      z, hbz, hz, hbzOpen, hxb⟩
  rcases h.1.2 with
    ⟨y, hyU, hyInfinite, u, huUpper, _huBoundary,
      w, huw, hw, huwOpen, hyu⟩
  have hxy : omega ∈
      P.connectedWithinSet (E.rightHalfPlaneVertices R) x y := by
    by_contra hnot
    apply h.2
    rw [PeriodicPlaneEmbedding.halfPlanePairMergeErrorUnion]
    apply Set.mem_iUnion.2
    refine ⟨x, Set.mem_iUnion.2 ⟨hxL, ?_⟩⟩
    apply Set.mem_iUnion.2
    refine ⟨y, Set.mem_iUnion.2 ⟨hyU, ?_⟩⟩
    exact ⟨⟨hxInfinite, hyInfinite⟩, hnot⟩
  exact ⟨x, hxL, hxInfinite, b, hbLower, z, hbz, hz, hbzOpen, hxb,
    y, hyU, hyInfinite, u, huUpper, w, huw, hw, huwOpen, hyu, hxy⟩


theorem PeriodicPlaneEmbedding.deepOpenExitedJoinedBoundaryArmEvent_measureReal_ge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (r R c d : Real) (L U : Finset V) :
    mu.real (E.infiniteOpenBoundaryConnectionTo r (L : Set V)
        (E.lowerBoundaryRayVertices r c)) +
      mu.real (E.infiniteOpenBoundaryConnectionTo r (U : Set V)
        (E.upperBoundaryRayVertices r d)) -
      mu.real (E.halfPlanePairMergeErrorUnion R L U) - 1 ≤
        mu.real (E.deepOpenExitedJoinedBoundaryArmEvent r R c d L U) := by
  let A := E.infiniteOpenBoundaryConnectionTo r (L : Set V)
    (E.lowerBoundaryRayVertices r c)
  let B := E.infiniteOpenBoundaryConnectionTo r (U : Set V)
    (E.upperBoundaryRayVertices r d)
  let C := E.halfPlanePairMergeErrorUnion R L U
  have hthree := three_event_intersection_lower_bound mu
    (E.infiniteOpenBoundaryConnectionTo_measurableSet r (U : Set V)
      (E.upperBoundaryRayVertices r d))
    (E.halfPlanePairMergeErrorUnion_measurableSet R L U).compl
    (A := A) (B := B) (C := Cᶜ)
  have hC : mu.real Cᶜ = 1 - mu.real C := by
    rw [measureReal_compl
      (E.halfPlanePairMergeErrorUnion_measurableSet R L U), probReal_univ]
  rw [hC] at hthree
  change mu.real A + mu.real B - mu.real C - 1 ≤
    mu.real ((A ∩ B) \ C)
  convert hthree using 1 <;> ring



theorem PeriodicPlaneEmbedding.deepOpenExitedJoinedBoundaryArmEvent_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (r R c d : Nat → Real) (L U : Nat → Finset V)
    (hlower : Tendsto (fun n =>
      mu.real (E.infiniteOpenBoundaryConnectionTo (r n) (L n : Set V)
        (E.lowerBoundaryRayVertices (r n) (c n)))) atTop (nhds 1))
    (hupper : Tendsto (fun n =>
      mu.real (E.infiniteOpenBoundaryConnectionTo (r n) (U n : Set V)
        (E.upperBoundaryRayVertices (r n) (d n)))) atTop (nhds 1))
    (hmerge : Tendsto (fun n =>
      mu.real (E.halfPlanePairMergeErrorUnion (R n) (L n) (U n)))
        atTop (nhds 0)) :
    Tendsto (fun n => mu.real
      (E.deepOpenExitedJoinedBoundaryArmEvent
        (r n) (R n) (c n) (d n) (L n) (U n))) atTop (nhds 1) := by
  have hlowerBound : Tendsto (fun n =>
      mu.real (E.infiniteOpenBoundaryConnectionTo (r n) (L n : Set V)
          (E.lowerBoundaryRayVertices (r n) (c n))) +
        mu.real (E.infiniteOpenBoundaryConnectionTo (r n) (U n : Set V)
          (E.upperBoundaryRayVertices (r n) (d n))) -
        mu.real (E.halfPlanePairMergeErrorUnion (R n) (L n) (U n)) - 1)
      atTop (nhds 1) := by
    simpa using ((hlower.add hupper).sub hmerge).sub
      (tendsto_const_nhds (x := (1 : Real)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlowerBound tendsto_const_nhds
      (fun n => E.deepOpenExitedJoinedBoundaryArmEvent_measureReal_ge
        mu (r n) (R n) (c n) (d n) (L n) (U n))
      (fun _ => measureReal_le_one)

end StatMech.FK.PeriodicPlanar
