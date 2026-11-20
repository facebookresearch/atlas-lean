/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly










open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

theorem PeriodicPlaneEmbedding.axisSwap_bottomBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisSwap.rectBottomBoundaryVertices a b c d =
      E.rectLeftBoundaryVertices c d a b := by
  ext x
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨by simpa only [E.axisSwap_rectVertices] using hx, y, hxy, hy⟩
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨by simpa only [E.axisSwap_rectVertices] using hx, y, hxy, hy⟩

theorem PeriodicPlaneEmbedding.axisSwap_topBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisSwap.rectTopBoundaryVertices a b c d =
      E.rectRightBoundaryVertices c d a b := by
  ext x
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨by simpa only [E.axisSwap_rectVertices] using hx, y, hxy, hy⟩
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨by simpa only [E.axisSwap_rectVertices] using hx, y, hxy, hy⟩

theorem PeriodicPlaneEmbedding.axisSwap_bottomBoundaryEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (S : Set V) :
    E.axisSwap.rectSideConnectionEvent a b c d S
        (E.axisSwap.rectBottomBoundaryVertices a b c d) =
      E.rectSideConnectionEvent c d a b S
        (E.rectLeftBoundaryVertices c d a b) := by
  change P.infiniteSetConnectionWithin
    (E.axisSwap.rectVertices a b c d) S
      (E.axisSwap.rectBottomBoundaryVertices a b c d) = _
  rw [E.axisSwap_rectVertices, E.axisSwap_bottomBoundaryVertices]
  rfl

theorem PeriodicPlaneEmbedding.axisSwap_topBoundaryEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (S : Set V) :
    E.axisSwap.rectSideConnectionEvent a b c d S
        (E.axisSwap.rectTopBoundaryVertices a b c d) =
      E.rectSideConnectionEvent c d a b S
        (E.rectRightBoundaryVertices c d a b) := by
  change P.infiniteSetConnectionWithin
    (E.axisSwap.rectVertices a b c d) S
      (E.axisSwap.rectTopBoundaryVertices a b c d) = _
  rw [E.axisSwap_rectVertices, E.axisSwap_topBoundaryVertices]
  rfl



theorem PeriodicPlanarDualPair.exists_common_nat_edgeArc_displacement_bound
    (D : PeriodicPlanarDualPair P Pdual) :
    ∃ B : Nat, 0 < B ∧
      (∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
        |D.primalEmbedding.coordinates
          (D.primalEmbedding.edgeArc hxy t -
            D.primalEmbedding.vertex x) i| ≤ (B : Real)) ∧
      (∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
        |D.dualEmbedding.coordinates
          (D.dualEmbedding.edgeArc hxy t -
            D.dualEmbedding.vertex x) i| ≤ (B : Real)) := by
  obtain ⟨R, hRpos, hRp, hRd⟩ :=
    D.exists_common_edgeArc_displacement_bound
  obtain ⟨B, hBR⟩ := exists_nat_gt R
  have hBpos : 0 < B := by
    by_contra hB
    have hB0 : B = 0 := Nat.eq_zero_of_not_pos hB
    subst B
    norm_num at hBR
    linarith
  refine ⟨B, hBpos, ?_, ?_⟩
  · intro x y hxy t i
    exact (hRp hxy t i).trans hBR.le
  · intro x y hxy t i
    exact (hRd hxy t i).trans hBR.le


def sheffieldMacroIncrement (B : Nat) : Nat := 8 * B + 1

theorem sheffieldMacroIncrement_gt_eight_mul (B : Nat) :
    (8 : Real) * B < sheffieldMacroIncrement B := by
  simp [sheffieldMacroIncrement]




def sheffieldMacroArrayCoordinates (B T : Nat)
    (a0 b0 c0 d0 : Nat → Real) (n k : Nat) : Real × Real × Real × Real :=
  (a0 n - 4 * B * k,
    b0 n + 4 * B * k,
    c0 n + 4 * B * k,
    d0 n + T * k)




theorem sheffieldMacroArrayCoordinates_adjacent
    (B T : Nat) (a0 b0 c0 d0 : Nat → Real) (n k : Nat) :
    let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
    (q n (k + 1)).1 + 4 * B = (q n k).1 ∧
    (q n (k + 1)).2.1 - 4 * B = (q n k).2.1 ∧
    (q n (k + 1)).2.2.1 = (q n k).2.2.1 + 4 * B ∧
    (q n (k + 1)).2.2.2 =
      (q n k).2.2.2 - 4 * B + (T + 4 * B : Nat) := by
  dsimp only [sheffieldMacroArrayCoordinates]
  push_cast
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring



theorem sheffieldMacroArrayCoordinates_spans
    (B T : Nat) (hT : 8 * B < T)
    (a0 b0 c0 d0 : Nat → Real)
    (hspanX0 : ∀ n, a0 n + 5 * B < b0 n - 5 * B)
    (hspanY0 : ∀ n, c0 n + 5 * B < d0 n - 5 * B) :
    let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
    (∀ n k, (q n k).1 + 5 * B < (q n k).2.1 - 5 * B) ∧
    ∀ n k, (q n k).2.2.1 + 5 * B < (q n k).2.2.2 - 5 * B := by
  dsimp only [sheffieldMacroArrayCoordinates]
  constructor
  · intro n k
    have h := hspanX0 n
    have hk : (0 : Real) ≤ k := by positivity
    have hBk : (0 : Real) ≤ (B : Real) * k := mul_nonneg (by positivity) hk
    push_cast at h ⊢
    nlinarith
  · intro n k
    have h := hspanY0 n
    have hTR : (8 : Real) * B < T := by exact_mod_cast hT
    have hk : (0 : Real) ≤ k := by positivity
    push_cast
    nlinarith [mul_nonneg (show (0 : Real) ≤ (T : Real) - 4 * B by
      linarith) hk]



def PeriodicPlaneEmbedding.finiteAdjacentHeightJoinedVerticalEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (t : Int)
    (L U : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  (E.rectSideConnectionEvent a b c d (L : Set V)
      (E.rectBottomBoundaryVertices a b c d) ∩
    E.rectSideConnectionEvent a b (c + t) (d + t) (U : Set V)
      (E.rectTopBoundaryVertices a b (c + t) (d + t))) \
    E.rectanglePairMergeErrorUnion a b c (d + t) L U

theorem PeriodicPlaneEmbedding.finiteAdjacentHeightJoinedVerticalEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (t : Int)
    (L U : Finset V) :
    MeasurableSet
      (E.finiteAdjacentHeightJoinedVerticalEvent a b c d t L U) :=
  ((E.rectSideConnectionEvent_measurableSet a b c d (L : Set V)
      (E.rectBottomBoundaryVertices a b c d)).inter
    (E.rectSideConnectionEvent_measurableSet a b (c + t) (d + t)
      (U : Set V) (E.rectTopBoundaryVertices a b (c + t) (d + t)))).diff
    (E.rectanglePairMergeErrorUnion_measurableSet a b c (d + t) L U)


theorem PeriodicPlaneEmbedding.finiteAdjacentHeightJoinedVerticalEvent_subset_verticalCrossing
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (t : Int)
    (ht : 0 ≤ t) (L U : Finset V) :
    E.finiteAdjacentHeightJoinedVerticalEvent a b c d t L U ⊆
      E.verticalCrossingEvent a b c (d + t) := by
  intro omega homega
  obtain ⟨x, hxL, hxinf, xb, hxbBottom, hxxb⟩ := homega.1.1
  obtain ⟨y, hyU, hyinf, yt, hytTop, hyyt⟩ := homega.1.2
  have hxy : omega ∈
      P.connectedWithinSet (E.rectVertices a b c (d + t)) x y := by
    by_contra hnot
    apply homega.2
    apply Set.mem_iUnion.2
    refine ⟨x, Set.mem_iUnion.2 ⟨hxL, Set.mem_iUnion.2 ⟨y,
      Set.mem_iUnion.2 ⟨hyU, ?_⟩⟩⟩⟩
    exact ⟨⟨hxinf, hyinf⟩, hnot⟩
  obtain ⟨qxb, hqxb⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxxb
  obtain ⟨qxy, hqxy⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxy
  obtain ⟨qyt, hqyt⟩ := P.connectedWithinSet_exists_openSubgraphWalk hyyt
  let q : (P.openSubgraph omega).Walk xb yt :=
    qxb.reverse.append (qxy.append qyt)
  have htR : (0 : Real) ≤ t := by exact_mod_cast ht
  have hRsubset : E.rectVertices a b c d ⊆
      E.rectVertices a b c (d + t) :=
    E.rectVertices_mono le_rfl le_rfl le_rfl (by linarith)
  have hR'subset : E.rectVertices a b (c + t) (d + t) ⊆
      E.rectVertices a b c (d + t) :=
    E.rectVertices_mono le_rfl le_rfl (by linarith) le_rfl
  have hqRect : ∀ v ∈ q.support, v ∈ E.rectVertices a b c (d + t) := by
    intro v hv
    dsimp only [q] at hv
    rw [SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_reverse] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hRsubset (hqxb v (by simpa using hv))
    · rw [SimpleGraph.Walk.support_append] at hv
      rcases List.mem_append.mp (List.mem_of_mem_tail hv) with hv | hv
      · exact hqxy v hv
      · exact hR'subset (hqyt v (List.mem_of_mem_tail hv))
  have hxbRect := hqRect xb q.start_mem_support
  have hytRect := hqRect yt q.end_mem_support
  have hbottom : E.rectBottomBoundary a b c (d + t) ⟨xb, hxbRect⟩ := by
    exact hxbBottom.2
  have htop : E.rectTopBoundary a b c (d + t) ⟨yt, hytRect⟩ := by
    exact hytTop.2
  have hreach :
      ((P.openSubgraph omega).induce (E.rectVertices a b c (d + t))).Reachable
        ⟨xb, hxbRect⟩ ⟨yt, hytRect⟩ :=
    ⟨q.induce (E.rectVertices a b c (d + t)) hqRect⟩
  change E.rectRestrict a b c (d + t) omega ∈
    E.finiteVerticalCrossing a b c (d + t)
  refine ⟨⟨xb, hxbRect⟩, ⟨yt, hytRect⟩, hbottom, htop, ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hreach


theorem PeriodicPlaneEmbedding.adjacentHeightVerticalCrossing_measureReal_ge_side_mul_sub_mergeError
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (t : Int) (ht : 0 ≤ t)
    (L U : Finset V) :
    mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectBottomBoundaryVertices a b c d)) *
      mu.real (E.rectSideConnectionEvent a b (c + t) (d + t) (U : Set V)
        (E.rectTopBoundaryVertices a b (c + t) (d + t))) -
      mu.real (E.rectanglePairMergeErrorUnion a b c (d + t) L U) ≤
        mu.real (E.verticalCrossingEvent a b c (d + t)) := by
  let A := E.rectSideConnectionEvent a b c d (L : Set V)
    (E.rectBottomBoundaryVertices a b c d)
  let T := E.rectSideConnectionEvent a b (c + t) (d + t) (U : Set V)
    (E.rectTopBoundaryVertices a b (c + t) (d + t))
  let M := E.rectanglePairMergeErrorUnion a b c (d + t) L U
  have hinter : mu.real A * mu.real T ≤ mu.real (A ∩ T) :=
    hFKG A T
      (E.rectSideConnectionEvent_measurableSet a b c d (L : Set V)
        (E.rectBottomBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b (c + t) (d + t)
        (U : Set V) (E.rectTopBoundaryVertices a b (c + t) (d + t)))
      (E.rectSideConnectionEvent_isIncreasing a b c d (L : Set V)
        (E.rectBottomBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b (c + t) (d + t)
        (U : Set V) (E.rectTopBoundaryVertices a b (c + t) (d + t)))
  have hdiff : mu.real (A ∩ T) - mu.real M ≤
      mu.real ((A ∩ T) \ M) := le_measureReal_diff
  have hjoined : mu.real ((A ∩ T) \ M) ≤
      mu.real (E.verticalCrossingEvent a b c (d + t)) :=
    measureReal_mono
      (E.finiteAdjacentHeightJoinedVerticalEvent_subset_verticalCrossing
        a b c d t ht L U)
  dsimp only [A, T, M] at hinter hdiff hjoined ⊢
  linarith





theorem PeriodicPlaneEmbedding.adjacentHeightVerticalCrossing_ge_approxPreferredSide_transfer
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (a b c d : Real) (t : Int) (ht : 0 ≤ t)
    (L R : Finset V) (epsilon : Real)
    (hOpposite :
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectBottomBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectTopBoundaryVertices a b c d)) + epsilon) :
    let U := R.image (P.shift (verticalShift t))
    let A := mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
      (E.rectBottomBoundaryVertices a b c d))
    let H := mu.real (P.setHitsInfinite (R : Set V))
    let Mtransfer := mu.real (E.rectanglePairMergeErrorUnion a b c d L R)
    let Mjoin := mu.real
      (E.rectanglePairMergeErrorUnion a b c (d + t) L U)
    A * (H * A - Mtransfer - epsilon) - Mjoin ≤
      mu.real (E.verticalCrossingEvent a b c (d + t)) := by
  dsimp only
  let U := R.image (P.shift (verticalShift t))
  have htransfer := E.rectSide_measureReal_ge_hits_mul_side_sub_mergeError
    mu hFKG a b c d L R (E.rectBottomBoundaryVertices a b c d)
  have htopR :
      mu.real (P.setHitsInfinite (R : Set V)) *
          mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
            (E.rectBottomBoundaryVertices a b c d)) -
          mu.real (E.rectanglePairMergeErrorUnion a b c d L R) - epsilon ≤
        mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
          (E.rectTopBoundaryVertices a b c d)) := by
    linarith
  have htranslate := E.rectTopConnection_translate_measureReal_eq
    mu hTI (verticalShift t) a b c d (R : Set V)
  have htopU :
      mu.real (P.setHitsInfinite (R : Set V)) *
          mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
            (E.rectBottomBoundaryVertices a b c d)) -
          mu.real (E.rectanglePairMergeErrorUnion a b c d L R) - epsilon ≤
        mu.real (E.rectSideConnectionEvent a b (c + t) (d + t)
          (U : Set V) (E.rectTopBoundaryVertices a b (c + t) (d + t))) := by
    have htranslate' :
        mu.real (E.rectSideConnectionEvent a b (c + t) (d + t)
          (U : Set V) (E.rectTopBoundaryVertices a b (c + t) (d + t))) =
        mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
          (E.rectTopBoundaryVertices a b c d)) := by
      simpa [U, verticalShift] using htranslate
    rwa [htranslate']
  have hAnonneg : 0 ≤
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectBottomBoundaryVertices a b c d)) := measureReal_nonneg
  have hmul := mul_le_mul_of_nonneg_left htopU hAnonneg
  have hcross :=
    E.adjacentHeightVerticalCrossing_measureReal_ge_side_mul_sub_mergeError
      mu hFKG a b c d t ht L U
  dsimp only [U] at hcross ⊢
  nlinarith





theorem PeriodicPlaneEmbedding.outwardVerticalCrossing_ge_approxPreferredSide_transfer
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (a b c d : Real) (pad : Int) (hpad : 0 ≤ pad)
    (L R : Finset V) (epsilon : Real)
    (hOpposite :
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectBottomBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectTopBoundaryVertices a b c d)) + epsilon) :
    let Ldown := L.image (P.shift (verticalShift (-pad)))
    let Rdown := R.image (P.shift (verticalShift (-pad)))
    let Rup := R.image (P.shift (verticalShift pad))
    let A := mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
      (E.rectBottomBoundaryVertices a b c d))
    let H := mu.real (P.setHitsInfinite (R : Set V))
    let Mtransfer := mu.real
      (E.rectanglePairMergeErrorUnion a b (c - pad) (d - pad) Ldown Rdown)
    let Mjoin := mu.real
      (E.rectanglePairMergeErrorUnion a b (c - pad) (d + pad) Ldown Rup)
    A * (H * A - Mtransfer - epsilon) - Mjoin ≤
      mu.real (E.verticalCrossingEvent a b (c - pad) (d + pad)) := by
  dsimp only
  let Ldown := L.image (P.shift (verticalShift (-pad)))
  let Rdown := R.image (P.shift (verticalShift (-pad)))
  let Rup := R.image (P.shift (verticalShift pad))
  have hbottomTranslate := E.rectBottomConnection_translate_measureReal_eq
    mu hTI (verticalShift (-pad)) a b c d (L : Set V)
  have htopTranslate := E.rectTopConnection_translate_measureReal_eq
    mu hTI (verticalShift (-pad)) a b c d (R : Set V)
  have hbottomEq :
      mu.real (E.rectSideConnectionEvent a b (c - pad) (d - pad)
        (Ldown : Set V) (E.rectBottomBoundaryVertices a b
          (c - pad) (d - pad))) =
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectBottomBoundaryVertices a b c d)) := by
    simpa [Ldown, verticalShift] using hbottomTranslate
  have hbottomREq :
      mu.real (E.rectSideConnectionEvent a b (c - pad) (d - pad)
        (Rdown : Set V) (E.rectBottomBoundaryVertices a b
          (c - pad) (d - pad))) =
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectBottomBoundaryVertices a b c d)) := by
    have h := E.rectBottomConnection_translate_measureReal_eq
      mu hTI (verticalShift (-pad)) a b c d (R : Set V)
    simpa [Rdown, verticalShift] using h
  have htopREq :
      mu.real (E.rectSideConnectionEvent a b (c - pad) (d - pad)
        (Rdown : Set V) (E.rectTopBoundaryVertices a b
          (c - pad) (d - pad))) =
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectTopBoundaryVertices a b c d)) := by
    simpa [Rdown, verticalShift] using htopTranslate
  have hOppositeDown :
      mu.real (E.rectSideConnectionEvent a b (c - pad) (d - pad)
        (Rdown : Set V) (E.rectBottomBoundaryVertices a b
          (c - pad) (d - pad))) ≤
      mu.real (E.rectSideConnectionEvent a b (c - pad) (d - pad)
        (Rdown : Set V) (E.rectTopBoundaryVertices a b
          (c - pad) (d - pad))) + epsilon := by
    rw [hbottomREq, htopREq]
    exact hOpposite
  have hRup : Rdown.image (P.shift (verticalShift (2 * pad))) = Rup := by
    ext x
    simp only [Rdown, Rup, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨u, hu, ?_⟩
      rw [← P.shift_add]
      congr 2
      ext i
      fin_cases i <;> simp [verticalShift] <;> omega
    · rintro ⟨u, hu, rfl⟩
      refine ⟨P.shift (verticalShift (-pad)) u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add]
      congr 2
      ext i
      fin_cases i <;> simp [verticalShift] <;> omega
  have hraw :=
    E.adjacentHeightVerticalCrossing_ge_approxPreferredSide_transfer
      mu hFKG hTI a b (c - pad) (d - pad) (2 * pad)
      (mul_nonneg (by norm_num) hpad) Ldown Rdown epsilon hOppositeDown
  have hHits := P.setHitsInfinite_translate_measureReal_eq
    mu hTI (verticalShift (-pad)) (R : Set V)
  rw [hRup, hbottomEq] at hraw
  have hHits' :
      mu.real (P.setHitsInfinite (Rdown : Set V)) =
        mu.real (P.setHitsInfinite (R : Set V)) := by
    simpa [Rdown, Finset.coe_image] using hHits
  rw [hHits'] at hraw
  dsimp only at hraw
  simp only [Ldown, Rdown, Rup] at hraw
  convert hraw using 1 <;> push_cast <;> ring


theorem PeriodicPlaneEmbedding.outwardHorizontalCrossing_ge_approxPreferredSide_transfer
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (a b c d : Real) (pad : Int) (hpad : 0 ≤ pad)
    (L R : Finset V) (epsilon : Real)
    (hOpposite :
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectLeftBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectRightBoundaryVertices a b c d)) + epsilon) :
    let Lleft := L.image (P.shift (horizontalShift (-pad)))
    let Rleft := R.image (P.shift (horizontalShift (-pad)))
    let Rright := R.image (P.shift (horizontalShift pad))
    let A := mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
      (E.rectLeftBoundaryVertices a b c d))
    let H := mu.real (P.setHitsInfinite (R : Set V))
    let Mtransfer := mu.real
      (E.rectanglePairMergeErrorUnion (a - pad) (b - pad) c d Lleft Rleft)
    let Mjoin := mu.real
      (E.rectanglePairMergeErrorUnion (a - pad) (b + pad) c d Lleft Rright)
    A * (H * A - Mtransfer - epsilon) - Mjoin ≤
      mu.real (E.horizontalCrossingEvent (a - pad) (b + pad) c d) := by
  dsimp only
  have hOppositeSwap :
      mu.real (E.axisSwap.rectSideConnectionEvent c d a b (R : Set V)
        (E.axisSwap.rectBottomBoundaryVertices c d a b)) ≤
      mu.real (E.axisSwap.rectSideConnectionEvent c d a b (R : Set V)
        (E.axisSwap.rectTopBoundaryVertices c d a b)) + epsilon := by
    simpa only [E.axisSwap_bottomBoundaryEvent,
      E.axisSwap_topBoundaryEvent] using hOpposite
  have haxis :=
    E.axisSwap.outwardVerticalCrossing_ge_approxPreferredSide_transfer
      mu hFKG (P.axisSwap_isTranslationInvariant mu hTI)
      c d a b pad hpad L R epsilon hOppositeSwap
  dsimp only at haxis
  have hshift (S : Finset V) (t : Int) :
      S.image (P.axisSwap.shift (verticalShift t)) =
        S.image (P.shift (horizontalShift t)) := by
    apply Finset.image_congr
    intro x hx
    change P.shift (siteAxisSwap (verticalShift t)) x =
      P.shift (horizontalShift t) x
    congr 2
    ext i
    fin_cases i <;> simp [siteAxisSwap, verticalShift, horizontalShift]
  have hmerge (x y : Real) (S T : Finset V) :
      E.axisSwap.rectanglePairMergeErrorUnion c d x y S T =
        E.rectanglePairMergeErrorUnion x y c d S T := by
    unfold PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion
    rw [E.axisSwap_rectVertices]
    have hcluster (omega : ConfigSpace (Sym2 V)) (v : V) :
        P.axisSwap.cluster omega v = P.cluster omega v := rfl
    have hconnected (u v : V) :
        P.axisSwap.connectedWithinSet (E.rectVertices x y c d) u v =
          P.connectedWithinSet (E.rectVertices x y c d) u v := rfl
    simp only [hcluster, hconnected]
  rw [E.axisSwap_bottomBoundaryEvent] at haxis
  simp only [hshift, hmerge] at haxis
  have hcross : mu.real (E.axisSwap.verticalCrossingEvent
      c d (a - pad) (b + pad)) ≤
      mu.real (E.horizontalCrossingEvent (a - pad) (b + pad) c d) :=
    measureReal_mono
      (E.axisSwap_verticalCrossingEvent_subset_horizontalCrossingEvent
        c d (a - pad) (b + pad))
  exact haxis.trans hcross



theorem PeriodicPlaneEmbedding.exists_outward_approxPreferredSide_crossing_branch
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (a b c d : Real) (pad : Int) (hpad : 0 ≤ pad)
    {width height : Nat} (hwidth : 0 < width) (hheight : 0 < height)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (source : PreferenceGridVertex width height → Finset V)
    (bottom top left right : PreferenceGridVertex width height → Real)
    (hsource : ∀ x, (source x : Set V) ⊆ E.rectVertices a b c d)
    (hbottomScore : ∀ x, bottom x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectBottomBoundaryVertices a b c d)))
    (htopScore : ∀ x, top x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectTopBoundaryVertices a b c d)))
    (hleftScore : ∀ x, left x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectLeftBoundaryVertices a b c d)))
    (hrightScore : ∀ x, right x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectRightBoundaryVertices a b c d)))
    (hbottom : ∀ i : Fin (width + 1),
      top (i, 0) ≤ bottom (i, 0) + epsilon)
    (htop : ∀ i : Fin (width + 1),
      bottom (i, Fin.last height) ≤ top (i, Fin.last height) + epsilon)
    (hleft : ∀ j : Fin (height + 1),
      right (0, j) ≤ left (0, j) + epsilon)
    (hright : ∀ j : Fin (height + 1),
      left (Fin.last width, j) ≤ right (Fin.last width, j) + epsilon) :
    ∃ x xVertical xHorizontal : PreferenceGridVertex width height,
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧
      ((1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
          bottom x + epsilon ∧
        let Ldown := (source x).image (P.shift (verticalShift (-pad)))
        let Rdown :=
          (source xVertical).image (P.shift (verticalShift (-pad)))
        let Rup := (source xVertical).image (P.shift (verticalShift pad))
        let Mtransfer := mu.real
          (E.rectanglePairMergeErrorUnion a b (c - pad) (d - pad)
            Ldown Rdown)
        let Mjoin := mu.real
          (E.rectanglePairMergeErrorUnion a b (c - pad) (d + pad)
            Ldown Rup)
        bottom x *
            (mu.real (P.setHitsInfinite (source xVertical : Set V)) *
              bottom x - Mtransfer - epsilon) - Mjoin ≤
          mu.real (E.verticalCrossingEvent a b (c - pad) (d + pad))) ∨
       (1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
          left x + epsilon ∧
        let Lleft := (source x).image (P.shift (horizontalShift (-pad)))
        let Rleft :=
          (source xHorizontal).image (P.shift (horizontalShift (-pad)))
        let Rright :=
          (source xHorizontal).image (P.shift (horizontalShift pad))
        let Mtransfer := mu.real
          (E.rectanglePairMergeErrorUnion (a - pad) (b - pad) c d
            Lleft Rleft)
        let Mjoin := mu.real
          (E.rectanglePairMergeErrorUnion (a - pad) (b + pad) c d
            Lleft Rright)
        left x *
            (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) *
              left x - Mtransfer - epsilon) - Mjoin ≤
          mu.real (E.horizontalCrossingEvent (a - pad) (b + pad) c d))) := by
  obtain ⟨x, xVertical, xHorizontal, hxBottom, hxLeft,
      hxVertical, hxVerticalOpposite, hxHorizontal, hxHorizontalOpposite⟩ :=
    exists_common_weak_approximate_preference_grid_witness
      hwidth hheight epsilon hepsilon bottom top left right
      hbottom htop hleft hright
  have hpref := E.preference_max_bottom_left_add_epsilon_ge_fourthRoot
    mu hFKG a b c d (source x : Set V) epsilon hepsilon (hsource x)
    (by simpa [hbottomScore x, htopScore x] using hxBottom)
    (by simpa [hleftScore x, hrightScore x] using hxLeft)
  have hpref' :
      1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
        max (bottom x) (left x) + epsilon := by
    simpa [hbottomScore x, hleftScore x] using hpref
  refine ⟨x, xVertical, xHorizontal, hxVertical, hxHorizontal, ?_⟩
  by_cases hLB : left x ≤ bottom x
  · left
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
        bottom x + epsilon := by
      simpa [max_eq_left hLB] using hpref'
    have htransfer :=
      E.outwardVerticalCrossing_ge_approxPreferredSide_transfer
        mu hFKG hTI a b c d pad hpad (source x) (source xVertical)
        epsilon (by simpa [hbottomScore xVertical, htopScore xVertical]
          using hxVerticalOpposite)
    rw [← hbottomScore x] at htransfer
    exact ⟨hroot, htransfer⟩
  · right
    have hBL : bottom x ≤ left x := le_of_not_ge hLB
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
        left x + epsilon := by
      simpa [max_eq_right hBL] using hpref'
    have htransfer :=
      E.outwardHorizontalCrossing_ge_approxPreferredSide_transfer
        mu hFKG hTI a b c d pad hpad (source x) (source xHorizontal)
        epsilon (by simpa [hleftScore xHorizontal, hrightScore xHorizontal]
          using hxHorizontalOpposite)
    rw [← hleftScore x] at htransfer
    exact ⟨hroot, htransfer⟩

set_option linter.unusedVariables false in

theorem PeriodicPlaneEmbedding.exists_uniformTemplate_outwardPreference_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat → Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (pad : Nat → Int) (hpad : ∀ n, 0 ≤ pad n) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n)
      (base : Nat → Site 2) (a b c d epsilon : Nat → Real)
      (bottom top left right : (n : Nat) →
        PreferenceGridVertex (width n) (height n) → Real),
      Tendsto epsilon atTop (nhds 0) → (∀ n, 0 ≤ epsilon n) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v +
            verticalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n)
              (c n - pad n) (d n - pad n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v +
            verticalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n)
              (c n - pad n) (d n + pad n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v +
            horizontalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n - pad n) (b n - pad n) (c n) (d n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v +
            horizontalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n - pad n) (b n + pad n) (c n) (d n)) →
      (∀ n v, bottom n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, top n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, left n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, right n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n i, top n (i, 0) ≤ bottom n (i, 0) + epsilon n) →
      (∀ n i, bottom n (i, Fin.last (height n)) ≤
        top n (i, Fin.last (height n)) + epsilon n) →
      (∀ n j, right n (0, j) ≤ left n (0, j) + epsilon n) →
      (∀ n j, left n (Fin.last (width n), j) ≤
        right n (Fin.last (width n), j) + epsilon n) →
      Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent (a n) (b n)
          (c n - pad n) (d n + pad n)))
        (mu.real (E.horizontalCrossingEvent
          (a n - pad n) (b n + pad n) (c n) (d n))))
        atTop (nhds 1) := by
  classical
  let neighbor : Nat → (Fin 3 × (Fin 3 × Fin 3)) → Finset V := fun n q =>
    (template n).image (P.shift (preferenceKingOffset q.2 +
      if q.1.val = 0 then 0 else if q.1.val = 1 then
        verticalShift (2 * pad n) else horizontalShift (2 * pad n)))
  obtain ⟨radius, _hradius, hmerge⟩ :=
    E.exists_uniform_translatedTemplate_mergeError_tendsto_zero
      mu hTI hunique template neighbor
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight base a b c d epsilon
    bottom top left right hepsilon hepsilon0 hsource
    hconnectorV0 hconnectorV1 hconnectorH0 hconnectorH1
    hbottomScore htopScore hleftScore hrightScore
    hbottom htop hleft hright
  have hwitness (n : Nat) :=
    E.exists_outward_approxPreferredSide_crossing_branch
      mu hFKG hTI (a n) (b n) (c n) (d n) (pad n) (hpad n)
      (hwidth n) (hheight n) (epsilon n) (hepsilon0 n)
      (fun v => (template n).image
        (P.shift (base n + preferenceGridSite v)))
      (bottom n) (top n) (left n) (right n)
      (hsource n) (hbottomScore n) (htopScore n)
      (hleftScore n) (hrightScore n)
      (hbottom n) (htop n) (hleft n) (hright n)
  choose x xVertical xHorizontal hxVadj hxHadj hbranch using hwitness
  choose ijV hijV using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxVadj n)
  choose ijH hijH using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxHadj n)
  let source : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Finset V := fun n v =>
    (template n).image (P.shift (base n + preferenceGridSite v))
  let zV : Nat → Site 2 := fun n =>
    base n + preferenceGridSite (x n) + verticalShift (-(pad n))
  let zH : Nat → Site 2 := fun n =>
    base n + preferenceGridSite (x n) + horizontalShift (-(pad n))
  have hneighbor (z : Nat → Site 2) (n : Nat)
      (q : Fin 3 × (Fin 3 × Fin 3)) :
      (neighbor n q).image (P.shift (z n)) =
        (template n).image (P.shift (z n + preferenceKingOffset q.2 +
          if q.1.val = 0 then 0 else if q.1.val = 1 then
            verticalShift (2 * pad n) else horizontalShift (2 * pad n))) := by
    simp only [neighbor, Finset.image_image]
    apply Finset.image_congr
    intro u hu
    change P.shift (z n) (P.shift (preferenceKingOffset q.2 +
        (if q.1.val = 0 then 0 else if q.1.val = 1 then
          verticalShift (2 * pad n) else horizontalShift (2 * pad n))) u) =
      P.shift (z n + preferenceKingOffset q.2 +
        (if q.1.val = 0 then 0 else if q.1.val = 1 then
          verticalShift (2 * pad n) else horizontalShift (2 * pad n))) u
    rw [← P.shift_add]
    congr 2
    abel
  have hzV (n : Nat) :
      zV n + preferenceKingOffset (ijV n) =
        base n + preferenceGridSite (xVertical n) +
          verticalShift (-(pad n)) := by
    dsimp only [zV]
    rw [hijV n]
    abel
  have hzH (n : Nat) :
      zH n + preferenceKingOffset (ijH n) =
        base n + preferenceGridSite (xHorizontal n) +
          horizontalShift (-(pad n)) := by
    dsimp only [zH]
    rw [hijH n]
    abel
  have hMv00 := hmerge zV (fun n => ((0 : Fin 3), ijV n))
    a b (fun n => c n - pad n) (fun n => d n - pad n)
    (fun n => hconnectorV0 n (x n))
  have hMv10 := hmerge zV (fun n => ((1 : Fin 3), ijV n))
    a b (fun n => c n - pad n) (fun n => d n + pad n)
    (fun n => hconnectorV1 n (x n))
  have hMh00 := hmerge zH (fun n => ((0 : Fin 3), ijH n))
    (fun n => a n - pad n) (fun n => b n - pad n) c d
    (fun n => hconnectorH0 n (x n))
  have hMh10 := hmerge zH (fun n => ((2 : Fin 3), ijH n))
    (fun n => a n - pad n) (fun n => b n + pad n) c d
    (fun n => hconnectorH1 n (x n))
  let Ldown : Nat → Finset V := fun n =>
    (source n (x n)).image (P.shift (verticalShift (-(pad n))))
  let Rdown : Nat → Finset V := fun n =>
    (source n (xVertical n)).image (P.shift (verticalShift (-(pad n))))
  let Rup : Nat → Finset V := fun n =>
    (source n (xVertical n)).image (P.shift (verticalShift (pad n)))
  let Lleft : Nat → Finset V := fun n =>
    (source n (x n)).image (P.shift (horizontalShift (-(pad n))))
  let Rleft : Nat → Finset V := fun n =>
    (source n (xHorizontal n)).image (P.shift (horizontalShift (-(pad n))))
  let Rright : Nat → Finset V := fun n =>
    (source n (xHorizontal n)).image (P.shift (horizontalShift (pad n)))
  have htranslatedSource (n : Nat)
      (v : PreferenceGridVertex (width n) (height n)) (s : Site 2) :
      (source n v).image (P.shift s) =
        (template n).image
          (P.shift (base n + preferenceGridSite v + s)) := by
    simp only [source, Finset.image_image]
    apply Finset.image_congr
    intro u hu
    change P.shift s (P.shift (base n + preferenceGridSite v) u) =
      P.shift (base n + preferenceGridSite v + s) u
    rw [← P.shift_add]
  have hLdown (n : Nat) :
      (template n).image (P.shift (zV n)) = Ldown n := by
    exact (htranslatedSource n (x n) (verticalShift (-(pad n)))).symm
  have hRdown (n : Nat) :
      (neighbor n ((0 : Fin 3), ijV n)).image (P.shift (zV n)) =
        Rdown n := by
    rw [hneighbor]
    simp only [Fin.val_zero, ↓reduceIte, add_zero]
    rw [hzV]
    exact (htranslatedSource n (xVertical n)
      (verticalShift (-(pad n)))).symm
  have hRup (n : Nat) :
      (neighbor n ((1 : Fin 3), ijV n)).image (P.shift (zV n)) =
        Rup n := by
    rw [hneighbor]
    simp only [Fin.val_one, one_ne_zero, ↓reduceIte]
    have hs : zV n + preferenceKingOffset (ijV n) +
        verticalShift (2 * pad n) =
      base n + preferenceGridSite (xVertical n) + verticalShift (pad n) := by
      rw [hzV]
      ext i
      fin_cases i <;> simp [verticalShift] <;> omega
    rw [hs]
    exact (htranslatedSource n (xVertical n) (verticalShift (pad n))).symm
  have hLleft (n : Nat) :
      (template n).image (P.shift (zH n)) = Lleft n := by
    exact (htranslatedSource n (x n) (horizontalShift (-(pad n)))).symm
  have hRleft (n : Nat) :
      (neighbor n ((0 : Fin 3), ijH n)).image (P.shift (zH n)) =
        Rleft n := by
    rw [hneighbor]
    simp only [Fin.val_zero, ↓reduceIte, add_zero]
    rw [hzH]
    exact (htranslatedSource n (xHorizontal n)
      (horizontalShift (-(pad n)))).symm
  have hRright (n : Nat) :
      (neighbor n ((2 : Fin 3), ijH n)).image (P.shift (zH n)) =
        Rright n := by
    rw [hneighbor]
    change (template n).image (P.shift
      (zH n + preferenceKingOffset (ijH n) +
        horizontalShift (2 * pad n))) = Rright n
    have hs : zH n + preferenceKingOffset (ijH n) +
        horizontalShift (2 * pad n) =
      base n + preferenceGridSite (xHorizontal n) + horizontalShift (pad n) := by
      rw [hzH]
      ext i
      fin_cases i <;> simp [horizontalShift] <;> omega
    rw [hs]
    exact (htranslatedSource n (xHorizontal n)
      (horizontalShift (pad n))).symm
  let Mv0 : Nat → Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n)
      (c n - pad n) (d n - pad n) (Ldown n) (Rdown n))
  let Mv1 : Nat → Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n)
      (c n - pad n) (d n + pad n) (Ldown n) (Rup n))
  let Mh0 : Nat → Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n - pad n) (b n - pad n)
      (c n) (d n) (Lleft n) (Rleft n))
  let Mh1 : Nat → Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n - pad n) (b n + pad n)
      (c n) (d n) (Lleft n) (Rright n))
  let Mv : Nat → Real := fun n => Mv0 n + Mv1 n
  let Mh : Nat → Real := fun n => Mh0 n + Mh1 n
  have hMv0 : Tendsto Mv0 atTop (nhds 0) := by
    simpa only [Mv0, hLdown, hRdown] using hMv00
  have hMv1 : Tendsto Mv1 atTop (nhds 0) := by
    simpa only [Mv1, hLdown, hRup] using hMv10
  have hMh0 : Tendsto Mh0 atTop (nhds 0) := by
    simpa only [Mh0, hLleft, hRleft] using hMh00
  have hMh1 : Tendsto Mh1 atTop (nhds 0) := by
    simpa only [Mh1, hLleft, hRright] using hMh10
  have hMv : Tendsto Mv atTop (nhds 0) := by
    simpa [Mv] using hMv0.add hMv1
  have hMh : Tendsto Mh atTop (nhds 0) := by
    simpa [Mh] using hMh0.add hMh1
  let verticalBranch : Nat → Prop := fun n =>
    1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))) ≤
          bottom n (x n) + epsilon n ∧
      bottom n (x n) *
          (mu.real (P.setHitsInfinite
              (source n (xVertical n) : Set V)) * bottom n (x n) -
            Mv0 n - epsilon n) - Mv1 n ≤
        mu.real (E.verticalCrossingEvent (a n) (b n)
          (c n - pad n) (d n + pad n))
  let A : Nat → Real := fun n =>
    if verticalBranch n then bottom n (x n) else left n (x n)
  let Hv : Nat → Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xVertical n) : Set V))
  let Hh : Nat → Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xHorizontal n) : Set V))
  let Cv : Nat → Real := fun n => mu.real
    (E.verticalCrossingEvent (a n) (b n)
      (c n - pad n) (d n + pad n))
  let Ch : Nat → Real := fun n => mu.real
    (E.horizontalCrossingEvent (a n - pad n) (b n + pad n) (c n) (d n))
  let root : Nat → Real := fun n =>
    1 - Real.sqrt (Real.sqrt
      (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V))))
  have htranslatedHit (y : (n : Nat) →
      PreferenceGridVertex (width n) (height n)) : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (source n (y n) : Set V)))
      atTop (nhds 1) := by
    apply htemplateHit.congr'
    filter_upwards with n
    have hset : ((source n (y n) : Finset V) : Set V) =
        P.shift (base n + preferenceGridSite (y n)) ''
          (template n : Set V) := by
      ext v
      simp [source]
    rw [hset, P.setHitsInfinite_translate_measureReal_eq mu hTI]
  have hroot : Tendsto root atTop (nhds 1) := by
    have hhit := htranslatedHit x
    have hmiss : Tendsto (fun n =>
        1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hhit
    simpa [root] using tendsto_const_nhds.sub hmiss.sqrt.sqrt
  have hHv : Tendsto Hv atTop (nhds 1) := by
    simpa [Hv] using htranslatedHit xVertical
  have hHh : Tendsto Hh atTop (nhds 1) := by
    simpa [Hh] using htranslatedHit xHorizontal
  have hrootA (n : Nat) : root n ≤ A n + epsilon n := by
    by_cases hv : verticalBranch n
    · simpa [A, root, hv] using hv.1
    · simpa [A, root, source, Ldown, Rdown, Rup, Lleft, Rleft, Rright,
        Mv0, Mv1, Mh0, Mh1, hv] using ((hbranch n).resolve_left hv).1
  have hAupper (n : Nat) : A n ≤ 1 := by
    by_cases hv : verticalBranch n
    · simp only [A, if_pos hv]
      rw [hbottomScore n (x n)]
      exact measureReal_le_one
    · simp only [A, if_neg hv]
      rw [hleftScore n (x n)]
      exact measureReal_le_one
  have hcrossingBranch (n : Nat) :
      A n * (Hv n * A n - Mv n - epsilon n) - Mv n ≤ Cv n ∨
      A n * (Hh n * A n - Mh n - epsilon n) - Mh n ≤ Ch n := by
    by_cases hv : verticalBranch n
    · left
      have hraw := hv.2
      have hA0 : 0 ≤ bottom n (x n) := by
        rw [hbottomScore]
        exact measureReal_nonneg
      have hM0 : 0 ≤ Mv0 n := measureReal_nonneg
      have hM1 : 0 ≤ Mv1 n := measureReal_nonneg
      simp only [A, if_pos hv, Hv, Cv, Mv] at ⊢
      nlinarith
    · right
      have hraw := ((hbranch n).resolve_left hv).2
      have hA0 : 0 ≤ left n (x n) := by
        rw [hleftScore]
        exact measureReal_nonneg
      have hM0 : 0 ≤ Mh0 n := measureReal_nonneg
      have hM1 : 0 ≤ Mh1 n := measureReal_nonneg
      have hraw' :
          left n (x n) *
              (Hh n * left n (x n) - Mh0 n - epsilon n) - Mh1 n ≤
            Ch n := by
        simpa [Hh, Ch, source, Ldown, Rdown, Rup, Lleft, Rleft, Rright,
          Mv0, Mv1, Mh0, Mh1] using hraw
      simp only [A, if_neg hv, Hh, Ch, Mh]
      nlinarith [hraw']
  simpa [Cv, Ch] using
    crossing_max_tendsto_one_of_approxPreferredSide_root_branches
      root A Hv Hh Mv Mh epsilon Cv Ch hroot hrootA hAupper
      hHv hHh hMv hMh hepsilon hcrossingBranch
      (fun _ => measureReal_le_one) (fun _ => measureReal_le_one)

set_option linter.unusedVariables false in

theorem PeriodicPlaneEmbedding.exists_uniformTemplate_outwardBoundaryScores_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat → Finset V)
    (htemplateHit : Tendsto (fun n ↦
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (pad : Nat → Int) (hpad : ∀ n, 0 ≤ pad n) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n)
      (base : Nat → Site 2) (a b c d p : Nat → Real),
      Tendsto p atTop (nhds 1) → (∀ n, p n ≤ 1) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v +
            verticalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n)
              (c n - pad n) (d n - pad n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v +
            verticalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n)
              (c n - pad n) (d n + pad n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v +
            horizontalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n - pad n) (b n - pad n) (c n) (d n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v +
            horizontalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n - pad n) (b n + pad n) (c n) (d n)) →
      (∀ n (i : Fin (width n + 1)), p n ≤ mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image (P.shift (base n + preferenceGridSite
            (i, (0 : Fin (height n + 1))))) : Set V)
          (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n (i : Fin (width n + 1)), p n ≤ mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image (P.shift (base n + preferenceGridSite
            (i, Fin.last (height n)))) : Set V)
          (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n (j : Fin (height n + 1)), p n ≤ mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image (P.shift (base n + preferenceGridSite
            ((0 : Fin (width n + 1)), j))) : Set V)
          (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n (j : Fin (height n + 1)), p n ≤ mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image (P.shift (base n + preferenceGridSite
            (Fin.last (width n), j))) : Set V)
          (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) →
      Tendsto (fun n ↦ max
        (mu.real (E.verticalCrossingEvent (a n) (b n)
          (c n - pad n) (d n + pad n)))
        (mu.real (E.horizontalCrossingEvent
          (a n - pad n) (b n + pad n) (c n) (d n))))
        atTop (nhds 1) := by
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_outwardPreference_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit pad hpad
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight base a b c d p
    hplim hp hsource hconnectorV0 hconnectorV1 hconnectorH0 hconnectorH1
    hbottom htop hleft hright
  let epsilon : Nat → Real := fun n ↦ 1 - p n
  let bottom : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real :=
    fun n v ↦ mu.real (E.rectSideConnectionEvent
      (a n) (b n) (c n) (d n)
      ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  let top : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real :=
    fun n v ↦ mu.real (E.rectSideConnectionEvent
      (a n) (b n) (c n) (d n)
      ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))
  let left : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real :=
    fun n v ↦ mu.real (E.rectSideConnectionEvent
      (a n) (b n) (c n) (d n)
      ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  let right : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real :=
    fun n v ↦ mu.real (E.rectSideConnectionEvent
      (a n) (b n) (c n) (d n)
      ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))
  apply hcross width height hwidth hheight base a b c d epsilon
    bottom top left right
  · simpa [epsilon] using
      (tendsto_const_nhds (x := (1 : Real))).sub hplim
  · exact fun n ↦ sub_nonneg.mpr (hp n)
  · exact hsource
  · exact hconnectorV0
  · exact hconnectorV1
  · exact hconnectorH0
  · exact hconnectorH1
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n i
    have hTop : top n (i, 0) ≤ 1 := measureReal_le_one
    have hBottom := hbottom n i
    dsimp only [top, bottom, epsilon]
    linarith
  · intro n i
    have hBottom : bottom n (i, Fin.last (height n)) ≤ 1 :=
      measureReal_le_one
    have hTop := htop n i
    dsimp only [top, bottom, epsilon]
    linarith
  · intro n j
    have hRight : right n (0, j) ≤ 1 := measureReal_le_one
    have hLeft := hleft n j
    dsimp only [left, right, epsilon]
    linarith
  · intro n j
    have hLeft : left n (Fin.last (width n), j) ≤ 1 := measureReal_le_one
    have hRight := hright n j
    dsimp only [left, right, epsilon]
    linarith




theorem PeriodicPlaneEmbedding.exists_adjacentHeight_approxPreferredSide_crossing_branch
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (a b c d : Real) (t : Int) (ht : 0 ≤ t) {width height : Nat}
    (hwidth : 0 < width) (hheight : 0 < height)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (source : PreferenceGridVertex width height → Finset V)
    (bottom top left right : PreferenceGridVertex width height → Real)
    (hsource : ∀ x, (source x : Set V) ⊆ E.rectVertices a b c d)
    (hbottomScore : ∀ x, bottom x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectBottomBoundaryVertices a b c d)))
    (htopScore : ∀ x, top x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectTopBoundaryVertices a b c d)))
    (hleftScore : ∀ x, left x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectLeftBoundaryVertices a b c d)))
    (hrightScore : ∀ x, right x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectRightBoundaryVertices a b c d)))
    (hbottom : ∀ i : Fin (width + 1),
      top (i, 0) ≤ bottom (i, 0) + epsilon)
    (htop : ∀ i : Fin (width + 1),
      bottom (i, Fin.last height) ≤ top (i, Fin.last height) + epsilon)
    (hleft : ∀ j : Fin (height + 1),
      right (0, j) ≤ left (0, j) + epsilon)
    (hright : ∀ j : Fin (height + 1),
      left (Fin.last width, j) ≤ right (Fin.last width, j) + epsilon) :
    ∃ x xVertical xHorizontal : PreferenceGridVertex width height,
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧
      ((1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
          bottom x + epsilon ∧
        let U := (source xVertical).image (P.shift (verticalShift t))
        let Mtransfer := mu.real
          (E.rectanglePairMergeErrorUnion a b c d
            (source x) (source xVertical))
        let Mjoin := mu.real
          (E.rectanglePairMergeErrorUnion a b c (d + t) (source x) U)
        bottom x *
            (mu.real (P.setHitsInfinite (source xVertical : Set V)) *
              bottom x - Mtransfer - epsilon) - Mjoin ≤
          mu.real (E.verticalCrossingEvent a b c (d + t))) ∨
       (1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
          left x + epsilon ∧
        left x *
            (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) *
              left x -
              mu.real (E.rectanglePairMergeErrorUnion a b c d
                (source x) (source xHorizontal)) - epsilon) -
            mu.real (E.rectanglePairMergeErrorUnion a b c d
              (source x) (source xHorizontal)) ≤
          mu.real (E.horizontalCrossingEvent a b c d))) := by
  obtain ⟨x, xVertical, xHorizontal, hxBottom, hxLeft,
      hxVertical, hxVerticalOpposite, hxHorizontal, hxHorizontalOpposite⟩ :=
    exists_common_weak_approximate_preference_grid_witness
      hwidth hheight epsilon hepsilon bottom top left right
      hbottom htop hleft hright
  have hpref := E.preference_max_bottom_left_add_epsilon_ge_fourthRoot
    mu hFKG a b c d (source x : Set V) epsilon hepsilon (hsource x)
    (by simpa [hbottomScore x, htopScore x] using hxBottom)
    (by simpa [hleftScore x, hrightScore x] using hxLeft)
  have hpref' :
      1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
        max (bottom x) (left x) + epsilon := by
    simpa [hbottomScore x, hleftScore x] using hpref
  refine ⟨x, xVertical, xHorizontal, hxVertical, hxHorizontal, ?_⟩
  by_cases hLB : left x ≤ bottom x
  · left
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
        bottom x + epsilon := by
      simpa [max_eq_left hLB] using hpref'
    have htransfer :=
      E.adjacentHeightVerticalCrossing_ge_approxPreferredSide_transfer
        mu hFKG hTI a b c d t ht (source x) (source xVertical) epsilon
        (by simpa [hbottomScore xVertical, htopScore xVertical] using
          hxVerticalOpposite)
    rw [← hbottomScore x] at htransfer
    exact ⟨hroot, htransfer⟩
  · right
    have hBL : bottom x ≤ left x := le_of_not_ge hLB
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
        left x + epsilon := by
      simpa [max_eq_right hBL] using hpref'
    have htransfer := E.horizontalCrossing_ge_approxPreferredSide_transfer
      mu hFKG a b c d (source x) (source xHorizontal) epsilon
      (by simpa [hleftScore xHorizontal, hrightScore xHorizontal] using
        hxHorizontalOpposite)
    rw [← hleftScore x] at htransfer
    exact ⟨hroot, htransfer⟩

set_option linter.unusedVariables false in



theorem PeriodicPlaneEmbedding.exists_uniformTemplate_adjacentHeightPreference_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat → Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (step : Nat → Int) (hstep : ∀ n, 0 ≤ step n) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n)
      (base : Nat → Site 2) (a b c d epsilon : Nat → Real)
      (bottom top left right : (n : Nat) →
        PreferenceGridVertex (width n) (height n) → Real),
      Tendsto epsilon atTop (nhds 0) → (∀ n, 0 ≤ epsilon n) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n v, bottom n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, top n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, left n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, right n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n i, top n (i, 0) ≤ bottom n (i, 0) + epsilon n) →
      (∀ n i, bottom n (i, Fin.last (height n)) ≤
        top n (i, Fin.last (height n)) + epsilon n) →
      (∀ n j, right n (0, j) ≤ left n (0, j) + epsilon n) →
      (∀ n j, left n (Fin.last (width n), j) ≤
        right n (Fin.last (width n), j) + epsilon n) →
      Tendsto (fun n => max
        (mu.real (E.horizontalCrossingEvent
          (a n) (b n) (c n) (d n)))
        (mu.real (E.verticalCrossingEvent
          (a n) (b n) (c n) (d n + step n)))) atTop (nhds 1) := by
  classical
  let neighbor : Nat → (Fin 2 × (Fin 3 × Fin 3)) → Finset V := fun n q =>
    (template n).image (P.shift (preferenceKingOffset q.2 +
      if q.1.val = 0 then 0 else verticalShift (step n)))
  obtain ⟨radius, _hradius, hmerge⟩ :=
    E.exists_uniform_translatedTemplate_mergeError_tendsto_zero
      mu hTI hunique template neighbor
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight base a b c d epsilon
    bottom top left right hepsilon hepsilon0 hsource hconnector
    hbottomScore htopScore hleftScore hrightScore
    hbottom htop hleft hright
  have hwitness (n : Nat) :=
    E.exists_adjacentHeight_approxPreferredSide_crossing_branch
      mu hFKG hTI (a n) (b n) (c n) (d n) (step n) (hstep n)
      (hwidth n) (hheight n) (epsilon n) (hepsilon0 n)
      (fun v => (template n).image
        (P.shift (base n + preferenceGridSite v)))
      (bottom n) (top n) (left n) (right n)
      (hsource n) (hbottomScore n) (htopScore n)
      (hleftScore n) (hrightScore n)
      (hbottom n) (htop n) (hleft n) (hright n)
  choose x xVertical xHorizontal hxVadj hxHadj hbranch using hwitness
  choose ijV hijV using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxVadj n)
  choose ijH hijH using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxHadj n)
  let source : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Finset V := fun n v =>
    (template n).image (P.shift (base n + preferenceGridSite v))
  let shiftedVerticalSource : Nat → Finset V := fun n =>
    (source n (xVertical n)).image (P.shift (verticalShift (step n)))
  let z : Nat → Site 2 := fun n => base n + preferenceGridSite (x n)
  have hzV (n : Nat) : z n + preferenceKingOffset (ijV n) =
      base n + preferenceGridSite (xVertical n) := by
    dsimp only [z]
    rw [hijV n]
    simp only [add_assoc]
  have hzH (n : Nat) : z n + preferenceKingOffset (ijH n) =
      base n + preferenceGridSite (xHorizontal n) := by
    dsimp only [z]
    rw [hijH n]
    simp only [add_assoc]
  have hneighbor0 (n : Nat) (ij : Fin 3 × Fin 3) :
      (neighbor n ((0 : Fin 2), ij)).image (P.shift (z n)) =
        (template n).image
          (P.shift (z n + preferenceKingOffset ij)) := by
    simp only [neighbor, Fin.isValue, Fin.val_zero, ↓reduceIte, add_zero,
      Finset.image_image]
    apply Finset.image_congr
    intro u hu
    simpa [add_comm] using
      (P.shift_add (preferenceKingOffset ij) (z n) u).symm
  have hneighbor1 (n : Nat) (ij : Fin 3 × Fin 3) :
      (neighbor n ((1 : Fin 2), ij)).image (P.shift (z n)) =
        ((template n).image
          (P.shift (z n + preferenceKingOffset ij))).image
            (P.shift (verticalShift (step n))) := by
    simp only [neighbor, Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte,
      Finset.image_image]
    apply Finset.image_congr
    intro u hu
    change P.shift (z n)
        (P.shift (preferenceKingOffset ij + verticalShift (step n)) u) =
      P.shift (verticalShift (step n))
        (P.shift (z n + preferenceKingOffset ij) u)
    rw [← P.shift_add, ← P.shift_add]
    congr 2
    abel
  have hconnectorHull (n : Nat)
      (v : PreferenceGridVertex (width n) (height n)) :
      (P.shift (base n + preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
          E.rectVertices (a n) (b n) (c n) (d n + step n) := by
    have hstepR : (0 : Real) ≤ step n := by exact_mod_cast hstep n
    exact Set.Subset.trans (hconnector n v)
      (E.rectVertices_mono le_rfl le_rfl le_rfl (by linarith))
  have hMv00 := hmerge z (fun n => ((0 : Fin 2), ijV n)) a b c d
    (fun n => hconnector n (x n))
  have hMv10 := hmerge z (fun n => ((1 : Fin 2), ijV n))
    a b c (fun n => d n + step n) (fun n => hconnectorHull n (x n))
  have hMh0 := hmerge z (fun n => ((0 : Fin 2), ijH n)) a b c d
    (fun n => hconnector n (x n))
  let Mv0 : Nat → Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
      (source n (x n)) (source n (xVertical n)))
  let Mv1 : Nat → Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n + step n)
      (source n (x n)) (shiftedVerticalSource n))
  let Mv : Nat → Real := fun n => Mv0 n + Mv1 n
  let Mh : Nat → Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
      (source n (x n)) (source n (xHorizontal n)))
  have hMv0 : Tendsto Mv0 atTop (nhds 0) := by
    simpa only [Mv0, source, z, hneighbor0, hzV] using hMv00
  have hMv1 : Tendsto Mv1 atTop (nhds 0) := by
    simpa only [Mv1, source, shiftedVerticalSource, z, hneighbor1, hzV]
      using hMv10
  have hMv : Tendsto Mv atTop (nhds 0) := by
    simpa only [Mv, zero_add] using hMv0.add hMv1
  have hMh : Tendsto Mh atTop (nhds 0) := by
    simpa only [Mh, source, z, hneighbor0, hzH] using hMh0
  let verticalBranch : Nat → Prop := fun n =>
    1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))) ≤
          bottom n (x n) + epsilon n ∧
      bottom n (x n) *
          (mu.real (P.setHitsInfinite
              (source n (xVertical n) : Set V)) * bottom n (x n) -
            Mv0 n - epsilon n) - Mv1 n ≤
        mu.real (E.verticalCrossingEvent
          (a n) (b n) (c n) (d n + step n))
  let A : Nat → Real := fun n =>
    if verticalBranch n then bottom n (x n) else left n (x n)
  let Hv : Nat → Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xVertical n) : Set V))
  let Hh : Nat → Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xHorizontal n) : Set V))
  let Cv : Nat → Real := fun n => mu.real
    (E.verticalCrossingEvent (a n) (b n) (c n) (d n + step n))
  let Ch : Nat → Real := fun n => mu.real
    (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))
  let root : Nat → Real := fun n =>
    1 - Real.sqrt (Real.sqrt
      (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V))))
  have htranslatedHit (y : (n : Nat) →
      PreferenceGridVertex (width n) (height n)) : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (source n (y n) : Set V)))
      atTop (nhds 1) := by
    apply htemplateHit.congr'
    filter_upwards with n
    have hset : ((source n (y n) : Finset V) : Set V) =
        P.shift (base n + preferenceGridSite (y n)) ''
          (template n : Set V) := by
      ext v
      simp [source]
    rw [hset, P.setHitsInfinite_translate_measureReal_eq mu hTI]
  have hroot : Tendsto root atTop (nhds 1) := by
    have hhit := htranslatedHit x
    have hmiss : Tendsto (fun n =>
        1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hhit
    simpa [root] using tendsto_const_nhds.sub hmiss.sqrt.sqrt
  have hHv : Tendsto Hv atTop (nhds 1) := by
    simpa [Hv] using htranslatedHit xVertical
  have hHh : Tendsto Hh atTop (nhds 1) := by
    simpa [Hh] using htranslatedHit xHorizontal
  have hrootA (n : Nat) : root n ≤ A n + epsilon n := by
    by_cases hv : verticalBranch n
    · simpa [A, root, hv] using hv.1
    · simpa [A, root, source, shiftedVerticalSource, Mv0, Mv1, hv] using
        ((hbranch n).resolve_left hv).1
  have hAupper (n : Nat) : A n ≤ 1 := by
    by_cases hv : verticalBranch n
    · simp only [A, if_pos hv]
      rw [hbottomScore n (x n)]
      exact measureReal_le_one
    · simp only [A, if_neg hv]
      rw [hleftScore n (x n)]
      exact measureReal_le_one
  have hcrossingBranch (n : Nat) :
      A n * (Hv n * A n - Mv n - epsilon n) - Mv n ≤ Cv n ∨
      A n * (Hh n * A n - Mh n - epsilon n) - Mh n ≤ Ch n := by
    by_cases hv : verticalBranch n
    · left
      have hraw := hv.2
      have hA0 : 0 ≤ bottom n (x n) := by
        rw [hbottomScore]
        exact measureReal_nonneg
      have hM0 : 0 ≤ Mv0 n := measureReal_nonneg
      have hM1 : 0 ≤ Mv1 n := measureReal_nonneg
      simp only [A, if_pos hv, Hv, Cv, Mv] at ⊢
      nlinarith
    · right
      have h := (hbranch n).resolve_left hv
      simpa [A, Hh, Ch, Mh, source, shiftedVerticalSource, Mv0, Mv1, hv]
        using h.2
  simpa [Cv, Ch, max_comm] using
    crossing_max_tendsto_one_of_approxPreferredSide_root_branches
      root A Hv Hh Mv Mh epsilon Cv Ch hroot hrootA hAupper
      hHv hHh hMv hMh hepsilon hcrossingBranch
      (fun _ => measureReal_le_one) (fun _ => measureReal_le_one)

set_option linter.unusedVariables false in

theorem PeriodicPlaneEmbedding.exists_uniformTemplate_adjacentHeightBoundaryScores_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat → Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (step : Nat → Int) (hstep : ∀ n, 0 ≤ step n) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n)
      (base : Nat → Site 2) (a b c d p : Nat → Real),
      Tendsto p atTop (nhds 1) → (∀ n, p n ≤ 1) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n (i : Fin (width n + 1)), p n ≤ mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image (P.shift (base n + preferenceGridSite
            (i, (0 : Fin (height n + 1))))) : Set V)
          (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n (i : Fin (width n + 1)), p n ≤ mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image (P.shift (base n + preferenceGridSite
            (i, Fin.last (height n)))) : Set V)
          (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n (j : Fin (height n + 1)), p n ≤ mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image (P.shift (base n + preferenceGridSite
            ((0 : Fin (width n + 1)), j))) : Set V)
          (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n (j : Fin (height n + 1)), p n ≤ mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image (P.shift (base n + preferenceGridSite
            (Fin.last (width n), j))) : Set V)
          (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) →
      Tendsto (fun n => max
        (mu.real (E.horizontalCrossingEvent
          (a n) (b n) (c n) (d n)))
        (mu.real (E.verticalCrossingEvent
          (a n) (b n) (c n) (d n + step n)))) atTop (nhds 1) := by
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_adjacentHeightPreference_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit step hstep
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight base a b c d p
    hplim hp hsource hconnector hbottom htop hleft hright
  let epsilon : Nat → Real := fun n => 1 - p n
  let bottom : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real :=
    fun n v => mu.real (E.rectSideConnectionEvent
      (a n) (b n) (c n) (d n)
      ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  let top : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real :=
    fun n v => mu.real (E.rectSideConnectionEvent
      (a n) (b n) (c n) (d n)
      ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))
  let left : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real :=
    fun n v => mu.real (E.rectSideConnectionEvent
      (a n) (b n) (c n) (d n)
      ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  let right : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real :=
    fun n v => mu.real (E.rectSideConnectionEvent
      (a n) (b n) (c n) (d n)
      ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))
  apply hcross width height hwidth hheight base a b c d epsilon
    bottom top left right
  · simpa [epsilon] using
      (tendsto_const_nhds (x := (1 : Real))).sub hplim
  · exact fun n => sub_nonneg.mpr (hp n)
  · exact hsource
  · exact hconnector
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n i
    have hTop : top n (i, 0) ≤ 1 := measureReal_le_one
    have hBottom := hbottom n i
    dsimp only [top, bottom, epsilon]
    linarith
  · intro n i
    have hBottom : bottom n (i, Fin.last (height n)) ≤ 1 :=
      measureReal_le_one
    have hTop := htop n i
    dsimp only [top, bottom, epsilon]
    linarith
  · intro n j
    have hRight : right n (0, j) ≤ 1 := measureReal_le_one
    have hLeft := hleft n j
    dsimp only [left, right, epsilon]
    linarith
  · intro n j
    have hLeft : left n (Fin.last (width n), j) ≤ 1 := measureReal_le_one
    have hRight := hright n j
    dsimp only [left, right, epsilon]
    linarith




theorem PeriodicPlanarDualPair.macroArray_contradiction_of_crossing_limits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B T : Nat) (hBpos : 0 < B) (hT : 8 * B < T)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| ≤ (B : Real))
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| ≤ (B : Real))
    (a0 b0 c0 d0 : Nat → Real) (K : Nat → Nat)
    (hspanX0 : ∀ n, a0 n + 5 * B < b0 n - 5 * B)
    (hspanY0 : ∀ n, c0 n + 5 * B < d0 n - 5 * B)
    (hverticalStart : Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n)))
      atTop (nhds 1))
    (hhorizontalEnd :
      let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
      Tendsto (fun n => mu.real
        (D.primalEmbedding.horizontalCrossingEvent
          (q n (K n + 1)).1 (q n (K n + 1)).2.1
          ((q n (K n + 1)).2.2.1 + 4 * B)
          ((q n (K n + 1)).2.2.2 - 4 * B))) atTop (nhds 1))
    (hprimalAdjacent :
      let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
      ∀ k : Nat → Nat, (∀ n, k n < K n + 1) →
        Tendsto (fun n => max
          (mu.real (D.primalEmbedding.horizontalCrossingEvent
            (q n (k n)).1 (q n (k n)).2.1
            ((q n (k n)).2.2.1 + 4 * B)
            ((q n (k n)).2.2.2 - 4 * B)))
          (mu.real (D.primalEmbedding.verticalCrossingEvent
            (q n (k n)).1 (q n (k n)).2.1
            ((q n (k n)).2.2.1 + 4 * B)
            ((q n (k n)).2.2.2 - 4 * B + (T + 4 * B : Nat)))))
          atTop (nhds 1))
    (hdual :
      let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
      ∀ k : Nat → Nat, Tendsto (fun n => max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            ((q n (k n)).1 + 4 * B) ((q n (k n)).2.1 - 4 * B)
            ((q n (k n)).2.2.1) ((q n (k n)).2.2.2)))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            ((q n (k n)).1) ((q n (k n)).2.1)
            ((q n (k n)).2.2.1 + 4 * B)
            ((q n (k n)).2.2.2 - 4 * B)))) atTop (nhds 1)) : False := by
  let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
  let a : Nat → Nat → Real := fun n k => (q n k).1
  let b : Nat → Nat → Real := fun n k => (q n k).2.1
  let c : Nat → Nat → Real := fun n k => (q n k).2.2.1
  let d : Nat → Nat → Real := fun n k => (q n k).2.2.2
  have hspans := sheffieldMacroArrayCoordinates_spans B T hT
    a0 b0 c0 d0 hspanX0 hspanY0
  apply D.adjacent_rectangles_contradiction_of_max_limits mu
    (B := (B : Real)) (by exact_mod_cast hBpos) hBp hBd a b c d K
  · simpa only [a, b, c, d, q] using hspans.1
  · simpa only [a, b, c, d, q] using hspans.2
  · simpa only [a, b, c, d, q, sheffieldMacroArrayCoordinates,
      Nat.cast_zero, mul_zero, sub_zero, add_zero] using hverticalStart
  · simpa only [a, b, c, d, q] using hhorizontalEnd
  · intro k hk
    have hlim := hprimalAdjacent k hk
    apply hlim.congr'
    filter_upwards with n
    apply congrArg (fun x : Real => x)
    congr 3
    · dsimp only [a, q, sheffieldMacroArrayCoordinates]
      push_cast
      ring
    · dsimp only [b, q, sheffieldMacroArrayCoordinates]
      push_cast
      ring
    · dsimp only [c, q, sheffieldMacroArrayCoordinates]
      push_cast
      ring
    · dsimp only [d, q, sheffieldMacroArrayCoordinates]
      push_cast
      ring
  · intro k
    simpa only [a, b, c, d, q] using hdual k

end StatMech.FK.PeriodicPlanar
