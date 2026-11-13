/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDevelopedSquareReflection



open Set

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section



def fkRectDevelopedThreeByOneRect (n : Nat) : Set (Site 2) :=
  rect 0 (3 * (n : Int)) 0 n



noncomputable def fkRectDevelopedThreeByOneVerticalEndpointPairs (n : Nat) :
    Finset ((fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) := by
  classical
  letI : Fintype (fkRectDevelopedThreeByOneRect n) := by
    rw [fkRectDevelopedThreeByOneRect]
    exact (rect_finite 0 (3 * (n : Int)) 0 n).fintype
  exact Finset.univ.filter fun p => p.1.1 1 = 0 ∧ p.2.1 1 = n

theorem mem_fkRectDevelopedThreeByOneVerticalEndpointPairs
    (n : Nat)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) :
    p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n ↔
      p.1.1 1 = 0 ∧ p.2.1 1 = n := by
  classical
  unfold fkRectDevelopedThreeByOneVerticalEndpointPairs
  simp



def fkRectDevelopedThreeByOneEndpointConnectionEvent
    (R : FKRectTorus) (n : Nat)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) : Set R.Configuration :=
  {omega | ConnectedWithin 2 (fkRectDevelopedSquarePullback R n omega)
    (fkRectDevelopedThreeByOneRect n) p.1 p.2}



theorem fkRectDevelopedThreeByOne_undevelop_bounds
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {z : Site 2} (hz : z ∈ fkRectDevelopedThreeByOneRect n) :
    let p := fkRectSquareUndevelopPoint (fkRectDevelopedSquarePoint n z)
    0 ≤ p.1 ∧ p.1 < R.width ∧ 0 ≤ p.2 ∧ p.2 < R.height := by
  change z ∈ rect 0 (3 * (n : Int)) 0 n at hz
  rw [mem_rect] at hz
  dsimp [fkRectDevelopedSquarePoint, fkRectSquareUndevelopPoint]
  have hhalfLower : 0 ≤ (z 0 - z 1 + (n : Int)) / 2 := by omega
  have hhalfUpper : (z 0 - z 1 + (n : Int)) / 2 ≤ 2 * n := by
    omega
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

theorem fkRectVertexSquarePoint_developedThreeByOneVertex
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {z : Site 2} (hz : z ∈ fkRectDevelopedThreeByOneRect n) :
    fkRectVertexSquarePoint R (fkRectDevelopedSquareVertex R n z) =
      fkRectDevelopedSquarePoint n z := by
  let t := fkRectDevelopedSquarePoint n z
  let p := fkRectSquareUndevelopPoint t
  have hp := fkRectDevelopedThreeByOne_undevelop_bounds
    R n hwidth hheight hz
  change fkRectSquareDevelopPoint
      (((fkRectSquareRepresentativeVertex R t).1.val : Int),
        ((fkRectSquareRepresentativeVertex R t).2.val : Int)) = t
  have hx : ((fkRectSquareRepresentativeVertex R t).1.val : Int) = p.1 := by
    change ((p.1.natMod R.width : Nat) : Int) = p.1
    rw [Int.natMod, Int.emod_eq_of_lt hp.1 hp.2.1]
    exact Int.natCast_toNat_eq_self.mpr hp.1
  have hy : ((fkRectSquareRepresentativeVertex R t).2.val : Int) = p.2 := by
    change ((p.2.natMod R.height : Nat) : Int) = p.2
    rw [Int.natMod, Int.emod_eq_of_lt hp.2.2.1 hp.2.2.2]
    exact Int.natCast_toNat_eq_self.mpr hp.2.2.1
  rw [hx, hy]
  exact fkRectSquareDevelopPoint_undevelopPoint t

theorem fkRectVertexSquareSite_developedThreeByOneVertex
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {z : Site 2} (hz : z ∈ fkRectDevelopedThreeByOneRect n) :
    fkRectVertexSquareSite R (fkRectDevelopedSquareVertex R n z) =
      fkRectDevelopedSquareSite n z := by
  unfold fkRectVertexSquareSite fkRectDevelopedSquareSite
  rw [fkRectVertexSquarePoint_developedThreeByOneVertex
    R n hwidth hheight hz]

theorem fkRectDevelopedThreeByOneVertex_cutGraph_adj
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {z w : Site 2} (hz : z ∈ fkRectDevelopedThreeByOneRect n)
    (hw : w ∈ fkRectDevelopedThreeByOneRect n)
    (hzw : (hypercubicLattice 2).Adj z w) :
    (fkRectCutGraph R).Adj
      (fkRectDevelopedSquareVertex R n z)
      (fkRectDevelopedSquareVertex R n w) := by
  rw [fkRectCutGraph_adj_iff_hypercubicAdj,
    fkRectVertexSquareSite_developedThreeByOneVertex R n
      hwidth hheight hz,
    fkRectVertexSquareSite_developedThreeByOneVertex R n
      hwidth hheight hw]
  rw [hypercubicLattice_adj] at hzw ⊢
  simpa [fkRectDevelopedSquareSite, fkRectDevelopedSquarePoint,
    fkRectSquareSiteOfPair, Fin.sum_univ_two] using hzw

theorem fkRectDevelopedThreeByOnePullback_open_iff
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration) {z w : Site 2}
    (hz : z ∈ fkRectDevelopedThreeByOneRect n)
    (hw : w ∈ fkRectDevelopedThreeByOneRect n)
    (hzw : (hypercubicLattice 2).Adj z w) :
    fkRectDevelopedSquarePullback R n omega s(z, w) = true ↔
      (fkRectOpenGraph R omega).Adj
        (fkRectDevelopedSquareVertex R n z)
        (fkRectDevelopedSquareVertex R n w) := by
  have hcut := fkRectDevelopedThreeByOneVertex_cutGraph_adj R n
    hwidth hheight hz hw hzw
  have htorus : (fkRectTorusGraph R).Adj
      (fkRectDevelopedSquareVertex R n z)
      (fkRectDevelopedSquareVertex R n w) :=
    ((fkRectCutGraph_adj_iff R _ _).mp hcut).1
  rw [← fkOpenSub_fullGraphConfiguration]
  rw [StatMech.FK.openSub_adj]
  constructor
  · intro hopen
    refine ⟨htorus, ?_⟩
    simpa [fkRectDevelopedSquarePullback] using hopen
  · rintro ⟨_, hopen⟩
    simpa [fkRectDevelopedSquarePullback] using hopen

noncomputable def fkRectDevelopedThreeByOneOpenHom
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration) :
    (openSubgraph 2 (fkRectDevelopedSquarePullback R n omega)).induce
        (fkRectDevelopedThreeByOneRect n) →g
      fkRectOpenGraph R omega where
  toFun z := fkRectDevelopedSquareVertex R n z
  map_rel' := by
    intro z w hzw
    change (openSubgraph 2
      (fkRectDevelopedSquarePullback R n omega)).Adj z.1 w.1 at hzw
    rw [openSubgraph_adj] at hzw
    exact (fkRectDevelopedThreeByOnePullback_open_iff
      R n hwidth hheight omega z.2 w.2 hzw.1).mp hzw.2



theorem fkRectDevelopedThreeByOneEndpointConnection_imp_torusReachable
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n))
    (hconn : omega ∈
      fkRectDevelopedThreeByOneEndpointConnectionEvent R n p) :
    (fkRectOpenGraph R omega).Reachable
      (fkRectDevelopedSquareVertex R n p.1)
      (fkRectDevelopedSquareVertex R n p.2) := by
  exact hconn.map
    (fkRectDevelopedThreeByOneOpenHom R n hwidth hheight omega)

def fkRectDevelopedThreeByOneTorusEndpointConnectionEvent
    (R : FKRectTorus) (n : Nat)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) : Set R.Configuration :=
  {omega | (fkRectOpenGraph R omega).Reachable
    (fkRectDevelopedSquareVertex R n p.1)
    (fkRectDevelopedSquareVertex R n p.2)}

theorem fkRectDevelopedThreeByOneTorusEndpointConnectionEvent_isIncreasing
    (R : FKRectTorus) (n : Nat)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) :
    IsIncreasing
      (fkRectDevelopedThreeByOneTorusEndpointConnectionEvent R n p) := by
  intro omega tau hot hconn
  apply hconn.mono
  apply fkRectOpenGraph_mono R
  intro e he
  have hle := hot e
  rw [he] at hle
  exact top_le_iff.mp hle

theorem fkRectDevelopedThreeByOneEndpointConnection_subset_torus
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) :
    fkRectDevelopedThreeByOneEndpointConnectionEvent R n p ⊆
      fkRectDevelopedThreeByOneTorusEndpointConnectionEvent R n p := by
  intro omega hconn
  exact fkRectDevelopedThreeByOneEndpointConnection_imp_torusReachable
    R n hwidth hheight omega p hconn

theorem fkRectDevelopedThreeByOneEndpointConnectionEvent_isIncreasing
    (R : FKRectTorus) (n : Nat)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) :
    IsIncreasing
      (fkRectDevelopedThreeByOneEndpointConnectionEvent R n p) := by
  intro omega tau hot hconn
  exact StatMech.TwoDim.connectedWithin_mono
    (fkRectDevelopedSquarePullback_mono R n hot) hconn

theorem fkRectDevelopedThreeByOneVerticalCrossingEvent_eq_endpointUnion
    (R : FKRectTorus) (n : Nat) :
    fkRectDevelopedRectangleVerticalCrossingEvent
        R n 0 (3 * (n : Int)) 0 n =
      fkRectFiniteEventUnion
        (fkRectDevelopedThreeByOneVerticalEndpointPairs n)
        (fkRectDevelopedThreeByOneEndpointConnectionEvent R n) := by
  ext omega
  constructor
  · rintro ⟨x, y, hxy⟩
    let p : (fkRectDevelopedThreeByOneRect n) ×
        (fkRectDevelopedThreeByOneRect n) :=
      (⟨x.1, x.2.1⟩, ⟨y.1, y.2.1⟩)
    refine ⟨p, ?_, ?_⟩
    · classical
      simp [fkRectDevelopedThreeByOneVerticalEndpointPairs, p,
        x.2.2, y.2.2]
    · simpa [fkRectDevelopedThreeByOneEndpointConnectionEvent, p,
        fkRectDevelopedThreeByOneRect] using hxy
  · rintro ⟨p, hp, hxy⟩
    have hend : p.1.1 1 = 0 ∧ p.2.1 1 = n :=
      (mem_fkRectDevelopedThreeByOneVerticalEndpointPairs n p).mp hp
    refine ⟨⟨p.1.1, p.1.2, hend.1⟩,
      ⟨p.2.1, p.2.2, hend.2⟩, ?_⟩
    simpa [fkRectDevelopedThreeByOneEndpointConnectionEvent,
      fkRectDevelopedThreeByOneRect] using hxy

theorem fkRectDevelopedThreeByOneVerticalEndpointPairs_nonempty (n : Nat) :
    (fkRectDevelopedThreeByOneVerticalEndpointPairs n).Nonempty := by
  classical
  let x : Site 2 := ![0, 0]
  let y : Site 2 := ![0, (n : Int)]
  have hx : x ∈ fkRectDevelopedThreeByOneRect n := by
    simp [fkRectDevelopedThreeByOneRect, mem_rect, x]
  have hy : y ∈ fkRectDevelopedThreeByOneRect n := by
    simp [fkRectDevelopedThreeByOneRect, mem_rect, y]
  refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩
  simp [fkRectDevelopedThreeByOneVerticalEndpointPairs, x, y]


theorem fkRectDevelopedThreeByOneVerticalEndpointPairs_card_le (n : Nat) :
    (fkRectDevelopedThreeByOneVerticalEndpointPairs n).card ≤
      (3 * n + 1) ^ 2 := by
  classical
  let encode :
      {p // p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n} →
        Fin (3 * n + 1) × Fin (3 * n + 1) := fun p =>
    (⟨Int.toNat (p.1.1.1 0), by
        have hp := p.1.1.2
        change p.1.1.1 ∈ rect 0 (3 * (n : Int)) 0 n at hp
        rw [mem_rect] at hp
        omega⟩,
      ⟨Int.toNat (p.1.2.1 0), by
        have hp := p.1.2.2
        change p.1.2.1 ∈ rect 0 (3 * (n : Int)) 0 n at hp
        rw [mem_rect] at hp
        omega⟩)
  have hinj : Function.Injective encode := by
    intro p r hpr
    have hpEnds :=
      (mem_fkRectDevelopedThreeByOneVerticalEndpointPairs n p.1).mp p.2
    have hrEnds :=
      (mem_fkRectDevelopedThreeByOneVerticalEndpointPairs n r.1).mp r.2
    have hfirst : Int.toNat (p.1.1.1 0) =
        Int.toNat (r.1.1.1 0) := congrArg (fun z => z.1.val) hpr
    have hsecond : Int.toNat (p.1.2.1 0) =
        Int.toNat (r.1.2.1 0) := congrArg (fun z => z.2.val) hpr
    have hp1 := p.1.1.2
    have hp2 := p.1.2.2
    have hr1 := r.1.1.2
    have hr2 := r.1.2.2
    change p.1.1.1 ∈ rect 0 (3 * (n : Int)) 0 n at hp1
    change p.1.2.1 ∈ rect 0 (3 * (n : Int)) 0 n at hp2
    change r.1.1.1 ∈ rect 0 (3 * (n : Int)) 0 n at hr1
    change r.1.2.1 ∈ rect 0 (3 * (n : Int)) 0 n at hr2
    rw [mem_rect] at hp1 hp2 hr1 hr2
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply funext
      intro i
      fin_cases i
      · calc
          p.1.1.1 0 = (Int.toNat (p.1.1.1 0) : Int) :=
            (Int.toNat_of_nonneg hp1.1).symm
          _ = (Int.toNat (r.1.1.1 0) : Int) := by exact_mod_cast hfirst
          _ = r.1.1.1 0 := Int.toNat_of_nonneg hr1.1
      · exact hpEnds.1.trans hrEnds.1.symm
    · apply Subtype.ext
      apply funext
      intro i
      fin_cases i
      · calc
          p.1.2.1 0 = (Int.toNat (p.1.2.1 0) : Int) :=
            (Int.toNat_of_nonneg hp2.1).symm
          _ = (Int.toNat (r.1.2.1 0) : Int) := by exact_mod_cast hsecond
          _ = r.1.2.1 0 := Int.toNat_of_nonneg hr2.1
      · exact hpEnds.2.trans hrEnds.2.symm
  rw [← Fintype.card_coe]
  calc
    Fintype.card
        {p // p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n} ≤
      Fintype.card (Fin (3 * n + 1) × Fin (3 * n + 1)) :=
        Fintype.card_le_of_injective encode hinj
    _ = (3 * n + 1) ^ 2 := by simp [pow_two]


theorem fkRectCritical_developedThreeByOne_exists_endpoint_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 <= n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 <= q) :
    ∃ p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n,
      1 / (2 * (1 + q)) ≤ ((3 * n + 1) ^ 2 : Nat) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedThreeByOneEndpointConnectionEvent R n p) := by
  have hcross := fkRectCritical_developedThreeByOneVerticalMass_ge
    R n hn hwidth hheight hq
  rw [fkRectDevelopedThreeByOneVerticalCrossingEvent_eq_endpointUnion]
    at hcross
  obtain ⟨p, hp, hlower⟩ := exists_card_mul_eventMass_ge_of_finiteUnion_ge
    R (zero_lt_one.trans_le hq)
    (fkRectDevelopedThreeByOneVerticalEndpointPairs_nonempty n)
    (fkRectDevelopedThreeByOneEndpointConnectionEvent R n) hcross
  refine ⟨p, hp, hlower.trans ?_⟩
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast fkRectDevelopedThreeByOneVerticalEndpointPairs_card_le n
  · exact fkRectCriticalEventMass_nonneg R
      (zero_lt_one.trans_le hq) _



theorem fkRectCritical_developedThreeByOne_exists_torus_endpoint_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 <= n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q : Real} (hq : 1 <= q) :
    ∃ p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n,
      1 / (2 * (1 + q)) ≤ ((3 * n + 1) ^ 2 : Nat) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedThreeByOneTorusEndpointConnectionEvent R n p) := by
  have hwidth3 : 3 * n < R.width := by omega
  have hheight3 : 3 * n < R.height := by omega
  obtain ⟨p, hp, hlower⟩ :=
    fkRectCritical_developedThreeByOne_exists_endpoint_ge
      R n hn hwidth3 hheight3 hq
  refine ⟨p, hp, hlower.trans ?_⟩
  apply mul_le_mul_of_nonneg_left
  · exact fkRectCriticalEventMass_mono R (zero_lt_one.trans_le hq)
      (fkRectDevelopedThreeByOneEndpointConnection_subset_torus
        R n hwidth hheight p)
  · positivity

end

end StatMech.FrontierD
