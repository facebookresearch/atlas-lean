/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectInducedConditionalLower
import Code.FK.FKG
import Code.FK.TwoPoint



namespace StatMech.FrontierD

noncomputable section


def fkRectRightStrip (R : FKRectTorus) (cut : Nat) : Set R.Vertex :=
  {v | cut ≤ v.1.val}


def fkRectRightStripBand (R : FKRectTorus)
    (cut lower upper : Nat) : Set R.Vertex :=
  {v | cut ≤ v.1.val ∧ lower ≤ v.2.val ∧ v.2.val ≤ upper}

abbrev FKRectRightStripVertex (R : FKRectTorus) (cut : Nat) :=
  FKRectInducedVertex R (fkRectRightStrip R cut)

abbrev FKRectRightStripBandVertex (R : FKRectTorus)
    (cut lower upper : Nat) :=
  FKRectInducedVertex R (fkRectRightStripBand R cut lower upper)



theorem fkRect_innerEdge_subtype_mk_mem_range_iff
    (R : FKRectTorus) (S : Set R.Vertex) (x y : R.Vertex) :
    s(x, y) ∈ Set.range (FK.ocd_innerEdge
      (Subtype.val : FKRectInducedVertex R S → R.Vertex)) ↔
      x ∈ S ∧ y ∈ S := by
  constructor
  · rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
        rw [FK.ocd_innerEdge_mk, Sym2.eq_iff] at he
        rcases he with he | he
        · exact ⟨he.1 ▸ u.2, he.2 ▸ v.2⟩
        · exact ⟨he.2 ▸ v.2, he.1 ▸ u.2⟩
  · rintro ⟨hx, hy⟩
    exact ⟨s(⟨x, hx⟩, ⟨y, hy⟩), by rw [FK.ocd_innerEdge_mk]⟩


theorem fkRect_verticalSeam_not_innerEdgeRange_of_rowZero_disjoint
    (R : FKRectTorus) (S : Set R.Vertex)
    (hzero : ∀ v ∈ S, v.2.val ≠ 0)
    {e : Sym2 R.Vertex} (he : fkRectCrossesVerticalSeam R e) :
    e ∉ Set.range (FK.ocd_innerEdge
      (Subtype.val : FKRectInducedVertex R S → R.Vertex)) := by
  induction e using Sym2.ind with
  | _ x y =>
      intro hrange
      have hxy := (fkRect_innerEdge_subtype_mk_mem_range_iff R S x y).1
        hrange
      rw [fkRectCrossesVerticalSeam_mk] at he
      rcases he with he | he
      · exact hzero x hxy.1 he.1
      · exact hzero y hxy.2 he.1

theorem fkRect_verticalSeam_not_rightStripBand_innerEdgeRange
    (R : FKRectTorus) (cut lower upper : Nat) (hlower : 1 ≤ lower)
    {e : Sym2 R.Vertex} (he : fkRectCrossesVerticalSeam R e) :
    e ∉ Set.range (FK.ocd_innerEdge
      (Subtype.val : FKRectRightStripBandVertex R cut lower upper →
        R.Vertex)) := by
  apply fkRect_verticalSeam_not_innerEdgeRange_of_rowZero_disjoint R
    (fkRectRightStripBand R cut lower upper) _ he
  intro v hv
  exact Nat.ne_of_gt (Nat.zero_lt_one.trans_le
    (hlower.trans hv.2.1))


def fkRectIndexedPatternEvent (R : FKRectTorus)
    (I : Finset R.EdgeIndex) (eta : R.Configuration) :
    Set R.Configuration :=
  {omega | ∀ a ∈ I, omega a = eta a}

theorem fkRectIndexedPatternEvent_dependsOnOutsideRegion
    (R : FKRectTorus) (S : Set R.Vertex)
    (I : Finset R.EdgeIndex) (eta : R.Configuration)
    (hI : ∀ a ∈ I, fkRectTorusIndexedEdge R a ∉
      Set.range (FK.ocd_innerEdge
        (Subtype.val : FKRectInducedVertex R S → R.Vertex))) :
    FKRectDependsOnOutsideRegion R S
      (fkRectIndexedPatternEvent R I eta) := by
  intro omega tau hot
  constructor
  · intro homega a ha
    exact (hot a (hI a ha)).symm.trans (homega a ha)
  · intro htau a ha
    exact (hot a (hI a ha)).trans (htau a ha)


theorem fkRectVerticalSeamPattern_dependsOnOutsideRightStripBand
    (R : FKRectTorus) (cut lower upper : Nat) (hlower : 1 ≤ lower)
    (I : Finset R.EdgeIndex)
    (hI : ∀ a ∈ I,
      fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a))
    (eta : R.Configuration) :
    FKRectDependsOnOutsideRegion R
      (fkRectRightStripBand R cut lower upper)
      (fkRectIndexedPatternEvent R I eta) := by
  apply fkRectIndexedPatternEvent_dependsOnOutsideRegion
  intro a ha
  exact fkRect_verticalSeam_not_rightStripBand_innerEdgeRange
    R cut lower upper hlower (hI a ha)



def fkRectInducedConnectionChainEvent (R : FKRectTorus)
    (S : Set R.Vertex)
    (t : Finset (FKRectInducedVertex R S × FKRectInducedVertex R S)) :
    Set (ConfigSpace (Sym2 (FKRectInducedVertex R S))) :=
  {omega | ∀ p ∈ t,
    omega ∈ FK.connEvent (fkRectInducedGraph R S) p.1 p.2}

theorem fkRectInducedConnectionChainEvent_isIncreasing
    (R : FKRectTorus) (S : Set R.Vertex)
    (t : Finset (FKRectInducedVertex R S × FKRectInducedVertex R S)) :
    IsIncreasing (fkRectInducedConnectionChainEvent R S t) := by
  intro omega tau hot hmem p hp
  exact FK.connEvent_isIncreasing (fkRectInducedGraph R S) p.1 p.2
    hot (hmem p hp)



theorem fkRectInduced_connectionChain_ge_prod
    (R : FKRectTorus) (S : Set R.Vertex)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (t : Finset (FKRectInducedVertex R S × FKRectInducedVertex R S)) :
    (∏ xy ∈ t,
        FK.twoPointFun (fkRectInducedGraph R S) p q xy.1 xy.2) ≤
      ∑ omega,
        FK.fkProb (fkRectInducedGraph R S) p q omega *
          (fkRectInducedConnectionChainEvent R S t).indicator
            (fun _ => (1 : Real)) omega := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp [fkRectInducedConnectionChainEvent,
        FK.fkProb_sum_eq_one (fkRectInducedGraph R S) hp hp1
          (lt_of_lt_of_le zero_lt_one hq)]
  | @insert xy t hxy ih =>
      have hconn : IsIncreasing
          (FK.connEvent (fkRectInducedGraph R S) xy.1 xy.2) :=
        FK.connEvent_isIncreasing _ _ _
      have hchain : IsIncreasing
          (fkRectInducedConnectionChainEvent R S t) :=
        fkRectInducedConnectionChainEvent_isIncreasing R S t
      have hnonneg : 0 ≤
          FK.twoPointFun (fkRectInducedGraph R S) p q xy.1 xy.2 :=
        FK.twoPointFun_nonneg (fkRectInducedGraph R S) hp hp1
          (lt_of_lt_of_le zero_lt_one hq) _ _
      calc
        (∏ z ∈ insert xy t,
            FK.twoPointFun (fkRectInducedGraph R S) p q z.1 z.2) =
            FK.twoPointFun (fkRectInducedGraph R S) p q xy.1 xy.2 *
              ∏ z ∈ t,
                FK.twoPointFun (fkRectInducedGraph R S) p q z.1 z.2 := by
          rw [Finset.prod_insert hxy]
        _ ≤ FK.twoPointFun (fkRectInducedGraph R S) p q xy.1 xy.2 *
              ∑ omega,
                FK.fkProb (fkRectInducedGraph R S) p q omega *
                  (fkRectInducedConnectionChainEvent R S t).indicator
                    (fun _ => (1 : Real)) omega :=
          mul_le_mul_of_nonneg_left ih hnonneg
        _ ≤ ∑ omega,
              FK.fkProb (fkRectInducedGraph R S) p q omega *
                (FK.connEvent (fkRectInducedGraph R S) xy.1 xy.2 ∩
                  fkRectInducedConnectionChainEvent R S t).indicator
                    (fun _ => (1 : Real)) omega := by
          exact FK.fkProb_positively_associated_events
            (fkRectInducedGraph R S) hp hp1 hq hconn hchain
        _ = ∑ omega,
              FK.fkProb (fkRectInducedGraph R S) p q omega *
                (fkRectInducedConnectionChainEvent R S
                  (insert xy t)).indicator
                    (fun _ => (1 : Real)) omega := by
          apply Finset.sum_congr rfl
          intro omega _
          congr 1
          congr 1
          ext
          simp [fkRectInducedConnectionChainEvent, hxy]



theorem fkRectInduced_connectionProduct_mul_outsideMass_le_genericInter
    (R : FKRectTorus) (S : Set R.Vertex)
    {q : Real} (hq : 1 ≤ q)
    (t : Finset (FKRectInducedVertex R S × FKRectInducedVertex R S))
    {B : Set R.Configuration}
    (hB : FKRectDependsOnOutsideRegion R S B) :
    (∏ xy ∈ t,
        FK.twoPointFun (fkRectInducedGraph R S)
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q B ≤
      ∑ rho,
        ((FK.ocd_innerRestrict
            (Subtype.val : FKRectInducedVertex R S → R.Vertex) ⁻¹'
              fkRectInducedConnectionChainEvent R S t) ∩
          fkRectFullGraphEvent R B).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp := fkRectCriticalP_pos hq0
  have hp1 := fkRectCriticalP_lt_one hq0
  have hprod := fkRectInduced_connectionChain_ge_prod R
    S hp hp1 hq t
  have hBnonneg := fkRectCriticalEventMass_nonneg R hq0 B
  have hlower :=
    fkRectInduced_freeMass_mul_indexedOutsideMass_le_genericInter R
      S hq
      (fkRectInducedConnectionChainEvent_isIncreasing R
        S t) hB
  have hmass :
      (∑ omega,
          FK.fkProb (fkRectInducedGraph R S)
              (fkRectCriticalP q) q omega *
            (fkRectInducedConnectionChainEvent R S t).indicator
                (fun _ => (1 : Real)) omega) =
        ∑ omega,
          (fkRectInducedConnectionChainEvent R S t).indicator
                (fun _ => (1 : Real)) omega *
            FK.fkProb (fkRectInducedGraph R S)
              (fkRectCriticalP q) q omega := by
    apply Finset.sum_congr rfl
    intro omega _
    ring
  calc
    _ ≤ (∑ omega,
          FK.fkProb (fkRectInducedGraph R S)
              (fkRectCriticalP q) q omega *
            (fkRectInducedConnectionChainEvent R S t).indicator
                (fun _ => (1 : Real)) omega) *
          fkRectCriticalEventMass R q B :=
      mul_le_mul_of_nonneg_right hprod hBnonneg
    _ = (∑ omega,
          (fkRectInducedConnectionChainEvent R S t).indicator
                (fun _ => (1 : Real)) omega *
            FK.fkProb (fkRectInducedGraph R S)
              (fkRectCriticalP q) q omega) *
          fkRectCriticalEventMass R q B := by rw [hmass]
    _ ≤ _ := hlower


theorem fkRectRightStrip_connectionProduct_mul_outsideMass_le_genericInter
    (R : FKRectTorus) (cut : Nat)
    {q : Real} (hq : 1 ≤ q)
    (t : Finset (FKRectRightStripVertex R cut ×
      FKRectRightStripVertex R cut))
    {B : Set R.Configuration}
    (hB : FKRectDependsOnOutsideRegion R (fkRectRightStrip R cut) B) :
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R (fkRectRightStrip R cut))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q B ≤
      ∑ rho,
        ((FK.ocd_innerRestrict
            (Subtype.val : FKRectRightStripVertex R cut → R.Vertex) ⁻¹'
              fkRectInducedConnectionChainEvent R
                (fkRectRightStrip R cut) t) ∩
          fkRectFullGraphEvent R B).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho :=
  fkRectInduced_connectionProduct_mul_outsideMass_le_genericInter R
    (fkRectRightStrip R cut) hq t hB


theorem fkRectRightStripBand_connectionProduct_mul_outsideMass_le_genericInter
    (R : FKRectTorus) (cut lower upper : Nat)
    {q : Real} (hq : 1 ≤ q)
    (t : Finset (FKRectRightStripBandVertex R cut lower upper ×
      FKRectRightStripBandVertex R cut lower upper))
    {B : Set R.Configuration}
    (hB : FKRectDependsOnOutsideRegion R
      (fkRectRightStripBand R cut lower upper) B) :
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut lower upper))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q B ≤
      ∑ rho,
        ((FK.ocd_innerRestrict
            (Subtype.val :
              FKRectRightStripBandVertex R cut lower upper → R.Vertex) ⁻¹'
              fkRectInducedConnectionChainEvent R
                (fkRectRightStripBand R cut lower upper) t) ∩
          fkRectFullGraphEvent R B).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho :=
  fkRectInduced_connectionProduct_mul_outsideMass_le_genericInter R
    (fkRectRightStripBand R cut lower upper) hq t hB

end

end StatMech.FrontierD
