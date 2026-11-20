/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace
import Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove










open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent
open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaSequentialExchangeDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


noncomputable def lpReplicaBalancedComponentBoundary
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    Finset (LPReplicaCurrentVertex V) :=
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K0 := lpReplicaRowCopies G sites m tag false
  let K1 := lpReplicaRowCopies G sites m tag true
  (A ∩ StatMech.Sharpness.RandomCurrent.compOf e K0
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)) ∆
    (B ∩ StatMech.Sharpness.RandomCurrent.compOf e K1
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V))




theorem lpReplicaBalancedComponentSelector_sources_general
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    StatMech.Sharpness.RandomCurrent.sources e
          ((lpReplicaBalancedComponentSelector G sites m tag).filter
            fun c => (tag c).2 = false) =
        lpReplicaBalancedComponentBoundary G sites m A B tag ∧
      StatMech.Sharpness.RandomCurrent.sources e
          ((lpReplicaBalancedComponentSelector G sites m tag).filter
            fun c => (tag c).2 = true) = ∅ := by
  classical
  dsimp only
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K0 := lpReplicaRowCopies G sites m tag false
  let K1 := lpReplicaRowCopies G sites m tag true
  let C0 := edgeComponent e K0
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
  let C1 := edgeComponent e K1
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  have hC0 : C0 ⊆ K0 := by
    intro c hc
    change c ∈ edgeComponent e K0 lpReplicaCurrentGhost1 at hc
    rw [edgeComponent, Finset.mem_filter] at hc
    exact hc.1
  have hC1 : C1 ⊆ K1 := by
    intro c hc
    change c ∈ edgeComponent e K1 lpReplicaCurrentGhost0 at hc
    rw [edgeComponent, Finset.mem_filter] at hc
    exact hc.1
  have hrows : Disjoint K0 K1 := by
    rw [Finset.disjoint_left]
    intro c hc0 hc1
    simp only [K0, K1, lpReplicaRowCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] at hc0 hc1
    exact Bool.false_ne_true (hc0.symm.trans hc1)
  have hcomponents : Disjoint C0 C1 := hrows.mono hC0 hC1
  have hinter (current : Bool) : Disjoint
      (lpReplicaCurrentCopies G sites m tag false current ∩ C0)
      (lpReplicaCurrentCopies G sites m tag true current ∩ C1) :=
    hcomponents.mono Finset.inter_subset_right Finset.inter_subset_right
  have hcurrent0 (current : Bool) :
      lpReplicaCurrentCopies G sites m tag false current ⊆ K0 :=
    lpReplicaCurrentCopies_subset_rowCopies G sites m tag false current
  have hcurrent1 (current : Bool) :
      lpReplicaCurrentCopies G sites m tag true current ⊆ K1 :=
    lpReplicaCurrentCopies_subset_rowCopies G sites m tag true current
  constructor
  · rw [lpReplicaBalancedComponentSelector_filter G sites m tag false,
      sources_union_of_disjoint (hinter false),
      sources_inter_edgeComponent (hcurrent0 false),
      sources_inter_edgeComponent (hcurrent1 false),
      hgate.1, hgate.2.2.2.1]
    rfl
  · rw [lpReplicaBalancedComponentSelector_filter G sites m tag true,
      sources_union_of_disjoint (hinter true),
      sources_inter_edgeComponent (hcurrent0 true),
      sources_inter_edgeComponent (hcurrent1 true),
      hgate.2.1, hgate.2.2.2.2.1]
    simp




theorem lpReplicaBalancedComponentSelector_rowCurrentSources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m B ∅ tag) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    let P := lpReplicaBalancedComponentSelector G sites m tag
    let X := lpReplicaBalancedComponentBoundary G sites m B ∅ tag
    StatMech.Sharpness.RandomCurrent.sources e
        (lpReplicaCurrentCopies G sites m tag false false ∩ P) = X ∧
      StatMech.Sharpness.RandomCurrent.sources e
        (lpReplicaCurrentCopies G sites m tag true false ∩ P) = ∅ ∧
      StatMech.Sharpness.RandomCurrent.sources e
        (lpReplicaCurrentCopies G sites m tag false true ∩ P) = ∅ ∧
      StatMech.Sharpness.RandomCurrent.sources e
        (lpReplicaCurrentCopies G sites m tag true true ∩ P) = ∅ := by
  classical
  dsimp only
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K0 := lpReplicaRowCopies G sites m tag false
  let K1 := lpReplicaRowCopies G sites m tag true
  let C0 := edgeComponent e K0
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
  let C1 := edgeComponent e K1
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  have hC0 : C0 ⊆ K0 := by
    intro c hc
    change c ∈ edgeComponent e K0 lpReplicaCurrentGhost1 at hc
    rw [edgeComponent, Finset.mem_filter] at hc
    exact hc.1
  have hC1 : C1 ⊆ K1 := by
    intro c hc
    change c ∈ edgeComponent e K1 lpReplicaCurrentGhost0 at hc
    rw [edgeComponent, Finset.mem_filter] at hc
    exact hc.1
  have hrow0 (current : Bool) :
      lpReplicaCurrentCopies G sites m tag false current ∩ (C0 ∪ C1) =
        lpReplicaCurrentCopies G sites m tag false current ∩ C0 := by
    ext c
    have hc1 := @hC1 c
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hc, hc0 | hc1'⟩
      · exact ⟨hc, hc0⟩
      · have htag0 := hc
        have htag1 := hc1 hc1'
        simp only [lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] at htag0
        simp only [K1, lpReplicaRowCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] at htag1
        exact False.elim (Bool.false_ne_true
          ((congrArg Prod.fst htag0).symm.trans htag1))
    · exact fun hc => ⟨hc.1, Or.inl hc.2⟩
  have hrow1 (current : Bool) :
      lpReplicaCurrentCopies G sites m tag true current ∩ (C0 ∪ C1) =
        lpReplicaCurrentCopies G sites m tag true current ∩ C1 := by
    ext c
    have hc0 := @hC0 c
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hc, hc0' | hc1⟩
      · have htag1 := hc
        have htag0 := hc0 hc0'
        simp only [lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] at htag1
        simp only [K0, lpReplicaRowCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] at htag0
        exact False.elim (Bool.false_ne_true
          (htag0.symm.trans (congrArg Prod.fst htag1)))
      · exact ⟨hc, hc1⟩
    · exact fun hc => ⟨hc.1, Or.inr hc.2⟩
  have hcurrent0 (current : Bool) :
      lpReplicaCurrentCopies G sites m tag false current ⊆ K0 :=
    lpReplicaCurrentCopies_subset_rowCopies G sites m tag false current
  have hcurrent1 (current : Bool) :
      lpReplicaCurrentCopies G sites m tag true current ⊆ K1 :=
    lpReplicaCurrentCopies_subset_rowCopies G sites m tag true current
  change StatMech.Sharpness.RandomCurrent.sources e
      (lpReplicaCurrentCopies G sites m tag false false ∩ (C0 ∪ C1)) = _ ∧
    StatMech.Sharpness.RandomCurrent.sources e
      (lpReplicaCurrentCopies G sites m tag true false ∩ (C0 ∪ C1)) = _ ∧
    StatMech.Sharpness.RandomCurrent.sources e
      (lpReplicaCurrentCopies G sites m tag false true ∩ (C0 ∪ C1)) = _ ∧
    StatMech.Sharpness.RandomCurrent.sources e
      (lpReplicaCurrentCopies G sites m tag true true ∩ (C0 ∪ C1)) = _
  rw [hrow0 false, hrow1 false, hrow0 true, hrow1 true,
    sources_inter_edgeComponent (hcurrent0 false),
    sources_inter_edgeComponent (hcurrent1 false),
    sources_inter_edgeComponent (hcurrent0 true),
    sources_inter_edgeComponent (hcurrent1 true),
    hgate.1, hgate.2.2.2.1, hgate.2.1, hgate.2.2.2.2.1]
  simp [lpReplicaBalancedComponentBoundary, K0, K1]
  dsimp only [e]
  ext x
  simp [Finset.mem_symmDiff]



theorem lpReplicaBalancedComponentSelector_disconnects_general
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag) :
    let moved := lpReplicaToggleRows G sites m
      (lpReplicaBalancedComponentSelector G sites m tag) tag
    (¬ StatMech.Sharpness.RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m moved false)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) ∧
      ¬ StatMech.Sharpness.RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m moved true)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  classical
  dsimp only
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K0 := lpReplicaRowCopies G sites m tag false
  let K1 := lpReplicaRowCopies G sites m tag true
  let C0 := edgeComponent e K0
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
  let C1 := edgeComponent e K1
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  have hC0 : C0 ⊆ K0 := by
    intro c hc
    change c ∈ edgeComponent e K0 lpReplicaCurrentGhost1 at hc
    rw [edgeComponent, Finset.mem_filter] at hc
    exact hc.1
  have hC1 : C1 ⊆ K1 := by
    intro c hc
    change c ∈ edgeComponent e K1 lpReplicaCurrentGhost0 at hc
    rw [edgeComponent, Finset.mem_filter] at hc
    exact hc.1
  have hrows : Disjoint K0 K1 := by
    rw [Finset.disjoint_left]
    intro c hc0 hc1
    simp only [K0, K1, lpReplicaRowCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] at hc0 hc1
    exact Bool.false_ne_true (hc0.symm.trans hc1)
  have hrow0 :
      lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m
            (lpReplicaBalancedComponentSelector G sites m tag) tag) false =
        exchangeFirstRow e K0 K1
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 := by
    rw [lpReplicaRowCopies_toggle]
    change K0 ∆ (C0 ∪ C1) = _
    rw [symmDiff_componentExchange_first hC0 hC1 hrows]
    rfl
  have hrow1 :
      lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m
            (lpReplicaBalancedComponentSelector G sites m tag) tag) true =
        exchangeSecondRow e K0 K1
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 := by
    rw [lpReplicaRowCopies_toggle]
    change K1 ∆ (C0 ∪ C1) = _
    rw [symmDiff_componentExchange_second hC0 hC1 hrows]
    rfl
  rw [hrow0, hrow1]
  exact componentExchange_disconnects
    (show (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ≠
      lpReplicaCurrentGhost1 by
        simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])
    hgate.2.2.1 hgate.2.2.2.2.2



theorem lpReplicaRowGate_balancedComponentExchange_general
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag) :
    let D := lpReplicaBalancedComponentBoundary G sites m A B tag
    LPReplicaRowGate G sites m (A ∆ D) (B ∆ D)
      (lpReplicaToggleRows G sites m
        (lpReplicaBalancedComponentSelector G sites m tag) tag) := by
  dsimp only
  have hsources := lpReplicaBalancedComponentSelector_sources_general
    G sites m A B tag hgate
  have hdisc := lpReplicaBalancedComponentSelector_disconnects_general
    G sites m A B tag hgate
  have h := lpReplicaRowGate_toggle G sites m A B tag
    (lpReplicaBalancedComponentSelector G sites m tag) hgate hsources.2
    hdisc.1 hdisc.2
  dsimp only at h
  rw [hsources.1] at h
  exact h




def lpReplicaCoupledReflectToggleTagRaw
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :=
  lpReplicaPartialReflectTagRaw G sites m P
    (lpReplicaToggleRows G sites m P tag)

set_option maxHeartbeats 800000 in




theorem lpReplicaCoupledReflectToggle_currentSources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
      (profileFlux (lpReplicaCurrentGraph G sites) m P)
    let T := lpReplicaCurrentCopies G sites m tag row current
    let U := lpReplicaCurrentCopies G sites m tag (!row) current
    StatMech.Sharpness.RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites) target)
        (lpReplicaCurrentCopies G sites target
          (lpReplicaCoupledReflectToggleTagRaw G sites m P tag)
          row current) =
      (StatMech.Sharpness.RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites) m) T ∆
        StatMech.Sharpness.RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites) m) (T ∩ P)) ∆
        (StatMech.Sharpness.RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites) m) (U ∩ P)).map
            lpReplicaCurrentReflect.toEmbedding := by
  classical
  dsimp only
  unfold lpReplicaCoupledReflectToggleTagRaw
  let T := lpReplicaCurrentCopies G sites m tag row current
  let U := lpReplicaCurrentCopies G sites m tag (!row) current
  let Q := P.filter fun c => (tag c).2 = current
  have houtside : (T ∆ Q) \ P = T \ P := by
    ext c
    rcases htag : tag c with ⟨r, q⟩
    cases r <;> cases q <;> cases row <;> cases current <;>
      simp [T, Q, lpReplicaCurrentCopies, htag, Finset.mem_symmDiff]
  have hinside : (T ∆ Q) ∩ P = U ∩ P := by
    ext c
    rcases htag : tag c with ⟨r, q⟩
    cases r <;> cases q <;> cases row <;> cases current <;>
      simp [T, U, Q, lpReplicaCurrentCopies, htag, Finset.mem_symmDiff]
  have hinter : T ∩ P ⊆ T := Finset.inter_subset_left
  have hdiff : T \ P = T \ (T ∩ P) := by
    ext c
    simp
  rw [lpReplicaCurrentCopies_partialReflectTagRaw,
    lpReplicaCurrentCopies_toggle,
    lpReplicaPartialReflectCopiesRaw_sources,
    houtside, hinside, hdiff,
    sources_sdiff_of_subset hinter]



theorem lpReplicaCurrentReflect_map_involutive
    (X : Finset (LPReplicaCurrentVertex V)) :
    (X.map lpReplicaCurrentReflect.toEmbedding).map
        lpReplicaCurrentReflect.toEmbedding = X := by
  ext x
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, hzy⟩, hyx⟩
    change lpReplicaCurrentReflect z = y at hzy
    change lpReplicaCurrentReflect y = x at hyx
    subst y
    rw [lpReplicaCurrentReflect_involutive] at hyx
    simpa [← hyx] using hz
  · intro hx
    refine ⟨lpReplicaCurrentReflect x, ?_,
      lpReplicaCurrentReflect_involutive x⟩
    exact ⟨x, hx, rfl⟩




theorem lpReplicaRowGate_coupledReflectToggle
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (A B X0 X1 Z0 Z1 : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (hfalse0 : StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentCopies G sites m tag false false ∩ P) = X0)
    (hfalse1 : StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentCopies G sites m tag true false ∩ P) = X1)
    (htrue0 : StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentCopies G sites m tag false true ∩ P) = Z0)
    (htrue1 : StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentCopies G sites m tag true true ∩ P) = Z1)
    (htruePair : Z0 = Z1.map lpReplicaCurrentReflect.toEmbedding)
    (hdisc0 : ¬ StatMech.Sharpness.RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P)))
      (lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaCoupledReflectToggleTagRaw G sites m P tag) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
    (hdisc1 : ¬ StatMech.Sharpness.RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P)))
      (lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaCoupledReflectToggleTagRaw G sites m P tag) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P))
      ((A ∆ X0) ∆ X1.map lpReplicaCurrentReflect.toEmbedding)
      ((B ∆ X1) ∆ X0.map lpReplicaCurrentReflect.toEmbedding)
      (lpReplicaCoupledReflectToggleTagRaw G sites m P tag) := by
  unfold LPReplicaRowGate
  refine ⟨?_, ?_, hdisc0, ?_, ?_, hdisc1⟩
  · rw [lpReplicaCoupledReflectToggle_currentSources,
      hgate.1, hfalse0]
    simp only [Bool.not_false, hfalse1]
  · rw [lpReplicaCoupledReflectToggle_currentSources,
      hgate.2.1, htrue0]
    simp only [Bool.not_false, htrue1]
    rw [htruePair]
    simp
  · rw [lpReplicaCoupledReflectToggle_currentSources,
      hgate.2.2.2.1, hfalse1]
    simp only [Bool.not_true, hfalse0]
  · rw [lpReplicaCoupledReflectToggle_currentSources,
      hgate.2.2.2.2.1, htrue1]
    simp only [Bool.not_true, htrue0]
    rw [htruePair, lpReplicaCurrentReflect_map_involutive]
    simp




structure LPReplicaCoupledPairedCut
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) where
  selector : Finset (Copy (lpReplicaCurrentGraph G sites) m)
  half : Finset (LPReplicaCurrentVertex V)
  trueHalf : Finset (LPReplicaCurrentVertex V)
  falseSource0 : StatMech.Sharpness.RandomCurrent.sources
    (endsM (lpReplicaCurrentGraph G sites) m)
    (lpReplicaCurrentCopies G sites m tag false false ∩ selector) = half
  falseSource1 : StatMech.Sharpness.RandomCurrent.sources
    (endsM (lpReplicaCurrentGraph G sites) m)
    (lpReplicaCurrentCopies G sites m tag true false ∩ selector) = half
  trueSource0 : StatMech.Sharpness.RandomCurrent.sources
    (endsM (lpReplicaCurrentGraph G sites) m)
    (lpReplicaCurrentCopies G sites m tag false true ∩ selector) =
      trueHalf.map lpReplicaCurrentReflect.toEmbedding
  trueSource1 : StatMech.Sharpness.RandomCurrent.sources
    (endsM (lpReplicaCurrentGraph G sites) m)
    (lpReplicaCurrentCopies G sites m tag true true ∩ selector) = trueHalf
  row0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK
    (endsM (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m
          (Finset.univ \ selector))
        (profileFlux (lpReplicaCurrentGraph G sites) m selector)))
    (lpReplicaRowCopies G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m
          (Finset.univ \ selector))
        (profileFlux (lpReplicaCurrentGraph G sites) m selector))
      (lpReplicaCoupledReflectToggleTagRaw G sites m selector tag) false)
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  row1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK
    (endsM (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m
          (Finset.univ \ selector))
        (profileFlux (lpReplicaCurrentGraph G sites) m selector)))
    (lpReplicaRowCopies G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m
          (Finset.univ \ selector))
        (profileFlux (lpReplicaCurrentGraph G sites) m selector))
      (lpReplicaCoupledReflectToggleTagRaw G sites m selector tag) true)
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1




abbrev LPReplicaRightCoupledPairedCut
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :=
  LPReplicaCoupledPairedCut G sites m B (lpReplicaSwapRowsTag tag)



theorem LPReplicaRightCoupledPairedCut.falseSource0
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag) :
    StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentCopies G sites m tag false false ∩ cut.selector) =
        cut.half := by
  simpa only [lpReplicaCurrentCopies_swapRowsTag, Bool.not_true] using
    LPReplicaCoupledPairedCut.falseSource1 cut



theorem LPReplicaRightCoupledPairedCut.falseSource1
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag) :
    StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentCopies G sites m tag true false ∩ cut.selector) =
        cut.half := by
  simpa only [lpReplicaCurrentCopies_swapRowsTag, Bool.not_false] using
    LPReplicaCoupledPairedCut.falseSource0 cut



theorem LPReplicaRightCoupledPairedCut.trueSource0
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag) :
    StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentCopies G sites m tag false true ∩ cut.selector) =
        cut.trueHalf := by
  simpa only [lpReplicaCurrentCopies_swapRowsTag, Bool.not_true] using
    LPReplicaCoupledPairedCut.trueSource1 cut



theorem LPReplicaRightCoupledPairedCut.trueSource1
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag) :
    StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentCopies G sites m tag true true ∩ cut.selector) =
        cut.trueHalf.map lpReplicaCurrentReflect.toEmbedding := by
  simpa only [lpReplicaCurrentCopies_swapRowsTag, Bool.not_false] using
    LPReplicaCoupledPairedCut.trueSource0 cut


theorem lpReplicaCoupledReflectToggleTagRaw_swapRows
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaCoupledReflectToggleTagRaw G sites m P
        (lpReplicaSwapRowsTag tag) =
      lpReplicaSwapRowsTag
        (lpReplicaCoupledReflectToggleTagRaw G sites m P tag) := by
  funext d
  unfold lpReplicaCoupledReflectToggleTagRaw
    lpReplicaPartialReflectTagRaw lpReplicaToggleRows
    lpReplicaSwapRowsTag
  by_cases hc : (lpReplicaPartialReflectCopyEquivRaw
      G sites m P).symm d ∈ P <;> simp [hc]



theorem lpReplicaSwapRowsTag_coupledReflectToggleTagRaw_swapRows
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaSwapRowsTag
        (lpReplicaCoupledReflectToggleTagRaw G sites m P
          (lpReplicaSwapRowsTag tag)) =
      lpReplicaCoupledReflectToggleTagRaw G sites m P tag := by
  rw [lpReplicaCoupledReflectToggleTagRaw_swapRows]
  exact lpReplicaSwapRowsTag_involutive G sites _ _




theorem LPReplicaCoupledPairedCut.half_eq_empty_of_row1False_empty
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (cut : LPReplicaCoupledPairedCut G sites m B tag)
    (hempty : lpReplicaCurrentCopies G sites m tag true false = ∅) :
    cut.half = ∅ := by
  rw [← cut.falseSource1, hempty]
  ext x
  simp [StatMech.Sharpness.RandomCurrent.mem_sources,
    StatMech.Sharpness.RandomCurrent.degK]




theorem LPReplicaCoupledPairedCut.balancedComponentBoundary_eq_empty
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (cut : LPReplicaCoupledPairedCut G sites m B tag)
    (hselector : cut.selector =
      lpReplicaBalancedComponentSelector G sites m tag) :
    lpReplicaBalancedComponentBoundary G sites m B ∅ tag = ∅ := by
  have hs := lpReplicaBalancedComponentSelector_rowCurrentSources
    G sites m B tag hgate
  have h0 := cut.falseSource0
  have h1 := cut.falseSource1
  rw [hselector] at h0 h1
  exact hs.1.symm.trans (h0.trans (h1.symm.trans hs.2.1))



theorem LPReplicaCoupledPairedCut.doubledHalf_eq_empty_of_balancedSelector
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (cut : LPReplicaCoupledPairedCut G sites m B tag)
    (hselector : cut.selector =
      lpReplicaBalancedComponentSelector G sites m tag) :
    cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding = ∅ := by
  have hs := lpReplicaBalancedComponentSelector_rowCurrentSources
    G sites m B tag hgate
  have h1 := cut.falseSource1
  rw [hselector] at h1
  have hhalf : cut.half = ∅ := h1.symm.trans hs.2.1
  rw [hhalf]
  simp


theorem lpReplicaRowGate_coupledPairedCut
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (cut : LPReplicaCoupledPairedCut G sites m B tag) :
    let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
    LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m
          (Finset.univ \ cut.selector))
        (profileFlux (lpReplicaCurrentGraph G sites) m cut.selector))
      (B ∆ D) D
      (lpReplicaCoupledReflectToggleTagRaw G sites m cut.selector tag) := by
  dsimp only
  have h := lpReplicaRowGate_coupledReflectToggle
    G sites m cut.selector B ∅ cut.half cut.half
      (cut.trueHalf.map lpReplicaCurrentReflect.toEmbedding) cut.trueHalf
      tag hgate cut.falseSource0 cut.falseSource1 cut.trueSource0
      cut.trueSource1 rfl cut.row0Disconn cut.row1Disconn
  have hleft : (B ∆ cut.half) ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding =
        B ∆ (cut.half ∆
          cut.half.map lpReplicaCurrentReflect.toEmbedding) := by
    ext x
    simp only [Finset.mem_symmDiff]
    tauto
  have hright : (∅ ∆ cut.half) ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding =
        cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding := by
    ext x
    simp [Finset.mem_symmDiff]
  rw [← hleft, ← hright]
  exact h




theorem lpReplicaRowGate_rightCoupledPairedCut
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m ∅ B tag)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag) :
    let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
    LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m
          (Finset.univ \ cut.selector))
        (profileFlux (lpReplicaCurrentGraph G sites) m cut.selector))
      D (B ∆ D)
      (lpReplicaCoupledReflectToggleTagRaw G sites m cut.selector tag) := by
  dsimp only
  let target := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) m
      (Finset.univ \ cut.selector))
    (profileFlux (lpReplicaCurrentGraph G sites) m cut.selector)
  let movedSwap := lpReplicaCoupledReflectToggleTagRaw
    G sites m cut.selector (lpReplicaSwapRowsTag tag)
  let D := cut.half ∆
    cut.half.map lpReplicaCurrentReflect.toEmbedding
  have hswapped : LPReplicaRowGate G sites m B ∅
      (lpReplicaSwapRowsTag tag) :=
    lpReplicaRowGate_swapRows G sites m ∅ B tag hgate
  have hleft : LPReplicaRowGate G sites target (B ∆ D) D movedSwap := by
    simpa only [target, movedSwap, D] using
      lpReplicaRowGate_coupledPairedCut G sites m B
        (lpReplicaSwapRowsTag tag) hswapped cut
  have hright : LPReplicaRowGate G sites target D (B ∆ D)
      (lpReplicaSwapRowsTag movedSwap) :=
    lpReplicaRowGate_swapRows G sites target (B ∆ D) D movedSwap hleft
  simpa only [target, movedSwap, D,
    lpReplicaSwapRowsTag_coupledReflectToggleTagRaw_swapRows] using hright



theorem lpReplica_half_symmDiff_reflect_fixed
    (X : Finset (LPReplicaCurrentVertex V)) :
    (X ∆ X.map lpReplicaCurrentReflect.toEmbedding).map
        lpReplicaCurrentReflect.toEmbedding =
      X ∆ X.map lpReplicaCurrentReflect.toEmbedding := by
  rw [lpReplica_map_symmDiff,
    lpReplicaCurrentReflect_map_involutive, symmDiff_comm]




noncomputable def lpReplicaPartialReflectCanonicalCopyEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    Copy (lpReplicaCurrentGraph G sites) m ≃
      Copy (lpReplicaCurrentGraph G sites)
        (lpReplicaPartialReflectProfile G sites m
          (profileFlux (lpReplicaCurrentGraph G sites) m P)) :=
  (lpReplicaProfileCopyEquivCommonSlot G sites q m hm L).trans
    (lpReplicaProfileCopyEquivCommonSlot G sites q
      (lpReplicaPartialReflectProfile G sites m
        (profileFlux (lpReplicaCurrentGraph G sites) m P))
      ((lpReplicaSymmetrizedProfile_partialReflectCopies
        G sites m P).trans hm)
      (lpReplicaProfileOrbitLabelPartialReflectCopies
        G sites q m hm P L)).symm



noncomputable def lpReplicaCanonicalPartialReflectToggleTag
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaPartialReflectProfile G sites m
        (profileFlux (lpReplicaCurrentGraph G sites) m P)) ->
      LPReplicaRowTag :=
  fun d => lpReplicaToggleRows G sites m P tag
    ((lpReplicaPartialReflectCanonicalCopyEquiv
      G sites q m hm L P).symm d)

set_option maxHeartbeats 800000 in



theorem lpReplicaOrbitFourColorSlotState_canonicalPartialReflect
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaOrbitFourColorSlotStateOfTag G sites q
        (lpReplicaPartialReflectProfile G sites m
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        ((lpReplicaSymmetrizedProfile_partialReflectCopies
          G sites m P).trans hm)
        (lpReplicaProfileOrbitLabelPartialReflectCopies
          G sites q m hm P L)
        (lpReplicaCanonicalPartialReflectToggleTag
          G sites q m hm L P tag) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P)
        (lpReplicaOrbitFourColorSlotStateOfTag
          G sites q m hm L tag) := by
  apply LPReplicaOrbitFourColorSlotState.ext
  · rw [lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_allocation]
    rfl
  · rw [lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_color]
    funext x
    let Es := lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
    let Et := lpReplicaProfileCopyEquivCommonSlot G sites q
      (lpReplicaPartialReflectProfile G sites m
        (profileFlux (lpReplicaCurrentGraph G sites) m P))
      ((lpReplicaSymmetrizedProfile_partialReflectCopies
        G sites m P).trans hm)
      (lpReplicaProfileOrbitLabelPartialReflectCopies
        G sites q m hm P L)
    change lpReplicaRowTagEquivFin4
        (lpReplicaCanonicalPartialReflectToggleTag
          G sites q m hm L P tag (Et.symm x.1)) =
      lpReplicaRowTagEquivFin4
        (lpReplicaToggleRows G sites m P tag (Es.symm x.1))
    apply congrArg lpReplicaRowTagEquivFin4
    apply congrArg (lpReplicaToggleRows G sites m P tag)
    let E := lpReplicaPartialReflectCanonicalCopyEquiv
      G sites q m hm L P
    apply E.injective
    rw [E.apply_symm_apply]
    unfold E lpReplicaPartialReflectCanonicalCopyEquiv
    change Et.symm x.1 = Et.symm (Es (Es.symm x.1))
    rw [Es.apply_symm_apply]

set_option maxHeartbeats 800000 in



theorem lpReplicaPartialReflectCanonicalCopyEquiv_edge
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    (lpReplicaPartialReflectCanonicalCopyEquiv
      G sites q m hm L P c).1 =
      if c ∈ P then lpReplicaCurrentEdgeReflect G sites c.1 else c.1 := by
  classical
  let Es := lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
  let Et := lpReplicaProfileCopyEquivCommonSlot G sites q
    (lpReplicaPartialReflectProfile G sites m
      (profileFlux (lpReplicaCurrentGraph G sites) m P))
    ((lpReplicaSymmetrizedProfile_partialReflectCopies
      G sites m P).trans hm)
    (lpReplicaProfileOrbitLabelPartialReflectCopies
      G sites q m hm P L)
  let E := lpReplicaPartialReflectCanonicalCopyEquiv
    G sites q m hm L P
  let sourceTag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag :=
    fun _ => (false, false)
  let sourceState := lpReplicaOrbitFourColorSlotStateOfTag
    G sites q m hm L sourceTag
  let targetState := lpReplicaOrbitFourColorSlotStateOfTag G sites q
    (lpReplicaPartialReflectProfile G sites m
      (profileFlux (lpReplicaCurrentGraph G sites) m P))
    ((lpReplicaSymmetrizedProfile_partialReflectCopies
      G sites m P).trans hm)
    (lpReplicaProfileOrbitLabelPartialReflectCopies
      G sites q m hm P L)
    (lpReplicaCanonicalPartialReflectToggleTag
      G sites q m hm L P sourceTag)
  have hstate : targetState =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P)
        sourceState :=
    lpReplicaOrbitFourColorSlotState_canonicalPartialReflect
      G sites q m hm L P sourceTag
  have hs := lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy
    G sites q m hm L sourceTag c
  have ht := lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy G sites q
    (lpReplicaPartialReflectProfile G sites m
      (profileFlux (lpReplicaCurrentGraph G sites) m P))
    ((lpReplicaSymmetrizedProfile_partialReflectCopies
      G sites m P).trans hm)
    (lpReplicaProfileOrbitLabelPartialReflectCopies
      G sites q m hm P L)
    (lpReplicaCanonicalPartialReflectToggleTag
      G sites q m hm L P sourceTag) (E c)
  have hslot : Et (E c) = Es c := by
    unfold E Es Et lpReplicaPartialReflectCanonicalCopyEquiv
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [hslot] at ht
  change lpReplicaOrbitFourColorSlotEdge G sites q targetState (Es c) =
    (E c).1 at ht
  change lpReplicaOrbitFourColorSlotEdge G sites q sourceState (Es c) =
    c.1 at hs
  rw [hstate] at ht
  by_cases hc : c ∈ P
  · have hx : Es c ∈
        lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P := by
      rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
      simpa only [Es, Equiv.symm_apply_apply] using hc
    rw [lpReplicaOrbitFourColorSlotEdge_crossToggle_of_mem
      G sites q _ sourceState (Es c) hx, hs] at ht
    simpa only [E, if_pos hc] using ht.symm
  · have hx : Es c ∉
        lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P := by
      intro hx
      apply hc
      rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff] at hx
      simpa only [Es, Equiv.symm_apply_apply] using hx
    rw [lpReplicaOrbitFourColorSlotEdge_crossToggle_of_not_mem
      G sites q _ sourceState (Es c) hx, hs] at ht
    simpa only [E, if_neg hc] using ht.symm


noncomputable def lpReplicaPartialReflectCanonicalRelabelEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    Copy (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P)) ≃
      Copy (lpReplicaCurrentGraph G sites)
        (lpReplicaPartialReflectProfile G sites m
          (profileFlux (lpReplicaCurrentGraph G sites) m P)) :=
  (lpReplicaPartialReflectCopyEquivRaw G sites m P).symm.trans
    (lpReplicaPartialReflectCanonicalCopyEquiv G sites q m hm L P)


theorem lpReplicaPartialReflectCanonicalRelabelEquiv_ends
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (d : Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P))) :
    endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaPartialReflectProfile G sites m
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCanonicalRelabelEquiv
          G sites q m hm L P d) =
      endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P)) d := by
  let c := (lpReplicaPartialReflectCopyEquivRaw G sites m P).symm d
  have hcanon := lpReplicaPartialReflectCanonicalCopyEquiv_edge
    G sites q m hm L P c
  have hraw := lpReplicaPartialReflectCopyEquivRaw_edge G sites m P c
  have hd : lpReplicaPartialReflectCopyEquivRaw G sites m P c = d := by
    exact (lpReplicaPartialReflectCopyEquivRaw G sites m P).apply_symm_apply d
  change (lpReplicaPartialReflectCanonicalCopyEquiv
    G sites q m hm L P c).1.1 = d.1.1
  rw [<- hd]
  exact congrArg Subtype.val (hcanon.trans hraw.symm)

set_option maxHeartbeats 800000 in




noncomputable def lpReplicaDecoratedOrbitAtomOfCoupledPairedCut
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaCoupledPairedCut G sites m B tag) :
    let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
    LPReplicaDecoratedOrbitAtom G sites (B ∆ D) D q := by
  dsimp only
  let rawTarget := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) m
      (Finset.univ \ cut.selector))
    (profileFlux (lpReplicaCurrentGraph G sites) m cut.selector)
  let target := lpReplicaPartialReflectProfile G sites m
    (profileFlux (lpReplicaCurrentGraph G sites) m cut.selector)
  let rawTag := lpReplicaCoupledReflectToggleTagRaw
    G sites m cut.selector tag
  let movedTag := lpReplicaCanonicalPartialReflectToggleTag
    G sites q m horbit L cut.selector tag
  let D := cut.half ∆
    cut.half.map lpReplicaCurrentReflect.toEmbedding
  have hrawGate : LPReplicaRowGate G sites rawTarget (B ∆ D) D rawTag := by
    simpa only [rawTarget, rawTag, D] using
      lpReplicaRowGate_coupledPairedCut G sites m B tag hgate cut
  let relabel := lpReplicaPartialReflectCanonicalRelabelEquiv
    G sites q m horbit L cut.selector
  have htransport := lpReplicaRowGate_transportTag G sites relabel
    (lpReplicaPartialReflectCanonicalRelabelEquiv_ends
      G sites q m horbit L cut.selector)
    (B ∆ D) D rawTag hrawGate
  have htag : lpReplicaTransportTag G sites relabel rawTag = movedTag := by
    funext d
    let Eraw := lpReplicaPartialReflectCopyEquivRaw
      G sites m cut.selector
    let Ecanon := lpReplicaPartialReflectCanonicalCopyEquiv
      G sites q m horbit L cut.selector
    change lpReplicaToggleRows G sites m cut.selector tag
        (Eraw.symm (Eraw (Ecanon.symm d))) =
      lpReplicaToggleRows G sites m cut.selector tag (Ecanon.symm d)
    rw [Eraw.symm_apply_apply]
  have htargetGate : LPReplicaRowGate G sites target (B ∆ D) D movedTag := by
    rw [<- htag]
    exact htransport
  have htargetOrbit : lpReplicaSymmetrizedProfile G sites target = q := by
    exact (lpReplicaSymmetrizedProfile_partialReflectCopies
      G sites m cut.selector).trans horbit
  let Lpartial := lpReplicaProfileOrbitLabelPartialReflectCopies
    G sites q m horbit cut.selector L
  let y := lpReplicaDecoratedOrbitAtomOfRowGate G sites target q movedTag
    (B ∆ D) D htargetOrbit htargetGate Lpartial
  have hD : D.map lpReplicaCurrentReflect.toEmbedding = D :=
    lpReplica_half_symmDiff_reflect_fixed cut.half
  exact cast (congrArg
    (fun Z => LPReplicaDecoratedOrbitAtom G sites (B ∆ D) Z q) hD) y

set_option maxHeartbeats 800000 in




noncomputable def lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCut
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hB : B.map lpReplicaCurrentReflect.toEmbedding = B)
    (hgate : LPReplicaRowGate G sites m ∅ B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag) :
    let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
    LPReplicaDecoratedOrbitAtom G sites D (B ∆ D) q := by
  dsimp only
  let rawTarget := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) m
      (Finset.univ \ cut.selector))
    (profileFlux (lpReplicaCurrentGraph G sites) m cut.selector)
  let target := lpReplicaPartialReflectProfile G sites m
    (profileFlux (lpReplicaCurrentGraph G sites) m cut.selector)
  let rawTag := lpReplicaCoupledReflectToggleTagRaw
    G sites m cut.selector tag
  let movedTag := lpReplicaCanonicalPartialReflectToggleTag
    G sites q m horbit L cut.selector tag
  let D := cut.half ∆
    cut.half.map lpReplicaCurrentReflect.toEmbedding
  have hrawGate : LPReplicaRowGate G sites rawTarget D (B ∆ D) rawTag := by
    simpa only [rawTarget, rawTag, D] using
      lpReplicaRowGate_rightCoupledPairedCut G sites m B tag hgate cut
  let relabel := lpReplicaPartialReflectCanonicalRelabelEquiv
    G sites q m horbit L cut.selector
  have htransport := lpReplicaRowGate_transportTag G sites relabel
    (lpReplicaPartialReflectCanonicalRelabelEquiv_ends
      G sites q m horbit L cut.selector)
    D (B ∆ D) rawTag hrawGate
  have htag : lpReplicaTransportTag G sites relabel rawTag = movedTag := by
    funext d
    let Eraw := lpReplicaPartialReflectCopyEquivRaw
      G sites m cut.selector
    let Ecanon := lpReplicaPartialReflectCanonicalCopyEquiv
      G sites q m horbit L cut.selector
    change lpReplicaToggleRows G sites m cut.selector tag
        (Eraw.symm (Eraw (Ecanon.symm d))) =
      lpReplicaToggleRows G sites m cut.selector tag (Ecanon.symm d)
    rw [Eraw.symm_apply_apply]
  have htargetGate : LPReplicaRowGate G sites target D (B ∆ D) movedTag := by
    rw [← htag]
    exact htransport
  have htargetOrbit : lpReplicaSymmetrizedProfile G sites target = q := by
    exact (lpReplicaSymmetrizedProfile_partialReflectCopies
      G sites m cut.selector).trans horbit
  let Lpartial := lpReplicaProfileOrbitLabelPartialReflectCopies
    G sites q m horbit cut.selector L
  let y := lpReplicaDecoratedOrbitAtomOfRowGate G sites target q movedTag
    D (B ∆ D) htargetOrbit htargetGate Lpartial
  have hD : D.map lpReplicaCurrentReflect.toEmbedding = D :=
    lpReplica_half_symmDiff_reflect_fixed cut.half
  have hBD : (B ∆ D).map lpReplicaCurrentReflect.toEmbedding = B ∆ D := by
    rw [lpReplica_map_symmDiff, hB, hD]
  exact cast (congrArg
    (fun Z => LPReplicaDecoratedOrbitAtom G sites D Z q) hBD) y

end

end StatMech.Ising
