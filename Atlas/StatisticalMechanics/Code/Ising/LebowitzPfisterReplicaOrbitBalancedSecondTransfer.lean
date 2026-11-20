/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitPartialReflectDecorated









open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy
open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaBalancedSecondTransferDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



theorem lpReplica_source_symmDiff_partialReflectSource
    (A C : Finset (LPReplicaCurrentVertex V)) :
    A ∆ lpReplicaPartialReflectSource A C =
      (A ∩ C) ∆
        (A ∩ C).map lpReplicaCurrentReflect.toEmbedding := by
  ext x
  simp only [lpReplicaPartialReflectSource, Finset.mem_symmDiff,
    Finset.mem_sdiff, Finset.mem_inter, Finset.mem_map]
  have hmap :
      (∃ a, (a ∈ A ∧ a ∈ C) ∧
          (lpReplicaCurrentReflect.toEmbedding :
            LPReplicaCurrentVertex V ↪ LPReplicaCurrentVertex V) a = x) ↔
        lpReplicaCurrentReflect x ∈ A ∧
          lpReplicaCurrentReflect x ∈ C := by
    constructor
    · rintro ⟨a, ha, hax⟩
      change lpReplicaCurrentReflect a = x at hax
      subst x
      rw [lpReplicaCurrentReflect_involutive (V := V) a]
      exact ha
    · intro hx
      refine ⟨lpReplicaCurrentReflect x, hx, ?_⟩
      exact lpReplicaCurrentReflect_involutive x
  rw [hmap]
  tauto



theorem lpReplicaOffdiagRowComponent_missingSource_eq_half_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hsrc : StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m) K =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
    (hdisc : ¬ StatMech.Sharpness.RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m) K
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    let C := StatMech.Sharpness.RandomCurrent.compOf
      (endsM (lpReplicaCurrentGraph G sites) m) K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let X :=
      (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) ∩ C
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    ((Si ∆ Sj ∆ T) ∆ Si =
        X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∨
      ((Si ∆ Sj ∆ T) ∆ Sj =
        X ∆ X.map lpReplicaCurrentReflect.toEmbedding) := by
  dsimp only
  let C := StatMech.Sharpness.RandomCurrent.compOf
    (endsM (lpReplicaCurrentGraph G sites) m) K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  have halloc := lpReplicaOffdiagRowComponent_partialReflectAllocation
    G sites hsite hij m K hsrc hdisc
  have hchange := lpReplica_source_symmDiff_partialReflectSource
    B C
  dsimp only [B, Si, Sj, T, C] at halloc hchange ⊢
  rcases halloc with halloc | halloc
  · left
    calc
      _ = (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) ∆
          lpReplicaPartialReflectSource
            (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
              lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1)
            (StatMech.Sharpness.RandomCurrent.compOf
              (endsM (lpReplicaCurrentGraph G sites) m) K
              lpReplicaCurrentGhost0) :=
        congrArg (fun Z =>
          (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
              lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) ∆ Z) halloc.1.symm
      _ = _ := hchange
  · right
    calc
      _ = (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) ∆
          lpReplicaPartialReflectSource
            (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
              lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1)
            (StatMech.Sharpness.RandomCurrent.compOf
              (endsM (lpReplicaCurrentGraph G sites) m) K
              lpReplicaCurrentGhost0) :=
        congrArg (fun Z =>
          (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
              lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) ∆ Z) halloc.1.symm
      _ = _ := hchange

set_option maxHeartbeats 800000 in



theorem exists_lpReplicaOffdiag_missingSource_half
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hsrc : StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m) K =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
    (hdisc : ¬ StatMech.Sharpness.RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m) K
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    (∃ X, Sj ∆ T = X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∨
      (∃ X, Si ∆ T = X ∆ X.map lpReplicaCurrentReflect.toEmbedding) := by
  dsimp only
  have h := lpReplicaOffdiagRowComponent_missingSource_eq_half_reflect
    G sites hsite hij m K hsrc hdisc
  rcases h with h | h
  · left
    refine ⟨((lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) ∩
      StatMech.Sharpness.RandomCurrent.compOf
        (endsM (lpReplicaCurrentGraph G sites) m) K
        lpReplicaCurrentGhost0), ?_⟩
    rw [← h]
    ext x
    simp only [Finset.mem_symmDiff]
    tauto
  · right
    refine ⟨((lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) ∩
      StatMech.Sharpness.RandomCurrent.compOf
        (endsM (lpReplicaCurrentGraph G sites) m) K
        lpReplicaCurrentGhost0), ?_⟩
    rw [← h]
    ext x
    simp only [Finset.mem_symmDiff]
    tauto




theorem lpReplicaPartialReflectTagRaw_toggleRows
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaPartialReflectTagRaw G sites m P
        (lpReplicaToggleRows G sites m P tag) =
      lpReplicaToggleRows G sites
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCopiesRaw G sites m P P)
        (lpReplicaPartialReflectTagRaw G sites m P tag) := by
  funext c
  simp [lpReplicaPartialReflectTagRaw, lpReplicaToggleRows,
    lpReplicaPartialReflectCopiesRaw]




theorem lpReplicaRowComponent_currentTrue_sources_empty
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (row : Bool) (root : LPReplicaCurrentVertex V) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    let K := lpReplicaRowCopies G sites m tag row
    let P := edgeComponent e K root
    StatMech.Sharpness.RandomCurrent.sources e
      (P.filter fun c => (tag c).2 = true) = ∅ := by
  classical
  dsimp only
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K := lpReplicaRowCopies G sites m tag row
  let T := lpReplicaCurrentCopies G sites m tag row true
  have hTsub : T ⊆ K :=
    lpReplicaCurrentCopies_subset_rowCopies G sites m tag row true
  have hinter : (edgeComponent e K root).filter
      (fun c => (tag c).2 = true) = T ∩ edgeComponent e K root := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · intro h
      refine ⟨?_, h.1⟩
      have hrow : (tag c).1 = row := by
        have hcK : c ∈ K := by
          have hcP := h.1
          rw [edgeComponent, Finset.mem_filter] at hcP
          exact hcP.1
        simp only [K, lpReplicaRowCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] at hcK
        exact hcK
      change c ∈ T
      simp only [T, lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact Prod.ext hrow h.2
    · intro h
      refine ⟨h.2, ?_⟩
      have hc := h.1
      simp only [T, lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and] at hc
      exact congrArg Prod.snd hc
  rw [hinter, sources_inter_edgeComponent hTsub]
  cases row
  · rw [hgate.2.1]
    simp
  · rw [hgate.2.2.2.2.1]
    simp




noncomputable def lpReplicaBalancedComponentSelector
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    Finset (Copy (lpReplicaCurrentGraph G sites) m) :=
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K0 := lpReplicaRowCopies G sites m tag false
  let K1 := lpReplicaRowCopies G sites m tag true
  edgeComponent e K0
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∪
    edgeComponent e K1
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)

theorem lpReplicaBalancedComponentSelector_filter
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (current : Bool) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    let K0 := lpReplicaRowCopies G sites m tag false
    let K1 := lpReplicaRowCopies G sites m tag true
    let C0 := edgeComponent e K0
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
    let C1 := edgeComponent e K1
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    (lpReplicaBalancedComponentSelector G sites m tag).filter
        (fun c => (tag c).2 = current) =
      (lpReplicaCurrentCopies G sites m tag false current ∩ C0) ∪
        (lpReplicaCurrentCopies G sites m tag true current ∩ C1) := by
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
  change (C0 ∪ C1).filter (fun c => (tag c).2 = current) = _
  ext c
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro ⟨hc0 | hc1, hcurrent⟩
    · left
      refine ⟨?_, hc0⟩
      simp only [lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and]
      have hrow : (tag c).1 = false := by
        have hcK := hC0 hc0
        simpa only [K0, lpReplicaRowCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using hcK
      exact Prod.ext hrow hcurrent
    · right
      refine ⟨?_, hc1⟩
      simp only [lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and]
      have hrow : (tag c).1 = true := by
        have hcK := hC1 hc1
        simpa only [K1, lpReplicaRowCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using hcK
      exact Prod.ext hrow hcurrent
  · rintro (⟨hc, hc0⟩ | ⟨hc, hc1⟩)
    · refine ⟨Or.inl hc0, ?_⟩
      have htag := hc
      simp only [lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and] at htag
      exact congrArg Prod.snd htag
    · refine ⟨Or.inr hc1, ?_⟩
      have htag := hc
      simp only [lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and] at htag
      exact congrArg Prod.snd htag



theorem lpReplicaBalancedComponentSelector_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m B ∅ tag) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    let K0 := lpReplicaRowCopies G sites m tag false
    let C0 := StatMech.Sharpness.RandomCurrent.compOf e K0
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
    StatMech.Sharpness.RandomCurrent.sources e
          ((lpReplicaBalancedComponentSelector G sites m tag).filter
            fun c => (tag c).2 = false) = B ∩ C0 ∧
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
    simp [K0]
  · rw [lpReplicaBalancedComponentSelector_filter G sites m tag true,
      sources_union_of_disjoint (hinter true),
      sources_inter_edgeComponent (hcurrent0 true),
      sources_inter_edgeComponent (hcurrent1 true),
      hgate.2.1, hgate.2.2.2.2.1]
    simp



theorem lpReplicaBalancedComponentSelector_disconnects
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m B ∅ tag) :
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



structure LPReplicaBalancedSelector
    (G : SimpleGraph V) (sites : I -> V)
    (B D : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  profile : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat
  orbit : lpReplicaSymmetrizedProfile G sites profile = q
  tag : Copy (lpReplicaCurrentGraph G sites) profile -> LPReplicaRowTag
  gate : LPReplicaRowGate G sites profile B ∅ tag
  orbitLabel : LPReplicaProfileOrbitLabel G sites q profile
  selector : Finset (Copy (lpReplicaCurrentGraph G sites) profile)
  falseSource : StatMech.Sharpness.RandomCurrent.sources
    (endsM (lpReplicaCurrentGraph G sites) profile)
    (selector.filter fun c => (tag c).2 = false) = D
  trueSource : StatMech.Sharpness.RandomCurrent.sources
    (endsM (lpReplicaCurrentGraph G sites) profile)
    (selector.filter fun c => (tag c).2 = true) = ∅
  row0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK
    (endsM (lpReplicaCurrentGraph G sites) profile)
    (lpReplicaRowCopies G sites profile
      (lpReplicaToggleRows G sites profile selector tag) false)
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  row1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK
    (endsM (lpReplicaCurrentGraph G sites) profile)
    (lpReplicaRowCopies G sites profile
      (lpReplicaToggleRows G sites profile selector tag) true)
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1




noncomputable def lpReplicaBalancedSelectorOfComponentExchange
    (G : SimpleGraph V) (sites : I -> V)
    (B : Finset (LPReplicaCurrentVertex V))
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (orbitLabel : LPReplicaProfileOrbitLabel G sites q m) :
    LPReplicaBalancedSelector G sites B
      (B ∩ StatMech.Sharpness.RandomCurrent.compOf
        (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m tag false)
        (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)) q := by
  let selector := lpReplicaBalancedComponentSelector G sites m tag
  have hsources := lpReplicaBalancedComponentSelector_sources
    G sites m B tag hgate
  have hdisconn := lpReplicaBalancedComponentSelector_disconnects
    G sites m B tag hgate
  exact
    { profile := m
      orbit := horbit
      tag := tag
      gate := hgate
      orbitLabel := orbitLabel
      selector := selector
      falseSource := hsources.1
      trueSource := hsources.2
      row0Disconn := hdisconn.1
      row1Disconn := hdisconn.2 }




noncomputable def lpReplicaDecoratedOrbitAtomOfBalancedSelector
    (G : SimpleGraph V) (sites : I -> V)
    (Si Sj T : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q) :
    LPReplicaDecoratedOrbitAtom G sites Si
      ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q := by
  let movedTag := lpReplicaToggleRows G sites s.profile s.selector s.tag
  have hgate : LPReplicaRowGate G sites s.profile Si (Sj ∆ T) movedTag :=
    lpReplicaRowGate_toggle_offdiag G sites s.profile Si Sj T
      s.tag s.selector s.gate s.falseSource s.trueSource
      s.row0Disconn s.row1Disconn
  exact lpReplicaDecoratedOrbitAtomOfRowGate G sites s.profile q movedTag
    Si (Sj ∆ T) s.orbit hgate s.orbitLabel


theorem lpReplica_map_symmDiff
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (f : X ↪ Y) (A B : Finset X) :
    (A ∆ B).map f = A.map f ∆ B.map f := by
  change ((A \ B) ∪ (B \ A)).map f =
    (A.map f \ B.map f) ∪ (B.map f \ A.map f)
  rw [Finset.map_union, Finset.map_sdiff, Finset.map_sdiff]

theorem lpReplicaCurrentReflect_seam_symmDiff_ghost
    (G : SimpleGraph V) (sites : I -> V) (i : I) :
    (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1).map
        lpReplicaCurrentReflect.toEmbedding =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 := by
  rw [lpReplica_map_symmDiff,
    lpReplicaCurrentReflect_seamSource G sites i,
    lpReplicaCurrentReflect_ghostSource G sites]



noncomputable def lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaBalancedSelector G sites
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q) :
    LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q := by
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  have hfixed : (Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding =
      Sj ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites j
  exact cast (congrArg
    (fun D => LPReplicaDecoratedOrbitAtom G sites Si D q) hfixed)
    (lpReplicaDecoratedOrbitAtomOfBalancedSelector
      G sites Si Sj T q s)

end

end StatMech.Ising
