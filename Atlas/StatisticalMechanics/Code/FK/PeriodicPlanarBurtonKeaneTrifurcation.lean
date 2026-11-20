/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FK.PeriodicPlanarBurtonKeaneMerge
import Code.FrontierA.FiniteCutHubCount

open Filter MeasureTheory Set SimpleGraph Topology Finset
open scoped ENNReal BigOperators

namespace StatMech.FK.PeriodicPlanar

open Lattice StatMech.FrontierA

variable {V : Type*} [Countable V] [DecidableEq V]


def removeVertex (x : V) (omega : ConfigSpace (Sym2 V)) :
    ConfigSpace (Sym2 V) :=
  fun e => if x ∈ e then false else omega e

theorem measurable_removeVertex (x : V) :
    Measurable (removeVertex x :
      ConfigSpace (Sym2 V) -> ConfigSpace (Sym2 V)) := by
  apply measurable_pi_lambda
  intro e
  by_cases hx : x ∈ e
  · simpa [removeVertex, hx] using
      (measurable_const : Measurable (fun _ : ConfigSpace (Sym2 V) => false))
  · simpa [removeVertex, hx] using ConfigSpace.measurable_eval e

theorem PeriodicGraph.removeVertex_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (x : V) :
    removeVertex (P.shift z x) (P.configTranslate z omega) =
      P.configTranslate z (removeVertex x omega) := by
  funext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      simp only [removeVertex, PeriodicGraph.configTranslate, Sym2.map_mk]
      have hmem : P.shift z x ∈ s(a, b) ↔
          x ∈ s(P.shift (-z) a, P.shift (-z) b) := by
        simp only [Sym2.mem_iff]
        constructor
        · rintro (h | h)
          · left
            simpa only [h] using (P.shift_neg_shift z x).symm
          · right
            simpa only [h] using (P.shift_neg_shift z x).symm
        · rintro (h | h)
          · left
            calc
              P.shift z x = P.shift z (P.shift (-z) a) := congrArg (P.shift z) h
              _ = a := P.shift_shift_neg z a
          · right
            calc
              P.shift z x = P.shift z (P.shift (-z) b) := congrArg (P.shift z) h
              _ = b := P.shift_shift_neg z b
      by_cases hx : P.shift z x ∈ s(a, b)
      · rw [if_pos hx, if_pos (hmem.mp hx)]
      · rw [if_neg hx, if_neg (fun h => hx (hmem.mpr h))]



def PeriodicGraph.IsTrifurcation (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (x : V) : Prop :=
  ∃ a1 a2 a3 : V,
    (P.openSubgraph omega).Adj x a1 ∧
    (P.openSubgraph omega).Adj x a2 ∧
    (P.openSubgraph omega).Adj x a3 ∧
    (P.cluster (removeVertex x omega) a1).Infinite ∧
    (P.cluster (removeVertex x omega) a2).Infinite ∧
    (P.cluster (removeVertex x omega) a3).Infinite ∧
    ¬ (P.openSubgraph (removeVertex x omega)).Reachable a1 a2 ∧
    ¬ (P.openSubgraph (removeVertex x omega)).Reachable a1 a3 ∧
    ¬ (P.openSubgraph (removeVertex x omega)).Reachable a2 a3

theorem PeriodicGraph.measurableSet_openAdj
    (P : PeriodicGraph V) (x y : V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      (P.openSubgraph omega).Adj x y} := by
  by_cases hxy : P.graph.Adj x y
  · have heq : {omega : ConfigSpace (Sym2 V) |
        (P.openSubgraph omega).Adj x y} =
      {omega | omega s(x, y) = true} := by
      ext omega
      simp [P.openSubgraph_adj, hxy]
    rw [heq]
    exact measurableSet_eq_fun (ConfigSpace.measurable_eval s(x, y)) measurable_const
  · have heq : {omega : ConfigSpace (Sym2 V) |
        (P.openSubgraph omega).Adj x y} = ∅ := by
      ext omega
      simp [P.openSubgraph_adj, hxy]
    rw [heq]
    exact MeasurableSet.empty

theorem PeriodicGraph.measurableSet_isTrifurcation
    (P : PeriodicGraph V) (x : V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      P.IsTrifurcation omega x} := by
  have heq : {omega : ConfigSpace (Sym2 V) |
        P.IsTrifurcation omega x} =
      ⋃ a1, ⋃ a2, ⋃ a3,
        {omega | (P.openSubgraph omega).Adj x a1} ∩
        {omega | (P.openSubgraph omega).Adj x a2} ∩
        {omega | (P.openSubgraph omega).Adj x a3} ∩
        (removeVertex x ⁻¹'
          {eta | (P.cluster eta a1).Infinite}) ∩
        (removeVertex x ⁻¹'
          {eta | (P.cluster eta a2).Infinite}) ∩
        (removeVertex x ⁻¹'
          {eta | (P.cluster eta a3).Infinite}) ∩
        (removeVertex x ⁻¹' (P.twoPointEvent a1 a2))ᶜ ∩
        (removeVertex x ⁻¹' (P.twoPointEvent a1 a3))ᶜ ∩
        (removeVertex x ⁻¹' (P.twoPointEvent a2 a3))ᶜ := by
    ext omega
    simp [PeriodicGraph.IsTrifurcation, PeriodicGraph.twoPointEvent, and_assoc]
  rw [heq]
  refine MeasurableSet.iUnion fun a1 => MeasurableSet.iUnion fun a2 =>
    MeasurableSet.iUnion fun a3 => ?_
  exact ((((((((P.measurableSet_openAdj x a1).inter
    (P.measurableSet_openAdj x a2)).inter
    (P.measurableSet_openAdj x a3)).inter
    ((P.measurableSet_cluster_infinite a1).preimage (measurable_removeVertex x))).inter
    ((P.measurableSet_cluster_infinite a2).preimage (measurable_removeVertex x))).inter
    ((P.measurableSet_cluster_infinite a3).preimage (measurable_removeVertex x))).inter
    ((P.measurableSet_twoPointEvent a1 a2).preimage
      (measurable_removeVertex x)).compl).inter
    ((P.measurableSet_twoPointEvent a1 a3).preimage
      (measurable_removeVertex x)).compl).inter
    ((P.measurableSet_twoPointEvent a2 a3).preimage
      (measurable_removeVertex x)).compl

theorem PeriodicGraph.isTrifurcation_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (x : V) :
    P.IsTrifurcation (P.configTranslate z omega) (P.shift z x) ↔
      P.IsTrifurcation omega x := by
  rw [PeriodicGraph.IsTrifurcation, PeriodicGraph.IsTrifurcation]
  constructor
  · rintro ⟨a1, a2, a3, h1, h2, h3, hi1, hi2, hi3, hd12, hd13, hd23⟩
    let b1 := P.shift (-z) a1
    let b2 := P.shift (-z) a2
    let b3 := P.shift (-z) a3
    refine ⟨b1, b2, b3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hm := (P.openSubgraphTranslateHom (-z)
        (P.configTranslate z omega)).map_rel h1
      simpa [b1] using hm
    · have hm := (P.openSubgraphTranslateHom (-z)
        (P.configTranslate z omega)).map_rel h2
      simpa [b2] using hm
    · have hm := (P.openSubgraphTranslateHom (-z)
        (P.configTranslate z omega)).map_rel h3
      simpa [b3] using hm
    · have hc := P.cluster_infinite_configTranslate z
        (removeVertex x omega) b1
      apply hc.mp
      rw [← P.removeVertex_configTranslate z omega x]
      simpa [b1] using hi1
    · have hc := P.cluster_infinite_configTranslate z
        (removeVertex x omega) b2
      apply hc.mp
      rw [← P.removeVertex_configTranslate z omega x]
      simpa [b2] using hi2
    · have hc := P.cluster_infinite_configTranslate z
        (removeVertex x omega) b3
      apply hc.mp
      rw [← P.removeVertex_configTranslate z omega x]
      simpa [b3] using hi3
    · intro hb
      apply hd12
      rw [P.removeVertex_configTranslate]
      simpa [b1, b2] using
        (P.reachable_configTranslate z (removeVertex x omega) b1 b2).mpr hb
    · intro hb
      apply hd13
      rw [P.removeVertex_configTranslate]
      simpa [b1, b3] using
        (P.reachable_configTranslate z (removeVertex x omega) b1 b3).mpr hb
    · intro hb
      apply hd23
      rw [P.removeVertex_configTranslate]
      simpa [b2, b3] using
        (P.reachable_configTranslate z (removeVertex x omega) b2 b3).mpr hb
  · rintro ⟨a1, a2, a3, h1, h2, h3, hi1, hi2, hi3, hd12, hd13, hd23⟩
    refine ⟨P.shift z a1, P.shift z a2, P.shift z a3,
      (P.openSubgraphTranslateHom z omega).map_rel h1,
      (P.openSubgraphTranslateHom z omega).map_rel h2,
      (P.openSubgraphTranslateHom z omega).map_rel h3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [P.removeVertex_configTranslate]
      exact (P.cluster_infinite_configTranslate z
        (removeVertex x omega) a1).mpr hi1
    · rw [P.removeVertex_configTranslate]
      exact (P.cluster_infinite_configTranslate z
        (removeVertex x omega) a2).mpr hi2
    · rw [P.removeVertex_configTranslate]
      exact (P.cluster_infinite_configTranslate z
        (removeVertex x omega) a3).mpr hi3
    · rw [P.removeVertex_configTranslate]
      intro h
      exact hd12 ((P.reachable_configTranslate z
        (removeVertex x omega) a1 a2).mp h)
    · rw [P.removeVertex_configTranslate]
      intro h
      exact hd13 ((P.reachable_configTranslate z
        (removeVertex x omega) a1 a3).mp h)
    · rw [P.removeVertex_configTranslate]
      intro h
      exact hd23 ((P.reachable_configTranslate z
        (removeVertex x omega) a2 a3).mp h)

theorem PeriodicGraph.trifurcation_measure_eq_orbit
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (z : Site 2) (u : V) :
    mu {omega | P.IsTrifurcation omega (P.shift z u)} =
      mu {omega | P.IsTrifurcation omega u} := by
  have hpre : P.configTranslate z ⁻¹'
      {omega | P.IsTrifurcation omega (P.shift z u)} =
      {omega | P.IsTrifurcation omega u} := by
    ext omega
    exact P.isTrifurcation_configTranslate z omega u
  calc
    mu {omega | P.IsTrifurcation omega (P.shift z u)} =
        mu (P.configTranslate z ⁻¹'
          {omega | P.IsTrifurcation omega (P.shift z u)}) :=
      ((hTI z).measure_preimage
        (P.measurableSet_isTrifurcation (P.shift z u)).nullMeasurableSet).symm
    _ = mu {omega | P.IsTrifurcation omega u} := by rw [hpre]


noncomputable def PeriodicGraph.neighborOrbitRadius (P : PeriodicGraph V) : Nat :=
  P.nextBufferedRadius 0

theorem PeriodicGraph.fundamentalDomain_mem_orbitBox_zero
    (P : PeriodicGraph V) {u : V} (hu : u ∈ P.fundamentalDomain) :
    u ∈ P.orbitBox 0 := by
  rw [P.mem_orbitBox_iff]
  exact ⟨0, by simp, u, hu, by rw [P.shift_zero]; rfl⟩

theorem PeriodicGraph.neighbor_mem_orbitBox_add
    (P : PeriodicGraph V) {n : Nat} {x y : V}
    (hx : x ∈ P.orbitBox n) (hxy : P.graph.Adj x y) :
    y ∈ P.orbitBox (n + P.neighborOrbitRadius) := by
  rw [P.mem_orbitBox_iff] at hx ⊢
  obtain ⟨z, hz, u, hu, rfl⟩ := hx
  let y0 := P.shift (-z) y
  have hadj0 : P.graph.Adj u y0 := by
    have hm := (P.shift_adj (-z) (P.shift z u) y).2 hxy
    simpa [y0] using hm
  have hy0 : y0 ∈ P.orbitBox P.neighborOrbitRadius := by
    exact P.neighbor_mem_nextBufferedRadius 0
      (P.fundamentalDomain_mem_orbitBox_zero hu) hadj0
  rw [P.mem_orbitBox_iff] at hy0
  obtain ⟨w, hw, v, hv, hwv⟩ := hy0
  refine ⟨w + z, ?_, v, hv, ?_⟩
  · rw [mem_box] at hz hw ⊢
    intro i
    calc
      ((w + z) i).natAbs <= (w i).natAbs + (z i).natAbs :=
        Int.natAbs_add_le _ _
      _ <= P.neighborOrbitRadius + n := Nat.add_le_add (hw i) (hz i)
      _ = n + P.neighborOrbitRadius := Nat.add_comm _ _
  · have hshift : P.shift z y0 = y := by simp [y0]
    rw [← hshift, ← hwv]
    exact P.shift_add w z v

noncomputable def PeriodicGraph.orbitShell
    (P : PeriodicGraph V) (n c : Nat) : Finset V :=
  P.orbitBox (n + c) \ P.orbitBox n

noncomputable def PeriodicGraph.orbitShellSource
    (P : PeriodicGraph V) (n c : Nat) : Finset (Site 2 × V) :=
  ((box_finite 2 (n + c)).toFinset \ (box_finite 2 n).toFinset) ×ˢ
    P.fundamentalDomain

theorem PeriodicGraph.orbitShell_subset_source_image
    (P : PeriodicGraph V) (n c : Nat) :
    P.orbitShell n c ⊆
      (P.orbitShellSource n c).image (fun zu => P.shift zu.1 zu.2) := by
  intro x hx
  rw [PeriodicGraph.orbitShell, Finset.mem_sdiff] at hx
  rw [P.mem_orbitBox_iff] at hx
  obtain ⟨z, hz, u, hu, rfl⟩ := hx.1
  apply Finset.mem_image.mpr
  refine ⟨(z, u), ?_, rfl⟩
  rw [PeriodicGraph.orbitShellSource, Finset.mem_product, Finset.mem_sdiff,
    Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
  refine ⟨⟨hz, ?_⟩, hu⟩
  intro hzsmall
  apply hx.2
  rw [P.mem_orbitBox_iff]
  exact ⟨z, hzsmall, u, hu, rfl⟩

theorem PeriodicGraph.orbitShell_card_le
    (P : PeriodicGraph V) (n c : Nat) :
    (P.orbitShell n c).card <=
      (((2 * (n + c) + 1) ^ 2 - (2 * n + 1) ^ 2) *
        P.fundamentalDomain.card) := by
  calc
    (P.orbitShell n c).card <=
        ((P.orbitShellSource n c).image (fun zu => P.shift zu.1 zu.2)).card :=
      Finset.card_le_card (P.orbitShell_subset_source_image n c)
    _ <= (P.orbitShellSource n c).card := Finset.card_image_le
    _ = (((2 * (n + c) + 1) ^ 2 - (2 * n + 1) ^ 2) *
        P.fundamentalDomain.card) := by
      rw [PeriodicGraph.orbitShellSource, Finset.card_product,
        Finset.card_sdiff_of_subset]
      · rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF,
          ← boxSV_boxF_eq_toFinset, boxSV_card_boxF]
      · intro z hz
        rw [Set.Finite.mem_toFinset] at hz ⊢
        exact box_mono 2 (Nat.le_add_right n c) hz

theorem PeriodicPlaneEmbedding.orbitBox_card_ge_quadratic
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P) (n : Nat) :
    (2 * n + 1) ^ 2 <= (P.orbitBox n).card := by
  let u := P.root
  let Z := (box_finite 2 n).toFinset
  have hinj : Function.Injective (fun z : Site 2 => P.shift z u) := by
    intro z w hzw
    have hv := congrArg (fun x => E.vertex x) hzw
    change E.vertex (P.shift z u) = E.vertex (P.shift w u) at hv
    rw [E.vertex_shift, E.vertex_shift] at hv
    apply E.period_injective
    exact add_left_cancel hv
  have hsub : Z.image (fun z => P.shift z u) ⊆ P.orbitBox n := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    rw [P.mem_orbitBox_iff]
    exact ⟨z, by simpa [Z] using hz, u, P.root_mem_fundamentalDomain, rfl⟩
  calc
    (2 * n + 1) ^ 2 = Z.card := by
      rw [show Z = (box_finite 2 n).toFinset from rfl,
        ← boxSV_boxF_eq_toFinset, boxSV_card_boxF]
    _ = (Z.image (fun z => P.shift z u)).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ <= (P.orbitBox n).card := Finset.card_le_card hsub

omit [Countable V] in
theorem removeVertex_le (x : V) (omega : ConfigSpace (Sym2 V)) :
    removeVertex x omega <= omega := by
  intro e
  by_cases hx : x ∈ e <;> simp [removeVertex, hx]

omit [Countable V] in
theorem PeriodicGraph.openSubgraph_removeVertex_le
    (P : PeriodicGraph V) (x : V) (omega : ConfigSpace (Sym2 V)) :
    P.openSubgraph (removeVertex x omega) <= P.openSubgraph omega :=
  P.openSubgraph_mono (removeVertex_le x omega)

theorem PeriodicGraph.trifurcation_orbitShell_witnesses
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V))
    (n : Nat) {x : V} (hx : x ∈ P.orbitBox n)
    (htrif : P.IsTrifurcation omega x) :
    ∃ t1 t2 t3 : V,
      t1 ∈ P.orbitShell n P.neighborOrbitRadius ∧
      t2 ∈ P.orbitShell n P.neighborOrbitRadius ∧
      t3 ∈ P.orbitShell n P.neighborOrbitRadius ∧
      x ≠ t1 ∧ x ≠ t2 ∧ x ≠ t3 ∧
      (P.openSubgraph omega).Reachable x t1 ∧
      (P.openSubgraph omega).Reachable x t2 ∧
      (P.openSubgraph omega).Reachable x t3 ∧
      ¬ ((P.openSubgraph omega).deleteIncidenceSet x).Reachable t1 t2 ∧
      ¬ ((P.openSubgraph omega).deleteIncidenceSet x).Reachable t1 t3 ∧
      ¬ ((P.openSubgraph omega).deleteIncidenceSet x).Reachable t2 t3 := by
  obtain ⟨a1, a2, a3, ha1, ha2, ha3, hi1, hi2, hi3,
    hd12, hd13, hd23⟩ := htrif
  let cut := P.openSubgraph (removeVertex x omega)
  let S : Set V := P.orbitBox (n + P.neighborOrbitRadius)
  have arm_mem (a : V) (ha : (P.openSubgraph omega).Adj x a) : a ∈ S := by
    exact P.neighbor_mem_orbitBox_add hx ha.1
  have arm_exit (a : V) (ha : a ∈ S)
      (hi : (P.cluster (removeVertex x omega) a).Infinite) :
      ∃ t : V, t ∈ P.orbitShell n P.neighborOrbitRadius ∧
        cut.Reachable a t := by
    have hout : ∃ z : V, z ∉ S ∧ cut.Reachable a z := by
      by_contra h
      push Not at h
      have hsub : P.cluster (removeVertex x omega) a ⊆ S := by
        intro z hz
        by_contra hzS
        exact h z hzS hz
      exact hi ((P.orbitBox (n + P.neighborOrbitRadius)).finite_toSet.subset hsub)
    obtain ⟨z, hzS, haz⟩ := hout
    obtain ⟨t, hat, w, htw, hwS⟩ :=
      reachable_induce_innerBoundary cut S ha hzS haz
    have hatFull : cut.Reachable a t.1 :=
      hat.map (SimpleGraph.Embedding.induce S).toHom
    refine ⟨t.1, ?_, hatFull⟩
    rw [PeriodicGraph.orbitShell, Finset.mem_sdiff]
    refine ⟨t.2, ?_⟩
    intro htn
    have hwmem := P.neighbor_mem_orbitBox_add htn htw.1
    exact hwS hwmem
  obtain ⟨t1, ht1shell, ht1⟩ := arm_exit a1 (arm_mem a1 ha1) hi1
  obtain ⟨t2, ht2shell, ht2⟩ := arm_exit a2 (arm_mem a2 ha2) hi2
  obtain ⟨t3, ht3shell, ht3⟩ := arm_exit a3 (arm_mem a3 ha3) hi3
  have hcutLe : cut <= P.openSubgraph omega :=
    P.openSubgraph_removeVertex_le x omega
  have hreach1 : (P.openSubgraph omega).Reachable x t1 :=
    ha1.reachable.trans (ht1.mono hcutLe)
  have hreach2 : (P.openSubgraph omega).Reachable x t2 :=
    ha2.reachable.trans (ht2.mono hcutLe)
  have hreach3 : (P.openSubgraph omega).Reachable x t3 :=
    ha3.reachable.trans (ht3.mono hcutLe)
  have hdeleteEq : (P.openSubgraph omega).deleteIncidenceSet x = cut := by
    ext a b
    simp only [SimpleGraph.deleteIncidenceSet_adj,
      PeriodicGraph.openSubgraph_adj, cut, removeVertex]
    by_cases hxa : x = a
    · subst a
      simp
    by_cases hxb : x = b
    · subst b
      simp
    have hxmem : x ∉ s(a, b) := by
      simpa only [Sym2.mem_iff, not_or] using ⟨hxa, hxb⟩
    have hax : a ≠ x := Ne.symm hxa
    have hbx : b ≠ x := Ne.symm hxb
    simp [hxa, hxb, hax, hbx, hxmem]
  have hne (t : V) (ht : t ∈ P.orbitShell n P.neighborOrbitRadius) : x ≠ t := by
    intro hxt
    subst t
    exact (Finset.mem_sdiff.mp ht).2 hx
  refine ⟨t1, t2, t3, ht1shell, ht2shell, ht3shell,
    hne t1 ht1shell, hne t2 ht2shell, hne t3 ht3shell,
    hreach1, hreach2, hreach3, ?_, ?_, ?_⟩
  · rw [hdeleteEq]
    intro h
    exact hd12 (ht1.trans (h.trans ht2.symm))
  · rw [hdeleteEq]
    intro h
    exact hd13 (ht1.trans (h.trans ht3.symm))
  · rw [hdeleteEq]
    intro h
    exact hd23 (ht2.trans (h.trans ht3.symm))

noncomputable def PeriodicGraph.orbitTrifurcationCoords
    (P : PeriodicGraph V) (u : V) (omega : ConfigSpace (Sym2 V))
    (n : Nat) : Finset (Site 2) :=
  by
    classical
    exact (box_finite 2 n).toFinset.filter
      (fun z => P.IsTrifurcation omega (P.shift z u))

noncomputable def PeriodicGraph.orbitTrifurcationHubs
    (P : PeriodicGraph V) (u : V) (omega : ConfigSpace (Sym2 V))
    (n : Nat) : Finset V :=
  (P.orbitTrifurcationCoords u omega n).image (fun z => P.shift z u)

theorem PeriodicPlaneEmbedding.orbitTrifurcationHubs_card
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (u : V) (omega : ConfigSpace (Sym2 V)) (n : Nat) :
    (P.orbitTrifurcationHubs u omega n).card =
      (P.orbitTrifurcationCoords u omega n).card := by
  rw [PeriodicGraph.orbitTrifurcationHubs,
    Finset.card_image_of_injective]
  intro z w h
  have hv := congrArg (fun x => E.vertex x) h
  change E.vertex (P.shift z u) = E.vertex (P.shift w u) at hv
  rw [E.vertex_shift, E.vertex_shift] at hv
  exact E.period_injective (add_left_cancel hv)

theorem PeriodicPlaneEmbedding.orbitTrifurcation_count_le_shell
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (u : V) (hu : u ∈ P.fundamentalDomain)
    (omega : ConfigSpace (Sym2 V)) (n : Nat) :
    (P.orbitTrifurcationCoords u omega n).card <=
      (P.orbitShell n P.neighborOrbitRadius).card := by
  classical
  rw [← E.orbitTrifurcationHubs_card u omega n]
  apply finite_cutHub_count_of_ambient (P.openSubgraph omega)
    (P.orbitTrifurcationHubs u omega n)
    (P.orbitShell n P.neighborOrbitRadius)
  intro x hx
  rw [PeriodicGraph.orbitTrifurcationHubs, Finset.mem_image] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  rw [PeriodicGraph.orbitTrifurcationCoords, Finset.mem_filter] at hz
  have hxbox : P.shift z u ∈ P.orbitBox n := by
    rw [P.mem_orbitBox_iff]
    exact ⟨z, by simpa using hz.1, u, hu, rfl⟩
  exact P.trifurcation_orbitShell_witnesses omega n hxbox hz.2

theorem PeriodicGraph.orbitTrifurcationCoords_cast_eq_sum_indicator
    (P : PeriodicGraph V) (u : V) (omega : ConfigSpace (Sym2 V))
    (n : Nat) :
    ((P.orbitTrifurcationCoords u omega n).card : ENNReal) =
      ∑ z ∈ (box_finite 2 n).toFinset,
        ({eta | P.IsTrifurcation eta (P.shift z u)}.indicator
          (fun _ => (1 : ENNReal))) omega := by
  classical
  unfold PeriodicGraph.orbitTrifurcationCoords
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : P.IsTrifurcation omega (P.shift z u) <;> simp [h]

theorem PeriodicGraph.expected_orbitTrifurcationCoords
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (u : V) (n : Nat) :
    ∫⁻ omega, ((P.orbitTrifurcationCoords u omega n).card : ENNReal) ∂mu =
      ((box_finite 2 n).toFinset.card) •
        mu {omega | P.IsTrifurcation omega u} := by
  classical
  calc
    ∫⁻ omega, ((P.orbitTrifurcationCoords u omega n).card : ENNReal) ∂mu =
        ∫⁻ omega, ∑ z ∈ (box_finite 2 n).toFinset,
          ({eta | P.IsTrifurcation eta (P.shift z u)}.indicator
            (fun _ => (1 : ENNReal))) omega ∂mu := by
      apply lintegral_congr
      intro omega
      exact P.orbitTrifurcationCoords_cast_eq_sum_indicator u omega n
    _ = ∑ z ∈ (box_finite 2 n).toFinset,
        ∫⁻ omega, ({eta | P.IsTrifurcation eta (P.shift z u)}.indicator
          (fun _ => (1 : ENNReal))) omega ∂mu := by
      rw [MeasureTheory.lintegral_finsetSum]
      intro z _
      exact Measurable.indicator measurable_const
        (P.measurableSet_isTrifurcation (P.shift z u))
    _ = ∑ z ∈ (box_finite 2 n).toFinset,
        mu {omega | P.IsTrifurcation omega (P.shift z u)} := by
      apply Finset.sum_congr rfl
      intro z _
      rw [MeasureTheory.lintegral_indicator
        (P.measurableSet_isTrifurcation (P.shift z u))]
      simp
    _ = ∑ _z ∈ (box_finite 2 n).toFinset,
        mu {omega | P.IsTrifurcation omega u} := by
      apply Finset.sum_congr rfl
      intro z _
      exact P.trifurcation_measure_eq_orbit mu hTI z u
    _ = ((box_finite 2 n).toFinset.card) •
        mu {omega | P.IsTrifurcation omega u} := by
      simp

theorem PeriodicGraph.orbitShell_polynomial_ratio_tendsto_zero
    (P : PeriodicGraph V) (c : Nat) :
    Tendsto (fun n =>
      ((((2 * (n + c) + 1) ^ 2 - (2 * n + 1) ^ 2) *
        P.fundamentalDomain.card : Nat) : Real) /
        (((2 * n + 1) ^ 2 : Nat) : Real)) atTop (nhds 0) := by
  let C : Real := 16 * ((c : Real) + 1) * P.fundamentalDomain.card
  have hupper : Tendsto (fun n : Nat => C / ((n : Real) + 1))
      atTop (nhds 0) := by
    have hden : Tendsto (fun n : Nat => (n : Real) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := C)).div_atTop hden
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hupper
  filter_upwards [eventually_ge_atTop c] with n hn
  have hsub : (2 * n + 1) ^ 2 <= (2 * (n + c) + 1) ^ 2 := by
    exact Nat.pow_le_pow_left (by omega) 2
  have hcastSub :
      ((((2 * (n + c) + 1) ^ 2 - (2 * n + 1) ^ 2 : Nat) : Real)) =
        ((2 * ((n : Real) + c) + 1) ^ 2 -
          (2 * (n : Real) + 1) ^ 2) := by
    rw [Nat.cast_sub hsub]
    push_cast
    ring
  have hnreal : (c : Real) <= n := by exact_mod_cast hn
  have hn0 : (0 : Real) <= n := by positivity
  have hc0 : (0 : Real) <= c := by positivity
  have hfd0 : (0 : Real) <= P.fundamentalDomain.card := by positivity
  have hcn : (c : Real) * n <= ((c : Real) + 1) * (n + 1) := by
    exact mul_le_mul (by linarith) (by linarith) hn0 (by linarith)
  have hcc : (c : Real) * c <= ((c : Real) + 1) * (n + 1) := by
    exact mul_le_mul (by linarith) (by linarith) hc0 (by linarith)
  have hdiff :
      (2 * ((n : Real) + c) + 1) ^ 2 - (2 * (n : Real) + 1) ^ 2 <=
        16 * ((c : Real) + 1) * (n + 1) := by
    nlinarith [hcn, hcc]
  have hnum :
      (((((2 * (n + c) + 1) ^ 2 - (2 * n + 1) ^ 2) *
        P.fundamentalDomain.card : Nat) : Real)) <=
        C * ((n : Real) + 1) := by
    rw [Nat.cast_mul, hcastSub]
    dsimp [C]
    calc
      ((2 * ((n : Real) + c) + 1) ^ 2 - (2 * (n : Real) + 1) ^ 2) *
          P.fundamentalDomain.card <=
          (16 * ((c : Real) + 1) * (n + 1)) *
            P.fundamentalDomain.card :=
        mul_le_mul_of_nonneg_right hdiff hfd0
      _ = 16 * ((c : Real) + 1) * P.fundamentalDomain.card * (n + 1) := by
        ring
  have hden : ((n : Real) + 1) ^ 2 <=
      (((2 * n + 1) ^ 2 : Nat) : Real) := by
    push_cast
    nlinarith
  have hn1 : (0 : Real) < n + 1 := by positivity
  have hD : (0 : Real) < (((2 * n + 1) ^ 2 : Nat) : Real) := by positivity
  rw [div_le_div_iff₀ hD hn1]
  have hC0 : 0 <= C := by dsimp [C]; positivity
  nlinarith



theorem PeriodicPlaneEmbedding.trifurcation_measure_eq_zero
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (u : V)
    (hu : u ∈ P.fundamentalDomain) :
    mu {omega | P.IsTrifurcation omega u} = 0 := by
  let pr : Real := mu.real {omega | P.IsTrifurcation omega u}
  have hratio := P.orbitShell_polynomial_ratio_tendsto_zero P.neighborOrbitRadius
  have hle : ∀ n : Nat, pr <=
      ((((2 * (n + P.neighborOrbitRadius) + 1) ^ 2 -
          (2 * n + 1) ^ 2) * P.fundamentalDomain.card : Nat) : Real) /
        (((2 * n + 1) ^ 2 : Nat) : Real) := by
    intro n
    have hexp := P.expected_orbitTrifurcationCoords mu hTI u n
    have hlin : ∫⁻ omega,
        ((P.orbitTrifurcationCoords u omega n).card : ENNReal) ∂mu <=
        ((P.orbitShell n P.neighborOrbitRadius).card : ENNReal) := by
      calc
        (∫⁻ omega, ((P.orbitTrifurcationCoords u omega n).card : ENNReal) ∂mu) <=
            ∫⁻ _omega : ConfigSpace (Sym2 V),
              ((P.orbitShell n P.neighborOrbitRadius).card : ENNReal) ∂mu := by
          apply lintegral_mono
          intro omega
          change ((P.orbitTrifurcationCoords u omega n).card : ENNReal) <=
            ((P.orbitShell n P.neighborOrbitRadius).card : ENNReal)
          exact_mod_cast E.orbitTrifurcation_count_le_shell u hu omega n
        _ = ((P.orbitShell n P.neighborOrbitRadius).card : ENNReal) := by simp
    rw [hexp] at hlin
    have hpoly := P.orbitShell_card_le n P.neighborOrbitRadius
    have hENN : (((box_finite 2 n).toFinset.card : Nat) : ENNReal) *
        mu {omega | P.IsTrifurcation omega u} <=
      (((((2 * (n + P.neighborOrbitRadius) + 1) ^ 2 -
        (2 * n + 1) ^ 2) * P.fundamentalDomain.card : Nat)) : ENNReal) := by
      calc
        (((box_finite 2 n).toFinset.card : Nat) : ENNReal) *
            mu {omega | P.IsTrifurcation omega u} =
            ((box_finite 2 n).toFinset.card) •
              mu {omega | P.IsTrifurcation omega u} := by simp [nsmul_eq_mul]
        _ <= ((P.orbitShell n P.neighborOrbitRadius).card : ENNReal) := hlin
        _ <= _ := by exact_mod_cast hpoly
    have hboxcard : (box_finite 2 n).toFinset.card = (2 * n + 1) ^ 2 := by
      rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]
    let B : Nat := ((2 * (n + P.neighborOrbitRadius) + 1) ^ 2 -
      (2 * n + 1) ^ 2) * P.fundamentalDomain.card
    have hENN' : ((((2 * n + 1) ^ 2 : Nat) : ENNReal)) *
        mu {omega | P.IsTrifurcation omega u} <= (B : ENNReal) := by
      simpa only [hboxcard, B] using hENN
    have hright_ne_top : (B : ENNReal) ≠ (⊤ : ENNReal) := by simp
    have hreal0 := ENNReal.toReal_mono hright_ne_top hENN'
    have hreal : ((((2 * n + 1) ^ 2 : Nat) : Real) * pr <= (B : Real)) := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hreal0
    have hden : (0 : Real) < (((2 * n + 1) ^ 2 : Nat) : Real) := by positivity
    change pr <= (B : Real) / (((2 * n + 1) ^ 2 : Nat) : Real)
    apply (le_div_iff₀ hden).2
    simpa [mul_comm] using hreal
  have hpr0 : pr <= 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hratio hle
  have hpreal : pr = 0 := le_antisymm hpr0 measureReal_nonneg
  exact (measureReal_eq_zero_iff (measure_ne_top mu _)).1 hpreal

end StatMech.FK.PeriodicPlanar
