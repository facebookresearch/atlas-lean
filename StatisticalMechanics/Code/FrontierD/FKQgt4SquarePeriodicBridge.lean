/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FK.PeriodicPlanarCoherentLimit
import Code.FK.FiniteVolumeShift

open Finset SimpleGraph MeasureTheory

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.FK StatMech.FK.PeriodicPlanar

noncomputable section

theorem fkSquarePeriodic_orbitBox_eq_box (n : Nat) :
    square.orbitBox n = (box_finite 2 n).toFinset := by
  ext x
  rw [PeriodicGraph.mem_orbitBox_iff]
  simp [square]

theorem fkSquarePeriodic_mem_orbitBox_iff (n : Nat) (x : Site 2) :
    x ∈ square.orbitBox n ↔ x ∈ box 2 n := by
  rw [PeriodicGraph.mem_orbitBox_iff]
  simp [square]



noncomputable def fkSquarePeriodicVertexEquiv (n : Nat) :
    square.OrbitVertex n ≃ FK.boxVerts 2 n where
  toFun x := ⟨x.1, by
    exact (fkSquarePeriodic_mem_orbitBox_iff n x.1).mp x.2⟩
  invFun x := ⟨x.1, by
    exact (fkSquarePeriodic_mem_orbitBox_iff n x.1).mpr x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

@[simp] theorem fkSquarePeriodicVertexEquiv_apply (n : Nat)
    (x : square.OrbitVertex n) :
    (fkSquarePeriodicVertexEquiv n x : Site 2) = (x : Site 2) := rfl



theorem fkSquarePeriodicVertexEquiv_adj (n : Nat)
    (x y : square.OrbitVertex n) :
    (square.orbitGraph n).Adj x y ↔
      (FK.boxGraph 2 n).Adj
        (fkSquarePeriodicVertexEquiv n x)
        (fkSquarePeriodicVertexEquiv n y) := by
  rfl


theorem fkSquarePeriodicVertexEquiv_boundary (n : Nat)
    (x : square.OrbitVertex n) :
    square.orbitBoundary n x ↔
      FK.boxBoundary 2 n (fkSquarePeriodicVertexEquiv n x) := by
  unfold PeriodicGraph.orbitBoundary FK.boxBoundary
  rw [mem_vertexBoundary]
  have hxbox : (x : Site 2) ∈ box 2 n := by
    exact (fkSquarePeriodic_mem_orbitBox_iff n x.1).mp x.2
  simp only [fkSquarePeriodicVertexEquiv_apply, hxbox, true_and]
  exact not_congr (fkSquarePeriodic_mem_orbitBox_iff (n - 1) x.1)



theorem fkSquarePeriodic_fkProb_reCfgIso (n : Nat) (p q : Real)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))) :
    FK.fkProb (square.orbitGraph n) p q
        (FK.reCfgIso (fkSquarePeriodicVertexEquiv n) omega) =
      FK.fkProb (FK.boxGraph 2 n) p q omega := by
  exact FK.fvs_fkProb_reCfgIso
    (square.orbitGraph n) (FK.boxGraph 2 n)
    (fkSquarePeriodicVertexEquiv n)
    (fkSquarePeriodicVertexEquiv_adj n) p q omega



theorem fkSquarePeriodic_wiredFkProb_reCfgIso (n : Nat) (p q : Real)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))) :
    FK.wiredFkProb (square.orbitGraph n) (square.orbitBoundary n) p q
        (FK.reCfgIso (fkSquarePeriodicVertexEquiv n) omega) =
      FK.wiredFkProb (FK.boxGraph 2 n) (FK.boxBoundary 2 n) p q omega := by
  exact FK.fvs_wiredFkProb_reCfgIso
    (square.orbitGraph n) (FK.boxGraph 2 n)
    (square.orbitBoundary n) (FK.boxBoundary 2 n)
    (fkSquarePeriodicVertexEquiv n)
    (fkSquarePeriodicVertexEquiv_adj n)
    (fkSquarePeriodicVertexEquiv_boundary n) p q omega


theorem fkSquarePeriodic_freeFinitePMF_reCfgIso (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))) :
    square.freeFinitePMF n hp hp1 hq
        (FK.reCfgIso (fkSquarePeriodicVertexEquiv n) omega) =
      FK.fkPMF (FK.boxGraph 2 n) hp hp1 hq omega := by
  rw [PeriodicGraph.freeFinitePMF, FK.fkPMF_apply, FK.fkPMF_apply,
    fkSquarePeriodic_fkProb_reCfgIso]


theorem fkSquarePeriodic_wiredFinitePMF_reCfgIso (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))) :
    square.wiredFinitePMF n hp hp1 hq
        (FK.reCfgIso (fkSquarePeriodicVertexEquiv n) omega) =
      FK.wiredFkPMF (FK.boxGraph 2 n) (FK.boxBoundary 2 n)
        hp hp1 hq omega := by
  rw [PeriodicGraph.wiredFinitePMF, FK.wiredFkPMF, PMF.ofFintype_apply,
    FK.wiredFkPMF, PMF.ofFintype_apply,
    fkSquarePeriodic_wiredFkProb_reCfgIso]



noncomputable def fkSquarePeriodicConfigEquiv (n : Nat) :
    ConfigSpace (Sym2 (FK.boxVerts 2 n)) ≃
      ConfigSpace (Sym2 (square.OrbitVertex n)) :=
  FK.reCfgIsoEquiv (fkSquarePeriodicVertexEquiv n)

set_option maxHeartbeats 800000 in




theorem fkSquarePeriodic_freeFinitePMF_eq_map (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    square.freeFinitePMF n hp hp1 hq =
      (FK.fkPMF (FK.boxGraph 2 n) hp hp1 hq).map
        (fkSquarePeriodicConfigEquiv n) := by
  apply PMF.ext
  intro eta
  let decEta : ∀ z, Decidable (eta = z) := fun z => Classical.propDecidable _
  rw [PMF.map_apply]
  symm
  calc
    (∑' omega, @ite ENNReal
        (eta = fkSquarePeriodicConfigEquiv n omega)
        (decEta (fkSquarePeriodicConfigEquiv n omega))
        (FK.fkPMF (FK.boxGraph 2 n) hp hp1 hq omega) 0) =
        ∑' z, @ite ENNReal (eta = z) (decEta z)
          (FK.fkPMF (FK.boxGraph 2 n) hp hp1 hq
            ((fkSquarePeriodicConfigEquiv n).symm z)) 0 := by
      rw [← (fkSquarePeriodicConfigEquiv n).tsum_eq]
      apply tsum_congr
      intro omega
      simp
    _ = FK.fkPMF (FK.boxGraph 2 n) hp hp1 hq
          ((fkSquarePeriodicConfigEquiv n).symm eta) := by
      classical
      rw [tsum_eq_single eta]
      · rw [if_pos rfl]
      · intro z hz
        rw [if_neg (Ne.symm hz)]
    _ = square.freeFinitePMF n hp hp1 hq eta := by
      have h := fkSquarePeriodic_freeFinitePMF_reCfgIso n hp hp1 hq
        ((fkSquarePeriodicConfigEquiv n).symm eta)
      have hE := (fkSquarePeriodicConfigEquiv n).apply_symm_apply eta
      change FK.reCfgIso (fkSquarePeriodicVertexEquiv n)
        ((fkSquarePeriodicConfigEquiv n).symm eta) = eta at hE
      rw [hE] at h
      exact h.symm

set_option maxHeartbeats 800000 in




theorem fkSquarePeriodic_wiredFinitePMF_eq_map (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    square.wiredFinitePMF n hp hp1 hq =
      (FK.wiredFkPMF (FK.boxGraph 2 n) (FK.boxBoundary 2 n)
        hp hp1 hq).map (fkSquarePeriodicConfigEquiv n) := by
  apply PMF.ext
  intro eta
  let decEta : ∀ z, Decidable (eta = z) := fun z => Classical.propDecidable _
  rw [PMF.map_apply]
  symm
  calc
    (∑' omega, @ite ENNReal
        (eta = fkSquarePeriodicConfigEquiv n omega)
        (decEta (fkSquarePeriodicConfigEquiv n omega))
        (FK.wiredFkPMF (FK.boxGraph 2 n) (FK.boxBoundary 2 n)
          hp hp1 hq omega) 0) =
        ∑' z, @ite ENNReal (eta = z) (decEta z)
          (FK.wiredFkPMF (FK.boxGraph 2 n) (FK.boxBoundary 2 n)
            hp hp1 hq ((fkSquarePeriodicConfigEquiv n).symm z)) 0 := by
      rw [← (fkSquarePeriodicConfigEquiv n).tsum_eq]
      apply tsum_congr
      intro omega
      simp
    _ = FK.wiredFkPMF (FK.boxGraph 2 n) (FK.boxBoundary 2 n)
          hp hp1 hq ((fkSquarePeriodicConfigEquiv n).symm eta) := by
      classical
      rw [tsum_eq_single eta]
      · rw [if_pos rfl]
      · intro z hz
        rw [if_neg (Ne.symm hz)]
    _ = square.wiredFinitePMF n hp hp1 hq eta := by
      have h := fkSquarePeriodic_wiredFinitePMF_reCfgIso n hp hp1 hq
        ((fkSquarePeriodicConfigEquiv n).symm eta)
      have hE := (fkSquarePeriodicConfigEquiv n).apply_symm_apply eta
      change FK.reCfgIso (fkSquarePeriodicVertexEquiv n)
        ((fkSquarePeriodicConfigEquiv n).symm eta) = eta at hE
      rw [hE] at h
      exact h.symm


theorem fkSquarePeriodic_edgeIncl_eq (n : Nat)
    (e : Sym2 (square.OrbitVertex n)) :
    square.edgeIncl n e =
      FK.edgeIncl 2 n (Sym2.map (fkSquarePeriodicVertexEquiv n) e) := by
  induction e using Sym2.inductionOn with
  | _ x y => rfl



theorem fkSquarePeriodic_extendEdge_reCfgIso (n : Nat)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))) :
    square.extendEdge n
        (FK.reCfgIso (fkSquarePeriodicVertexEquiv n) omega) =
      FK.extendEdge 2 n omega := by
  funext e
  unfold PeriodicGraph.extendEdge FK.extendEdge
  by_cases hp : e ∈ Set.range (square.edgeIncl n)
  · rw [dif_pos hp]
    have hc : e ∈ Set.range (FK.edgeIncl 2 n) := by
      obtain ⟨ep, rfl⟩ := hp
      exact ⟨Sym2.map (fkSquarePeriodicVertexEquiv n) ep,
        (fkSquarePeriodic_edgeIncl_eq n ep).symm⟩
    rw [dif_pos hc]
    unfold FK.reCfgIso
    congr 1
    apply FK.edgeIncl_injective
    calc
      FK.edgeIncl 2 n
          (Sym2.map (fkSquarePeriodicVertexEquiv n) hp.choose) =
          square.edgeIncl n hp.choose :=
        (fkSquarePeriodic_edgeIncl_eq n hp.choose).symm
      _ = e := hp.choose_spec
      _ = FK.edgeIncl 2 n hc.choose := hc.choose_spec.symm
  · rw [dif_neg hp]
    have hc : e ∉ Set.range (FK.edgeIncl 2 n) := by
      intro hc
      obtain ⟨ec, hec⟩ := hc
      let ep : Sym2 (square.OrbitVertex n) :=
        Sym2.map (fkSquarePeriodicVertexEquiv n).symm ec
      apply hp
      refine ⟨ep, ?_⟩
      rw [fkSquarePeriodic_edgeIncl_eq]
      have hmap : Sym2.map (fkSquarePeriodicVertexEquiv n) ep = ec := by
        induction ec using Sym2.inductionOn with
        | _ x y => simp [ep]
      rw [hmap]
      exact hec
    rw [dif_neg hc]



theorem fkSquarePeriodic_freeFiniteMeasure_eq (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    square.freeFiniteMeasure n hp hp1 hq =
      FK.freeFiniteMeasure 2 n hp hp1 hq := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (square.extendEdge n)
      (square.freeFinitePMF n hp hp1 hq).toMeasure =
    Measure.map (FK.extendEdge 2 n)
      (FK.fkPMF (FK.boxGraph 2 n) hp hp1 hq).toMeasure
  rw [fkSquarePeriodic_freeFinitePMF_eq_map]
  have hE : Measurable (fkSquarePeriodicConfigEquiv n) :=
    Measurable.of_discrete
  rw [← PMF.toMeasure_map _ _ hE]
  rw [Measure.map_map (square.measurable_extendEdge n) hE]
  apply Measure.map_congr
  filter_upwards [] with omega
  exact fkSquarePeriodic_extendEdge_reCfgIso n omega



theorem fkSquarePeriodic_wiredFiniteMeasure_eq (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    square.wiredFiniteMeasure n hp hp1 hq =
      FK.wiredFiniteMeasure 2 n hp hp1 hq := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (square.extendEdge n)
      (square.wiredFinitePMF n hp hp1 hq).toMeasure =
    Measure.map (FK.extendEdge 2 n)
      (FK.wiredFkPMF (FK.boxGraph 2 n) (FK.boxBoundary 2 n)
        hp hp1 hq).toMeasure
  rw [fkSquarePeriodic_wiredFinitePMF_eq_map]
  have hE : Measurable (fkSquarePeriodicConfigEquiv n) :=
    Measurable.of_discrete
  rw [← PMF.toMeasure_map _ _ hE]
  rw [Measure.map_map (square.measurable_extendEdge n) hE]
  apply Measure.map_congr
  filter_upwards [] with omega
  exact fkSquarePeriodic_extendEdge_reCfgIso n omega


end

end StatMech.FrontierD
