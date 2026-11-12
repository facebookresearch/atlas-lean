/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















import Code.FK.FreeDLRKernel
import Code.FK.InfiniteFiniteEnergy
import Code.FK.TrifurcationPatternCapstone
import Code.Ising.GibbsExtremeClose
import Code.Probability.InfiniteHarris

open MeasureTheory Set Topology
open scoped BigOperators ENNReal StatMech

namespace StatMech

namespace FK

open StatMech.Lattice
open StatMech.Percolation

variable {E : Type*}


def exactFiniteCylinder (F : Finset E) (omega : ConfigSpace E) :
    Set (ConfigSpace E) :=
  {eta | ∀ e ∈ F, eta e = omega e}

theorem exactFiniteCylinder_isOpen (F : Finset E) (omega : ConfigSpace E) :
    IsOpen (exactFiniteCylinder F omega) := by
  have heq : exactFiniteCylinder F omega =
      ⋂ e ∈ F, (fun eta : ConfigSpace E => eta e) ⁻¹' {omega e} := by
    ext eta
    simp only [exactFiniteCylinder, mem_setOf_eq, mem_iInter, mem_preimage,
      mem_singleton_iff]
  rw [heq]
  exact isOpen_biInter_finset fun e _ =>
    (isOpen_discrete {omega e}).preimage (continuous_apply e)



theorem isClopen_dependsOn_finset (A : Set (ConfigSpace E)) (hA : IsClopen A) :
    ∃ F : Finset E, StatMech.DependsOn A (F : Set E) := by
  classical
  have hlocal : ∀ omega : A, ∃ F : Finset E,
      omega.1 ∈ exactFiniteCylinder F omega.1 ∧
        exactFiniteCylinder F omega.1 ⊆ A := by
    intro omega
    obtain ⟨F, u, hu, hsub⟩ :=
      isOpen_pi_iff.mp hA.isOpen omega.1 omega.2
    refine ⟨F, ?_, ?_⟩
    · intro e he
      rfl
    · intro eta heta
      apply hsub
      intro e he
      rw [heta e he]
      exact (hu e he).2
  choose support hmem hsub using hlocal
  have hopen : ∀ omega : A,
      IsOpen (exactFiniteCylinder (support omega) omega.1) :=
    fun omega => exactFiniteCylinder_isOpen (support omega) omega.1
  have hcover : A ⊆ ⋃ omega : A,
      exactFiniteCylinder (support omega) omega.1 := by
    intro omega homega
    exact mem_iUnion.mpr ⟨⟨omega, homega⟩, hmem ⟨omega, homega⟩⟩
  obtain ⟨witnesses, hwitnesses⟩ :=
    hA.isClosed.isCompact.elim_finite_subcover
      (fun omega : A => exactFiniteCylinder (support omega) omega.1)
      hopen hcover
  let F : Finset E := witnesses.biUnion support
  refine ⟨F, ?_⟩
  intro omega eta hagree
  have forward : omega ∈ A → eta ∈ A := by
    intro homega
    obtain ⟨x, hxw, hx⟩ := mem_iUnion₂.mp (hwitnesses homega)
    apply hsub x
    intro e he
    calc
      eta e = omega e := hagree e (by
        exact Finset.mem_biUnion.mpr ⟨x, hxw, he⟩)
      _ = x.1 e := hx e he
  have backward : eta ∈ A → omega ∈ A := by
    intro heta
    obtain ⟨x, hxw, hx⟩ := mem_iUnion₂.mp (hwitnesses heta)
    apply hsub x
    intro e he
    calc
      omega e = eta e := (hagree e (by
        exact Finset.mem_biUnion.mpr ⟨x, hxw, he⟩)).symm
      _ = x.1 e := hx e he
  exact ⟨forward, backward⟩

variable {d : ℕ}



theorem isClopen_eq_boxRestrict_preimage
    (A : Set (ConfigSpace (Sym2 (Site d)))) (hA : IsClopen A) :
    ∃ (N : ℕ) (S : Set (ConfigSpace (Sym2 (boxVerts d N)))),
      A = boxRestrict d N ⁻¹' S ∧
        (IsIncreasing A → IsIncreasing S) := by
  classical
  obtain ⟨F, hF⟩ := isClopen_dependsOn_finset A hA
  obtain ⟨N, t, ht⟩ := cdc_finset_in_box F
  have hrange : ∀ e ∈ F, e ∈ Set.range (edgeIncl d N) := by
    intro e he
    rw [ht] at he
    obtain ⟨eb, _, heb⟩ := Finset.mem_image.mp he
    exact ⟨eb, heb⟩
  have hindicator : _root_.DependsOn
      (A.indicator (fun _ => (1 : ℝ))) (F : Set (Sym2 (Site d))) :=
    ih_indicator_dependsOn_of_event hF
  have hcylinder : A = MeasureTheory.cylinder F (F.restrict '' A) :=
    eq_cylinder_restrict_image A F hindicator
  let S : Set (ConfigSpace (Sym2 (boxVerts d N))) := extendEdge d N ⁻¹' A
  refine ⟨N, S, ?_, ?_⟩
  · change A = boxRestrict d N ⁻¹' (extendEdge d N ⁻¹' A)
    calc
      A = MeasureTheory.cylinder F (F.restrict '' A) := hcylinder
      _ = boxRestrict d N ⁻¹'
          (extendEdge d N ⁻¹' MeasureTheory.cylinder F (F.restrict '' A)) :=
        cylinder_eq_boxRestrict_preimage_extend N F (F.restrict '' A) hrange
      _ = boxRestrict d N ⁻¹' (extendEdge d N ⁻¹' A) :=
        congrArg (fun B => boxRestrict d N ⁻¹' (extendEdge d N ⁻¹' B)) hcylinder.symm
  · intro hinc
    exact isIncreasing_preimage_extendEdge d N hinc



theorem freeInfiniteVolume_le_isFKDLR_clopen {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (phi : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hphi : IsFKDLR d p q phi) :
    Ising.StochasticallyDominatedClopen
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d))))
      (phi : Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro A hAclopen hAinc
  obtain ⟨N, S, hAS, hS⟩ := isClopen_eq_boxRestrict_preimage A hAclopen
  rw [hAS]
  exact (dlr_infinite_sandwich hp hp1 hq
    hphi (hS hAinc)).1



theorem freeInfiniteVolume_weakDLR_extreme {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (phi1 phi2 : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hphi1 : IsFKDLR d p q phi1) (hphi2 : IsFKDLR d p q phi2)
    (a b : ℝ≥0∞) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hconv : (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d))))
      = a • (phi1 : Measure (ConfigSpace (Sym2 (Site d))))
        + b • (phi2 : Measure (ConfigSpace (Sym2 (Site d))))) :
    (phi1 : Measure (ConfigSpace (Sym2 (Site d)))) =
        (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 (Site d))))
      ∧ (phi2 : Measure (ConfigSpace (Sym2 (Site d)))) =
        (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 (Site d)))) := by
  have ha_top : a ≠ ⊤ := by
    intro ha_inf
    rw [ha_inf, top_add] at hab
    exact ENNReal.top_ne_one hab
  have hb_top : b ≠ ⊤ := by
    intro hb_inf
    rw [hb_inf, add_top] at hab
    exact ENNReal.top_ne_one hab
  exact Ising.gec_min_extreme ha hb hab ha_top hb_top hconv
    (freeInfiniteVolume_le_isFKDLR_clopen hp hp1 hq phi1 hphi1)
    (freeInfiniteVolume_le_isFKDLR_clopen hp hp1 hq phi2 hphi2)



theorem freeInfinite_canonical_uniqueness_of_isErgodic
    (hd : 1 ≤ d) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (herg : StatMech.ConfigSpace.IsErgodic (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d))))) :
    ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          {omega | numInfiniteClusters d omega = 0} = 1 ∨
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          {omega | numInfiniteClusters d omega = 1} = 1) ∧
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          (atLeastTwoInfinite d) = 0 ∧
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
  exact cbk_canonical_uniqueness
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    hd herg (freeInfiniteVolume_hasFiniteEnergyMerge hp hp1 hq)
    (freeInfinite_canonical_trifurcation_pos_of_top_pos hp hp1 hq)




theorem freeInfinite_q2_canonical_uniqueness_of_isErgodic
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (herg : StatMech.ConfigSpace.IsErgodic (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) :
        Measure (ConfigSpace (Sym2 (Site d))))) :
    ((freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
          {omega | numInfiniteClusters d omega = 0} = 1 ∨
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
          {omega | numInfiniteClusters d omega = 1} = 1) ∧
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
          (atLeastTwoInfinite d) = 0 ∧
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
          {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
  exact freeInfinite_canonical_uniqueness_of_isErgodic hd hp hp1
    (by norm_num : (1 : ℝ) ≤ 2) herg

end FK

end StatMech
