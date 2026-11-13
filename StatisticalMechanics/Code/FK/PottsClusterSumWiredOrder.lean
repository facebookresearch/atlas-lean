/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PottsClusterSumWiredErgodicity
import Code.FK.PottsInfiniteVolumePhaseTransport





open MeasureTheory Set
open scoped ENNReal StatMech

namespace StatMech.FK

open Lattice Percolation

open scoped Classical in


theorem pottsIIDLabelMeasure_clusterSumSpin_apply
    {d q : Nat} [NeZero q] (boundaryColor a : Fin q)
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    pottsIIDLabelMeasure d q
        {label | pottsClusterSumSpin boundaryColor omega label x = a} =
      if (cluster d omega x).Infinite then
        if boundaryColor = a then 1 else 0
      else (q : ENNReal)⁻¹ := by
  classical
  by_cases hinf : (cluster d omega x).Infinite
  · rw [if_pos hinf]
    have hspin : ∀ label : Site d -> Fin q,
        pottsClusterSumSpin boundaryColor omega label x = boundaryColor :=
      fun label => pottsClusterSumSpin_of_infinite boundaryColor omega label x hinf
    by_cases hba : boundaryColor = a
    · rw [if_pos hba]
      have hset : {label : Site d -> Fin q |
          pottsClusterSumSpin boundaryColor omega label x = a} = Set.univ := by
        ext label
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        rw [hspin label, hba]
      rw [hset, measure_univ]
    · rw [if_neg hba]
      have hset : {label : Site d -> Fin q |
          pottsClusterSumSpin boundaryColor omega label x = a} = ∅ := by
        ext label
        simp [hspin label, hba]
      rw [hset, measure_empty]
  · rw [if_neg hinf]
    have hfin : (cluster d omega x).Finite := not_infinite.mp hinf
    have hset : {label : Site d -> Fin q |
        pottsClusterSumSpin boundaryColor omega label x = a} =
        pottsLabelSumEvent hfin.toFinset a := by
      ext label
      simp only [Set.mem_setOf_eq]
      rw [pottsClusterSumSpin_of_finite boundaryColor omega label x hfin]
      simp only [pottsLabelSumEvent, MeasureTheory.mem_cylinder,
        Set.mem_setOf_eq]
      change (∑ y ∈ hfin.toFinset, label y) = a ↔
        (∑ y : hfin.toFinset, label y) = a
      rw [← Finset.sum_subtype hfin.toFinset (fun _ => Iff.rfl) label]
    rw [hset]
    exact pottsIIDLabelMeasure_pottsLabelSumEvent hfin.toFinset
      (by
        rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        have hx : x ∈ hfin.toFinset := by
          simpa using self_mem_cluster omega x
        simp [hempty] at hx) a



theorem pottsClusterSumJointMeasure_boundaryColor_apply
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure edgeMeasure] (x : Site d) :
    Measure.map Prod.fst
        (pottsClusterSumJointMeasure boundaryColor edgeMeasure)
        (pottsColorEvent d q x boundaryColor) =
      edgeMeasure {omega | (cluster d omega x).Infinite} +
        (q : ENNReal)⁻¹ * edgeMeasure {omega | (cluster d omega x).Finite} := by
  classical
  let A := pottsColorEvent d q x boundaryColor
  have hA : MeasurableSet A := (pottsColorEvent_isClopen d q x boundaryColor).isOpen.measurableSet
  rw [Measure.map_apply measurable_fst hA]
  rw [pottsClusterSumJointMeasure]
  rw [Measure.map_apply (measurable_pottsClusterSumJointFactor boundaryColor)
    (hA.preimage measurable_fst)]
  rw [Measure.prod_apply
    ((hA.preimage measurable_fst).preimage
      (measurable_pottsClusterSumJointFactor boundaryColor))]
  have hsection : ∀ omega : ConfigSpace (Sym2 (Site d)),
      pottsIIDLabelMeasure d q
          (Prod.mk omega ⁻¹'
            (pottsClusterSumJointFactor boundaryColor ⁻¹' (Prod.fst ⁻¹' A))) =
        if (cluster d omega x).Infinite then 1 else (q : ENNReal)⁻¹ := by
    intro omega
    have hpre : Prod.mk omega ⁻¹'
        (pottsClusterSumJointFactor boundaryColor ⁻¹' (Prod.fst ⁻¹' A)) =
        {label | pottsClusterSumSpin boundaryColor omega label x = boundaryColor} := by
      ext label
      rfl
    rw [hpre]
    simpa using pottsIIDLabelMeasure_clusterSumSpin_apply
      boundaryColor boundaryColor omega x
  simp_rw [hsection]
  let I : Set (ConfigSpace (Sym2 (Site d))) :=
    {omega | (cluster d omega x).Infinite}
  have hI : MeasurableSet I := measurableSet_clusterInfinite x
  have hIc : Iᶜ = {omega | (cluster d omega x).Finite} := by
    ext omega
    simp only [I, Set.mem_compl_iff, Set.mem_setOf_eq]
    exact not_infinite
  have hrepr : (fun omega : ConfigSpace (Sym2 (Site d)) =>
      if (cluster d omega x).Infinite then (1 : ENNReal) else (q : ENNReal)⁻¹) =
      fun omega => I.indicator (fun _ => (1 : ENNReal)) omega +
        Iᶜ.indicator (fun _ => (q : ENNReal)⁻¹) omega := by
    funext omega
    by_cases hinf : (cluster d omega x).Infinite
    · rw [if_pos hinf, Set.indicator_of_mem (show omega ∈ I from hinf),
        Set.indicator_of_notMem (show omega ∉ Iᶜ by simp [I, hinf])]
      simp
    · rw [if_neg hinf, Set.indicator_of_notMem (show omega ∉ I from hinf),
        Set.indicator_of_mem (show omega ∈ Iᶜ by simp [I, hinf])]
      simp
  rw [hrepr, lintegral_add_left]
  · rw [lintegral_indicator hI, lintegral_indicator hI.compl]
    simp only [lintegral_const, Measure.restrict_apply_univ, hIc]
    rw [one_mul, mul_comm]
  · exact measurable_const.indicator hI



theorem pottsClusterSumJointMeasure_otherColor_apply
    {d q : Nat} [NeZero q] (boundaryColor a : Fin q) (hba : boundaryColor ≠ a)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure edgeMeasure] (x : Site d) :
    Measure.map Prod.fst
        (pottsClusterSumJointMeasure boundaryColor edgeMeasure)
        (pottsColorEvent d q x a) =
      (q : ENNReal)⁻¹ * edgeMeasure {omega | (cluster d omega x).Finite} := by
  classical
  let A := pottsColorEvent d q x a
  have hA : MeasurableSet A := (pottsColorEvent_isClopen d q x a).isOpen.measurableSet
  rw [Measure.map_apply measurable_fst hA]
  rw [pottsClusterSumJointMeasure]
  rw [Measure.map_apply (measurable_pottsClusterSumJointFactor boundaryColor)
    (hA.preimage measurable_fst)]
  rw [Measure.prod_apply
    ((hA.preimage measurable_fst).preimage
      (measurable_pottsClusterSumJointFactor boundaryColor))]
  have hsection : ∀ omega : ConfigSpace (Sym2 (Site d)),
      pottsIIDLabelMeasure d q
          (Prod.mk omega ⁻¹'
            (pottsClusterSumJointFactor boundaryColor ⁻¹' (Prod.fst ⁻¹' A))) =
        if (cluster d omega x).Infinite then 0 else (q : ENNReal)⁻¹ := by
    intro omega
    have hpre : Prod.mk omega ⁻¹'
        (pottsClusterSumJointFactor boundaryColor ⁻¹' (Prod.fst ⁻¹' A)) =
        {label | pottsClusterSumSpin boundaryColor omega label x = a} := by
      ext label
      rfl
    rw [hpre]
    simpa [hba] using pottsIIDLabelMeasure_clusterSumSpin_apply
      boundaryColor a omega x
  simp_rw [hsection]
  let I : Set (ConfigSpace (Sym2 (Site d))) :=
    {omega | (cluster d omega x).Infinite}
  have hI : MeasurableSet I := measurableSet_clusterInfinite x
  have hIc : Iᶜ = {omega | (cluster d omega x).Finite} := by
    ext omega
    simp only [I, Set.mem_compl_iff, Set.mem_setOf_eq]
    exact not_infinite
  have hrepr : (fun omega : ConfigSpace (Sym2 (Site d)) =>
      if (cluster d omega x).Infinite then (0 : ENNReal) else (q : ENNReal)⁻¹) =
      fun omega => Iᶜ.indicator (fun _ => (q : ENNReal)⁻¹) omega := by
    funext omega
    by_cases hinf : (cluster d omega x).Infinite
    · rw [if_pos hinf,
        Set.indicator_of_notMem (show omega ∉ Iᶜ by simp [I, hinf])]
    · rw [if_neg hinf,
        Set.indicator_of_mem (show omega ∈ Iᶜ by simp [I, hinf])]
  rw [hrepr, lintegral_indicator hI.compl]
  simp only [lintegral_const, Measure.restrict_apply_univ, hIc]


theorem pottsClusterSumJointMeasure_boundaryColor_real
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure edgeMeasure] (x : Site d) :
    (Measure.map Prod.fst
        (pottsClusterSumJointMeasure boundaryColor edgeMeasure)).real
        (pottsColorEvent d q x boundaryColor) =
      edgeMeasure.real {omega | (cluster d omega x).Infinite} +
        (1 / (q : Real)) *
          edgeMeasure.real {omega | (cluster d omega x).Finite} := by
  have h := congrArg ENNReal.toReal
    (pottsClusterSumJointMeasure_boundaryColor_apply
      boundaryColor edgeMeasure x)
  have htopI : edgeMeasure {omega | (cluster d omega x).Infinite} ≠ ⊤ :=
    measure_ne_top edgeMeasure _
  have htopF : edgeMeasure {omega | (cluster d omega x).Finite} ≠ ⊤ :=
    measure_ne_top edgeMeasure _
  have hqtop : (q : ENNReal)⁻¹ *
      edgeMeasure {omega | (cluster d omega x).Finite} ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by exact_mod_cast NeZero.ne q)) htopF
  rw [ENNReal.toReal_add htopI hqtop, ENNReal.toReal_mul,
    ENNReal.toReal_inv] at h
  simpa only [Measure.real, ENNReal.toReal_natCast, one_div] using h



theorem wiredPottsClusterSum_boundaryColorBias_eq_fkTheta
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    let hqR : (1 : Real) <= q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    (Measure.map Prod.fst
        (pottsClusterSumJointMeasure boundaryColor
          (wiredInfiniteVolume d hp hp1
            (zero_lt_one.trans_le hqR) : Measure _))).real
        (pottsColorEvent d q (origin d) boundaryColor) - 1 / (q : Real) =
      ((q : Real) - 1) / q *
        fkTheta d hp hp1 (zero_lt_one.trans_le hqR) (q := q) := by
  dsimp only
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let mu : Measure (ConfigSpace (Sym2 (Site d))) :=
    wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR)
  let I : Set (ConfigSpace (Sym2 (Site d))) :=
    {omega | (cluster d omega (origin d)).Infinite}
  have hI : MeasurableSet I := measurableSet_clusterInfinite (origin d)
  have hfinite : {omega : ConfigSpace (Sym2 (Site d)) |
      (cluster d omega (origin d)).Finite} = Iᶜ := by
    ext omega
    simp only [I, Set.mem_setOf_eq, Set.mem_compl_iff]
    exact not_infinite.symm
  have hlaw := pottsClusterSumJointMeasure_boundaryColor_real
    boundaryColor mu (origin d)
  have hcomp : mu.real Iᶜ = 1 - mu.real I := by
    rw [measureReal_compl hI, probReal_univ]
  rw [hfinite, hcomp] at hlaw
  have htheta : mu.real I =
      fkTheta d hp hp1 (zero_lt_one.trans_le hqR) (q := q) := rfl
  rw [htheta] at hlaw
  rw [hlaw]
  have hq0 : (0 : Real) < q := zero_lt_one.trans_le hqR
  field_simp
  ring

end StatMech.FK
