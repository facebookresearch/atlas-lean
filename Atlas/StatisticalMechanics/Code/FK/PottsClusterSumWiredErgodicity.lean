/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PottsClusterSumProductErgodicity
import Code.FK.WiredTailTriviality











open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal StatMech

namespace StatMech.FK

open StatMech.Lattice



theorem wiredInfiniteVolume_axisShift_ergodic_generalQ
    {d : Nat} (hd : 1 <= d) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    _root_.Ergodic
      (ConfigSpace.shift (freeAxisTranslation hd) :
        ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d)))
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  let mu := (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site d))))
  have hti : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d)) mu :=
    fkgqt_wiredIV_isTranslationInvariant hp hp1 hq
  refine ⟨hti (freeAxisTranslation hd), ⟨?_⟩⟩
  intro s hs hinv
  have hinvPow : forall n : Nat,
      ConfigSpace.shift (freeAxisTranslationPower hd n) ⁻¹' s = s := by
    intro n
    rw [shift_freeAxisTranslationPower]
    exact Function.IsFixedPt.preimage_iterate hinv n
  obtain ⟨t, ht, hae⟩ :=
    ati_sequenceInvariant_aeTail (fkTailEdgeWindow d)
      fkTailEdgeWindow_mono (freeAxisTranslationPower hd)
      (freeAxisTranslationPower_escape hd) hti s hs hinvPow
  rw [eventuallyConst_set']
  rcases wiredInfiniteVolume_tail_trivial_generalQ hp hp1 hq t ht with
      ht0 | ht1
  · exact Or.inl (hae.trans (ae_eq_empty.mpr ht0))
  · right
    apply hae.trans
    rw [ae_eq_univ]
    rw [measure_compl ht.measurableSet (measure_ne_top mu t), ht1,
      measure_univ]
    simp



theorem wiredInfiniteVolume_prod_pottsIIDLabel_axis_ergodic
    {d q : Nat} [NeZero q] (hd : 1 <= d) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) :
    let hqR : (1 : Real) <= q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    _root_.Ergodic
      (Prod.map
        (ConfigSpace.shift (freeAxisTranslation hd) :
          ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d)))
        (pottsLabelShift (freeAxisTranslation hd)))
      ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _).prod
        (pottsIIDLabelMeasure d q)) := by
  dsimp only
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  apply ergodic_prod_of_mixingAgainst
    (ConfigSpace.shift (freeAxisTranslation hd))
    (pottsLabelShift (freeAxisTranslation hd))
    (wiredInfiniteVolume_axisShift_ergodic_generalQ hd hp hp1 hqR)
    (pottsIIDLabelMeasure_measurePreserving (q := q)
      (freeAxisTranslation hd))
    (measurableCylinders (fun _ : Site d => Fin q))
  · exact generateFrom_measurableCylinders
  · exact isPiSystem_measurableCylinders
  · exact ⟨fun _ => Set.univ,
      fun _ => univ_mem_measurableCylinders _, by rw [iUnion_const]⟩
  · intro B hB
    exact MeasurableSet.of_mem_measurableCylinders hB
  · exact pottsIIDLabel_axis_mixingAgainst hd



theorem wiredInfiniteVolume_pottsClusterFactorInput_isErgodicFor
    {d q : Nat} [NeZero q] (hd : 1 <= d) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) :
    let hqR : (1 : Real) <= q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    IsErgodicFor pottsClusterFactorInputShift
      ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _).prod
        (pottsIIDLabelMeasure d q)) := by
  dsimp only
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let edgeMeasure :=
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) :
      Measure (ConfigSpace (Sym2 (Site d))))
  let sourceMeasure := edgeMeasure.prod (pottsIIDLabelMeasure d q)
  have hti : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d)) edgeMeasure :=
    fkgqt_wiredIV_isTranslationInvariant hp hp1 hqR
  have haxis : _root_.Ergodic
      (Prod.map
        (ConfigSpace.shift (freeAxisTranslation hd) :
          ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d)))
        (pottsLabelShift (freeAxisTranslation hd))) sourceMeasure :=
    wiredInfiniteVolume_prod_pottsIIDLabel_axis_ergodic hd hp hp1
  refine ⟨?_, ?_⟩
  · intro g
    have hprod := (hti g).prod
      (pottsIIDLabelMeasure_measurePreserving (q := q) g)
    convert hprod using 1
  · intro s hs hinv
    have hinvAxis : (Prod.map
        (ConfigSpace.shift (freeAxisTranslation hd) :
          ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d)))
        (pottsLabelShift (freeAxisTranslation hd))) ⁻¹' s = s := by
      simpa only [pottsClusterFactorInputShift, Prod.map_apply] using
        hinv (freeAxisTranslation hd)
    rcases haxis.toPreErgodic.prob_eq_zero_or_one hs hinvAxis with
      hzero | hone
    · exact Or.inl hzero
    · right
      simpa only [measure_univ] using hone



theorem wiredPottsClusterSumJointMeasure_isErgodicFor
    {d q : Nat} [NeZero q] (hd : 1 <= d) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (boundaryColor : Fin q) :
    let hqR : (1 : Real) <= q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    IsErgodicFor (pottsJointShift (d := d) (q := q))
      (pottsClusterSumJointMeasure (d := d) (q := q) boundaryColor
        (wiredInfiniteVolume d hp hp1
          (zero_lt_one.trans_le hqR) : Measure _)) := by
  dsimp only
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))) :=
    wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR)
  exact pottsClusterSumJointMeasure_isErgodicFor
    (d := d) (q := q) boundaryColor edgeMeasure
    (wiredInfiniteVolume_pottsClusterFactorInput_isErgodicFor
      (d := d) (q := q) hd hp hp1)



theorem wiredPottsClusterSumSpinMarginal_isErgodicFor
    {d q : Nat} [NeZero q] (hd : 1 <= d) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (boundaryColor : Fin q) :
    let hqR : (1 : Real) <= q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    IsErgodicFor (pottsSpinShift (d := d) (q := q))
      (Measure.map Prod.fst
        (pottsClusterSumJointMeasure (d := d) (q := q) boundaryColor
          (wiredInfiniteVolume d hp hp1
            (zero_lt_one.trans_le hqR) : Measure _))) := by
  dsimp only
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))) :=
    wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR)
  exact pottsClusterSumSpinMarginal_isErgodicFor
    (d := d) (q := q) boundaryColor edgeMeasure
    (wiredPottsClusterSumJointMeasure_isErgodicFor
      (d := d) (q := q) hd hp hp1 boundaryColor)

end StatMech.FK
