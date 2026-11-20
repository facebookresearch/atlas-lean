/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Percolation.TrifurcationPatternMeasure
import Code.FK.FKLimitsClose
import Code.FK.BulkDeviationProof
import Code.FK.FKLimitsErgodicUncond
import Code.FK.FKGeneralQTranslation
import Code.Percolation.CanonBurtonKeane

open MeasureTheory Set
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.FK

open StatMech.Percolation

variable {d : ℕ}




theorem wiredInfinite_trifurcation_pos_of_top_pos
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (htop : 0 < (wiredInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure _)
        {omega | numInfiniteClusters d omega = ⊤}) :
    0 < (wiredInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure _)
        {omega | IsTrifurcation d omega 0} := by
  exact trifurcation_at_origin_pos_of_patternAC (d := d)
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (fkgqt_wiredIV_isTranslationInvariant (d := d) hp hp1 hq)
    (fun I eta => wiredInfinite_setPattern_absolutelyContinuous
      (d := d) hp hp1 hq I eta)
    htop



theorem freeInfinite_trifurcation_pos_of_top_pos
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (htop : 0 < (freeInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure _)
        {omega | numInfiniteClusters d omega = ⊤}) :
    0 < (freeInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure _)
        {omega | IsTrifurcation d omega 0} := by
  exact trifurcation_at_origin_pos_of_patternAC (d := d)
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (fkgqt_freeIV_isTranslationInvariant (d := d) hp hp1 hq)
    (fun I eta => freeInfinite_setPattern_absolutelyContinuous
      (d := d) hp hp1 hq I eta)
    htop



theorem wiredInfinite_canonical_trifurcation_pos_of_top_pos
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (htop : 0 < (wiredInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure _)
        {omega | numInfiniteClusters d omega = ⊤}) :
    0 < (wiredInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure _)
        {omega | IsCanonicalTrifurcation d omega 0} := by
  exact canonical_trifurcation_at_origin_pos_of_patternAC (d := d)
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (fkgqt_wiredIV_isTranslationInvariant (d := d) hp hp1 hq)
    (fun I eta => wiredInfinite_setPattern_absolutelyContinuous
      (d := d) hp hp1 hq I eta)
    htop



theorem freeInfinite_canonical_trifurcation_pos_of_top_pos
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (htop : 0 < (freeInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure _)
        {omega | numInfiniteClusters d omega = ⊤}) :
    0 < (freeInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure _)
        {omega | IsCanonicalTrifurcation d omega 0} := by
  exact canonical_trifurcation_at_origin_pos_of_patternAC (d := d)
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (fkgqt_freeIV_isTranslationInvariant (d := d) hp hp1 hq)
    (fun I eta => freeInfinite_setPattern_absolutelyContinuous
      (d := d) hp hp1 hq I eta)
    htop



theorem wiredInfinite_q2_trifurcation_pos_of_top_pos
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (htop : 0 < (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
      {omega | numInfiniteClusters d omega = ⊤}) :
    0 < (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
      {omega | IsTrifurcation d omega 0} := by
  exact trifurcation_at_origin_pos_of_patternAC (d := d)
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
    (flc_wiredIV_isTranslationInvariant (d := d) hp hp1)
    (fun I eta => wiredInfinite_setPattern_absolutelyContinuous (d := d) hp hp1
      (by norm_num : (1 : ℝ) ≤ 2) I eta)
    htop



theorem freeInfinite_q2_trifurcation_pos_of_top_pos
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (htop : 0 < (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
      {omega | numInfiniteClusters d omega = ⊤}) :
    0 < (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
      {omega | IsTrifurcation d omega 0} := by
  exact trifurcation_at_origin_pos_of_patternAC (d := d)
    (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
    (bdp_freeIV_isTranslationInvariant (d := d) hp hp1)
    (fun I eta => freeInfinite_setPattern_absolutelyContinuous (d := d) hp hp1
      (by norm_num : (1 : ℝ) ≤ 2) I eta)
    htop



theorem wiredInfinite_q2_canonical_trifurcation_pos_of_top_pos
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (htop : 0 < (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
      {omega | numInfiniteClusters d omega = ⊤}) :
    0 < (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
      {omega | IsCanonicalTrifurcation d omega 0} := by
  exact canonical_trifurcation_at_origin_pos_of_patternAC (d := d)
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
    (flc_wiredIV_isTranslationInvariant (d := d) hp hp1)
    (fun I eta => wiredInfinite_setPattern_absolutelyContinuous (d := d) hp hp1
      (by norm_num : (1 : ℝ) ≤ 2) I eta)
    htop



theorem freeInfinite_q2_canonical_trifurcation_pos_of_top_pos
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (htop : 0 < (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
      {omega | numInfiniteClusters d omega = ⊤}) :
    0 < (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
      {omega | IsCanonicalTrifurcation d omega 0} := by
  exact canonical_trifurcation_at_origin_pos_of_patternAC (d := d)
    (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
    (bdp_freeIV_isTranslationInvariant (d := d) hp hp1)
    (fun I eta => freeInfinite_setPattern_absolutelyContinuous (d := d) hp hp1
      (by norm_num : (1 : ℝ) ≤ 2) I eta)
    htop



theorem wiredInfinite_q2_canonical_uniqueness
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ((wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
          {omega | numInfiniteClusters d omega = 0} = 1 ∨
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
          {omega | numInfiniteClusters d omega = 1} = 1) ∧
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
          (atLeastTwoInfinite d) = 0 ∧
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
          {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
  exact cbk_canonical_uniqueness
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
    hd (feu_wiredIV_isErgodic hd hp hp1)
    (wiredInfiniteVolume_hasFiniteEnergyMerge hp hp1
      (by norm_num : (1 : ℝ) ≤ 2))
    (wiredInfinite_q2_canonical_trifurcation_pos_of_top_pos hp hp1)

end StatMech.FK
