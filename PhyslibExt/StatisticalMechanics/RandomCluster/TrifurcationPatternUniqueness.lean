/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationPatternMeasure
public import PhyslibExt.StatisticalMechanics.RandomCluster.WiredTranslationInvariance
public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeTranslationInvariance
public import PhyslibExt.StatisticalMechanics.RandomCluster.WiredLimitErgodicity
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKGeneralQTranslation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonBurtonKeane

/-!
# Trifurcations and uniqueness of the infinite cluster for infinite-volume FK limits

If the free or wired infinite-volume random-cluster measure gives positive mass to infinitely many
infinite clusters, the origin is a trifurcation with positive probability; for the wired `q = 2`
limit this yields uniqueness of the infinite cluster.

## i. Overview

The free and wired infinite-volume limits for `q ≥ 1` are translation invariant, and changing the
configuration on a finite set of edges is absolutely continuous for them. A pattern argument then
shows that, when there are infinitely many infinite clusters with positive probability, the origin
is a (canonical) trifurcation with positive probability. The Burton–Keane counting argument,
together with ergodicity and the finite-energy merge property of the wired `q = 2` limit, rules this
out, so the number of infinite clusters is almost surely `0` or `1`. The trifurcation results are
implications whose only premise `htop` is the event they refute; they are proved unconditionally
otherwise, under `0 < p < 1` and `1 ≤ q`. The uniqueness headline
`wiredInfinite_q2_canonical_uniqueness` is proved unconditionally, under `d ≥ 1` and `0 < p < 1`.

## ii. Key results

- `wiredInfinite_q2_canonical_uniqueness` : for the wired `q = 2` limit on `ℤᵈ`, the number of
  infinite clusters is almost surely `0` or almost surely `1`, and at most one almost surely.
- `wiredInfinite_trifurcation_pos_of_top_pos` : for the wired limit with `q ≥ 1`, infinitely many
  infinite clusters with positive probability imply a trifurcation at the origin with positive
  probability.
- `freeInfinite_trifurcation_pos_of_top_pos` : the same for the free limit.

## iii. Table of contents

- A. Trifurcations for `q ≥ 1`
- B. Trifurcations for `q = 2`
- C. Uniqueness of the infinite cluster

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989).
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 5.99.
-/

@[expose] public section

open MeasureTheory Set
open StatMech.Lattice StatMech.ConfigSpace

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech.FK

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Trifurcations for `q ≥ 1` -/

/-- For `q ≥ 1`, if the wired infinite-volume measure gives positive mass to infinitely many
infinite clusters, the origin is a trifurcation with positive probability. -/
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

/-- For `q ≥ 1`, if the free infinite-volume measure gives positive mass to infinitely many
infinite clusters, the origin is a trifurcation with positive probability. -/
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

lemma wiredInfinite_canonical_trifurcation_pos_of_top_pos
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

lemma freeInfinite_canonical_trifurcation_pos_of_top_pos
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

/-! ## B. Trifurcations for `q = 2` -/

lemma wiredInfinite_q2_trifurcation_pos_of_top_pos
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

lemma freeInfinite_q2_trifurcation_pos_of_top_pos
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

lemma wiredInfinite_q2_canonical_trifurcation_pos_of_top_pos
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

lemma freeInfinite_q2_canonical_trifurcation_pos_of_top_pos
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

/-! ## C. Uniqueness of the infinite cluster -/

/-- Burton–Keane uniqueness for the wired `q = 2` limit on `ℤᵈ`: the number of infinite clusters is
almost surely `0` or almost surely `1`, two or more infinite clusters have probability zero, and at
most one infinite cluster has probability one. -/
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
