/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FrontierD.FKQgt4WiredPhaseInput
import Code.FK.WiredTailTriviality

open MeasureTheory Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section



theorem numInfiniteClusters_eq_one_subset_hasInfiniteClusterEvent (d : Nat) :
    {omega | numInfiniteClusters d omega = 1} ⊆
      hasInfiniteClusterEvent d := by
  intro omega hone
  have hset : ∃ C : Set (Site d), infiniteClusters d omega = {C} := by
    change (infiniteClusters d omega).encard = 1 at hone
    rw [Set.encard_eq_one] at hone
    exact hone
  obtain ⟨C, hC⟩ := hset
  have hCmem : C ∈ infiniteClusters d omega := by
    rw [hC]
    exact Set.mem_singleton C
  obtain ⟨hCinf, x, hxC⟩ := hCmem
  have hxinf : (cluster d omega x).Infinite := by
    rw [← hxC]
    exact hCinf
  rw [hasInfiniteClusterEvent, Set.mem_iUnion]
  exact ⟨x, hxinf⟩



theorem wiredInfiniteVolume_hasInfiniteClusterEvent_eq_one_of_percolation_pos
    {d : Nat} (hd : 1 ≤ d) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (htheta :
      0 < ((FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
        Measure (ConfigSpace (Sym2 (Site d)))).real (percolationEvent d)) :
    ((FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))) (hasInfiniteClusterEvent d) = 1 := by
  let mu : Measure (ConfigSpace (Sym2 (Site d))) :=
    FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  have hone : mu {omega | numInfiniteClusters d omega = 1} = 1 := by
    apply oneInfiniteCluster_ae_of_theta_pos_of_zero_one mu
    · simpa only [mu] using htheta
    · exact (FK.wiredInfinite_canonical_uniqueness_all_parameters
        hd hp hp1 hq).1
  apply le_antisymm
  · calc
      mu (hasInfiniteClusterEvent d) ≤ mu Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  calc
    1 = mu {omega | numInfiniteClusters d omega = 1} := hone.symm
    _ ≤ mu (hasInfiniteClusterEvent d) :=
      measure_mono (numInfiniteClusters_eq_one_subset_hasInfiniteClusterEvent d)



theorem wiredInfiniteVolume_hasInfiniteClusterEvent_eq_one_iff_percolation_pos
    {d : Nat} (hd : 1 ≤ d) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    ((FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))) (hasInfiniteClusterEvent d) = 1 ↔
    0 < ((FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (percolationEvent d) := by
  constructor
  · exact wiredInfiniteVolume_percolationEvent_pos_of_hasInfiniteCluster_ae
      hp hp1 hq
  · exact wiredInfiniteVolume_hasInfiniteClusterEvent_eq_one_of_percolation_pos
      hd hp hp1 hq

end

end StatMech.FrontierD
