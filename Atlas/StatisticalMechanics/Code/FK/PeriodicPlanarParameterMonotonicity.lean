/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.PeriodicPlanarCriticalAssembly
import Code.FK.FKUniquenessClose2

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

section Countable

variable [Countable V]



theorem PeriodicGraph.wiredBufferedMeasure_real_cylinder_monotone_in_p
    (P : PeriodicGraph V) {N m : Nat} (hNm : N <= m)
    {p1 p2 q : Real} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) (hp12 : p1 <= p2) (hq : 1 <= q)
    {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    (P.wiredBufferedMeasure m hp1 hp1' (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) <=
      (P.wiredBufferedMeasure m hp2 hp2' (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
  rw [P.wiredBufferedMeasure_real_cylinder hNm hp1 hp1'
      (zero_lt_one.trans_le hq),
    P.wiredBufferedMeasure_real_cylinder hNm hp2 hp2'
      (zero_lt_one.trans_le hq)]
  let A := P.bufferedRestrictLE hNm ⁻¹' S
  have hA : IsIncreasing A := fun _ _ home hmem =>
    hS (P.monotone_bufferedRestrictLE hNm home) hmem
  simpa only [bcProb_clique_eq_wiredFkProb] using
    (bcProb_monotone_in_p (P.bufferedGraph m)
      (StatMech.Lattice.boundaryCliqueGraph (P.bufferedBoundary m))
      hp1 hp1' hp2 hp2' hp12 hq hA)



theorem PeriodicGraph.wiredBufferedInfiniteVolume_real_cylinder_monotone_in_p
    (P : PeriodicGraph V) (N : Nat)
    {p1 p2 q : Real} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) (hp12 : p1 <= p2) (hq : 1 <= q)
    {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    (P.wiredBufferedInfiniteVolume hp1 hp1' (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) <=
      (P.wiredBufferedInfiniteVolume hp2 hp2' (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
  have hlim1 := P.wiredBufferedMeasure_tendsto_cylinder N hp1 hp1' hq hS
  have hlim2 := P.wiredBufferedMeasure_tendsto_cylinder N hp2 hp2' hq hS
  apply le_of_tendsto_of_tendsto hlim1 hlim2
  filter_upwards [eventually_ge_atTop N] with m hNm
  exact P.wiredBufferedMeasure_real_cylinder_monotone_in_p hNm
    hp1 hp1' hp2 hp2' hp12 hq hS



def PeriodicGraph.HasPercolationCylinderApproximation
    (P : PeriodicGraph V) (q : Real) : Prop :=
  exists A : forall n : Nat,
      Set (ConfigSpace (Sym2 (P.BufferedVertex n))),
    (forall n, IsIncreasing (A n)) /\
      forall p (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q),
        Tendsto
          (fun n =>
            (P.wiredBufferedInfiniteVolume hp hp1
                (zero_lt_one.trans_le hq) :
              Measure (ConfigSpace (Sym2 V))).real
              (P.bufferedCylinder n (A n)))
          atTop (nhds (P.wiredPercolationProbability p q))



theorem PeriodicGraph.wiredPercolationProbability_monotoneOn_of_cylinderApproximation
    (P : PeriodicGraph V) {q : Real} (hq : 1 <= q)
    (happrox : P.HasPercolationCylinderApproximation q) :
    MonotoneOn (fun p => P.wiredPercolationProbability p q)
      (Ioo (0 : Real) 1) := by
  rintro p1 hp1 p2 hp2 hp12
  obtain ⟨A, hA, hlim⟩ := happrox
  apply le_of_tendsto_of_tendsto
    (hlim p1 hp1.1 hp1.2 hq) (hlim p2 hp2.1 hp2.2 hq)
  exact Filter.Eventually.of_forall fun n =>
    P.wiredBufferedInfiniteVolume_real_cylinder_monotone_in_p n
      hp1.1 hp1.2 hp2.1 hp2.2 hp12 hq (hA n)

end Countable



theorem PeriodicGraph.dualCritical_relation_of_cylinderApproximation_noCoexistence
    [Countable V] [Countable W]
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W)
    {q : Real}
    (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hq : 1 <= q)
    (happrox : P.HasPercolationCylinderApproximation q)
    (happroxDual : Pdual.HasPercolationCylinderApproximation q)
    (hcoverage : DualSubcriticalCoverage
      (fun p => Pdual.wiredPercolates p q) (P.criticalPoint q) q)
    (hnoCoexistence : DualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q) :
    BeffaraDC.dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  apply P.dualCritical_relation_of_monotonicity_noCoexistence Pdual
    hpc hpcDual (zero_lt_one.trans_le hq)
  · exact P.wiredPercolationProbability_monotoneOn_of_cylinderApproximation hq happrox
  · exact Pdual.wiredPercolationProbability_monotoneOn_of_cylinderApproximation
      hq happroxDual
  · exact hcoverage
  · exact hnoCoexistence

end StatMech.FK.PeriodicPlanar
