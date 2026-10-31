/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CriticalAssembly
public import PhyslibExt.StatisticalMechanics.RandomCluster.MonotoneInPBoundaryCondition

/-!
# Monotonicity in `p` of buffered wired measures

Increasing cylinder events have probability nondecreasing in `p` under the buffered wired
random-cluster measures, in finite and in infinite volume; under a cylinder approximation of the
percolation event this makes `θ(p, q)` monotone and yields critical-point duality.

## i. Overview

For `q ≥ 1` the finite-volume wired measure is stochastically increasing in `p` (Holley's
inequality), so increasing cylinder events have nondecreasing probability; this passes to the
infinite-volume limit through convergence of cylinder probabilities. If the percolation
probability is a limit of probabilities of increasing cylinders (the cylinder approximation),
it is monotone in `p`, which feeds the critical relation of `CriticalAssembly`.
The cylinder monotonicity results are unconditional (only `0 < p₁ ≤ p₂ < 1`, `1 ≤ q`). The
headline `PeriodicGraph.dualCritical_relation_of_cylinderApproximation_noCoexistence` is
conditional: it assumes `HasPercolationCylinderApproximation` for the primal and dual graphs,
`DualSubcriticalCoverage` and `DualNoCoexistence`, besides `pc, pc* ∈ (0, 1)` and `1 ≤ q`.

## ii. Key results

- `PeriodicGraph.wiredBufferedInfiniteVolume_real_cylinder_monotone_in_p` : increasing cylinders
  are monotone in `p` under the infinite-volume wired measure.
- `PeriodicGraph.wiredPercolationProbability_monotoneOn_of_cylinderApproximation` : a cylinder
  approximation makes `θ(p, q)` monotone on `(0, 1)`.
- `PeriodicGraph.dualCritical_relation_of_cylinderApproximation_noCoexistence` : the critical
  relation from cylinder approximations, coverage and no-coexistence.

## iii. Table of contents

- A. Monotonicity of cylinder probabilities
- B. Monotonicity of the percolation probability
- C. The critical relation

## iv. References

- R. Holley, *Remarks on the FKG inequalities*, Comm. Math. Phys. 36 (1974).
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 3.21.
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

section Countable

variable [Countable V]

/-! ## A. Monotonicity of cylinder probabilities -/

lemma PeriodicGraph.wiredBufferedMeasure_real_cylinder_monotone_in_p
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

/-- For `q ≥ 1`, an increasing cylinder event has probability nondecreasing in `p` under the
buffered wired infinite-volume measure. -/
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

/-! ## B. Monotonicity of the percolation probability -/

/-- Cylinder approximation of percolation: there are increasing cylinder events whose probabilities
under the buffered wired infinite-volume measure converge to `θ(p, q)` for every `p ∈ (0, 1)`. -/
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

/-- Under a cylinder approximation, the wired percolation probability is monotone in `p` on
`(0, 1)`. -/
lemma PeriodicGraph.wiredPercolationProbability_monotoneOn_of_cylinderApproximation
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

/-! ## C. The critical relation -/

/-- Conditional critical-point duality: cylinder approximations for the primal and dual graphs, dual
subcritical coverage and no-coexistence give `pc* = (pc)*` and
`pc / (1 - pc) · pc* / (1 - pc*) = q`. -/
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
