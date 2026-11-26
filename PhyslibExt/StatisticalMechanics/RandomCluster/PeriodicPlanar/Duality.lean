/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Graph
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.PlanarFKDuality
public import MathlibExt.Probability.Percolation.RSW.SelfDuality

/-!
# Planar duality of random-cluster parameters

The dual parameter map `p ↦ p*` is an involution, and the free finite planar random-cluster
measure equals the wired dual measure at the dual parameter.

## i. Overview

For `q > 0` the dual parameter `p* = (1 - p) q / ((1 - p) q + p)` satisfies
`p / (1 - p) · p* / (1 - p*) = q`, maps `(0, 1)` to itself and is an involution; free and wired
boundary conditions are exchanged. On a finite planar subgraph of `ℤ²` the free random-cluster
measure at `(p, q)` coincides with the dual-wired measure at `(p*, q)` under the edge bijection.
All three results are unconditional (only `0 < p < 1` and `0 < q`).

## ii. Key results

- `dualParam_involutive` : `(p*)* = p`.
- `dual_parameter_boundary_involutive` : `p* ∈ (0, 1)`, `(p*)* = p`, and boundary duality is an
  involution.
- `finite_planar_free_dual_exchange` : the free planar FK measure equals the wired dual measure at
  `p*`.

## iii. Table of contents

- A. The dual parameter
- B. Finite planar duality

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Section 6.1.
-/

@[expose] public section

open Set

namespace StatMech
namespace FK
namespace PeriodicPlanar

open BeffaraDC StatMech.Lattice

/-! ## A. The dual parameter -/

/-- The dual parameter map is an involution on `(0, 1)` for `q > 0`. -/
lemma dualParam_involutive {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    dualParam (dualParam p q) q = p := by
  have hd : (1 - p) * q + p ≠ 0 := by positivity
  unfold dualParam
  field_simp [hd]
  ring

/-- The dual parameter lies in `(0, 1)` and is an involution, and the boundary-condition duality is
an involution. -/
lemma dual_parameter_boundary_involutive {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (bc : BoundaryCondition) :
    dualParam p q ∈ Ioo (0 : ℝ) 1 ∧
      dualParam (dualParam p q) q = p ∧
      RSW.dualBC (RSW.dualBC bc) = bc := by
  exact ⟨dualParam_mem_Ioo hp hp1 hq, dualParam_involutive hp hp1 hq,
    RSW.dualBC_dualBC bc⟩

/-! ## B. Finite planar duality -/

/-- Free-to-wired duality on a finite planar subgraph of `ℤ²`: the dual parameter lies in `(0, 1)`,
free boundary dualizes to wired, and the free random-cluster measure at `(p, q)` equals the
dual-wired measure at `(p*, q)`. -/
theorem finite_planar_free_dual_exchange
    (P : Lattice.PlanarZ2Subgraph) (omega : ConfigSpace (Sym2 P.V))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    dualParam p q ∈ Ioo (0 : ℝ) 1 ∧
      RSW.dualBC BoundaryCondition.free = BoundaryCondition.wired ∧
      FK.fkProb P.G p q omega =
        pfdDualProb P (dualParam p q) q omega := by
  exact ⟨dualParam_mem_Ioo hp hp1 hq, RSW.dualBC_free,
    pfd_fkProb_duality P omega hp hp1 hq⟩

end PeriodicPlanar
end FK
end StatMech
