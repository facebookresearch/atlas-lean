/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FK.PeriodicPlanarGraph
import Code.BeffaraDC.PlanarFKDuality
import Code.RSW.SelfDuality

open Set

namespace StatMech
namespace FK
namespace PeriodicPlanar

open BeffaraDC Lattice


theorem dualParam_involutive {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    dualParam (dualParam p q) q = p := by
  have hd : (1 - p) * q + p ≠ 0 := by positivity
  unfold dualParam
  field_simp [hd]
  ring



theorem dual_parameter_boundary_involutive {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (bc : BoundaryCondition) :
    dualParam p q ∈ Ioo (0 : ℝ) 1 ∧
      dualParam (dualParam p q) q = p ∧
      RSW.dualBC (RSW.dualBC bc) = bc := by
  exact ⟨dualParam_mem_Ioo hp hp1 hq, dualParam_involutive hp hp1 hq,
    RSW.dualBC_dualBC bc⟩




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
