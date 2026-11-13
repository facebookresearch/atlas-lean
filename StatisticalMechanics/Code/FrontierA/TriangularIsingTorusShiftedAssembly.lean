/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusLocalAngularSplit
import Code.FrontierA.SurfaceKacWardShiftedCycleAssembly
import Code.FrontierA.TriangularIsingTorusSurfaceReduction
import Code.FrontierA.TriangularIsingTorusSplitCyclePhase
import Code.FrontierA.TriangularIsingTorusSplitIsotropy





namespace StatMech.FrontierA




theorem triangularTorus_native_det_square_of_localSplit
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hphase : KWLocalAngularSplitShiftedCyclePhase
      (triangularTorusLocalAngularData L rho hrho)
      (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L))
      (triangularTorusSurfaceSpin 0 0))
    (hisotropic : SurfaceDisjointCycleIsotropic
      (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
        (triangularTorusLocalPortOrder L))
      (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L)))
    (weight : Sym2 (ZMod L × ZMod L) -> Complex) :
    (1 - kwGraphTransition (triangularTorusGraph L) weight
      (triangularTorusGraphPhase L rho 1 1)).det =
      surfaceQuadraticEvenPolynomial (triangularTorusGraph L)
        (triangularTorusSurfaceEdgeClass L)
        (triangularTorusSurfaceSpin 0 0) weight ^ 2 := by
  exact surface_kacWard_original_of_localAngularSplit_shifted_cyclePhase
    (triangularTorusLocalAngularData L rho hrho)
    (triangularTorusSurfaceEdgeClass L)
    (triangularTorusSurfaceEdgeClass_diag L)
    (triangularTorusSurfaceSpin 0 0) weight hphase hisotropic



theorem triangularTorus_sector_sq_eq_det_of_localSplit
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho : Complex) (a b : Fin 2)
    (hrho : rho ^ 4 = Complex.I)
    (hphase : KWLocalAngularSplitShiftedCyclePhase
      (triangularTorusLocalAngularData L rho hrho)
      (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L))
      (triangularTorusSurfaceSpin 0 0))
    (hisotropic : SurfaceDisjointCycleIsotropic
      (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
        (triangularTorusLocalPortOrder L))
      (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L))) :
    triangularTorusWeightedSpinCharacterSum L
        (triangularTorusEdgeWeight L t1 t2 t3) a b ^ 2 =
      (1 - triangularTorusKWMatrix L t1 t2 t3 rho
        (StatMech.Onsager.ons_spinPhase L a)
        (StatMech.Onsager.ons_spinPhase L b)).det := by
  apply triangularTorus_sector_sq_eq_det_of_surface_base
  intro weight
  simpa [triangularTorusSurfaceSpin] using
    triangularTorus_native_det_square_of_localSplit
      L rho hrho hphase hisotropic weight



theorem triangularTorus_native_det_square
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (weight : Sym2 (ZMod L × ZMod L) -> Complex) :
    (1 - kwGraphTransition (triangularTorusGraph L) weight
      (triangularTorusGraphPhase L rho 1 1)).det =
      surfaceQuadraticEvenPolynomial (triangularTorusGraph L)
        (triangularTorusSurfaceEdgeClass L)
        (triangularTorusSurfaceSpin 0 0) weight ^ 2 := by
  exact triangularTorus_native_det_square_of_localSplit L rho hrho
    (triangularTorus_localAngularSplit_shiftedCyclePhase L rho hrho)
    (triangularTorus_localAngularSplit_disjointCycleIsotropic L) weight



theorem triangularTorus_sector_sq_eq_det
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho : Complex) (a b : Fin 2)
    (hrho : rho ^ 4 = Complex.I) :
    triangularTorusWeightedSpinCharacterSum L
        (triangularTorusEdgeWeight L t1 t2 t3) a b ^ 2 =
      (1 - triangularTorusKWMatrix L t1 t2 t3 rho
        (StatMech.Onsager.ons_spinPhase L a)
        (StatMech.Onsager.ons_spinPhase L b)).det := by
  exact triangularTorus_sector_sq_eq_det_of_localSplit L t1 t2 t3 rho a b
    hrho (triangularTorus_localAngularSplit_shiftedCyclePhase L rho hrho)
    (triangularTorus_localAngularSplit_disjointCycleIsotropic L)

end StatMech.FrontierA
