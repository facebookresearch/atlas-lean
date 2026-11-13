/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusSurfaceTwist
import Code.FrontierA.SurfaceKacWardShiftedBase









namespace StatMech.FrontierA

open StatMech.Onsager




theorem triangularTorus_sector_sq_eq_det_of_surface_base
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho : Complex) (a b : Fin 2)
    (hbase : ∀ w : Sym2 (ZMod L × ZMod L) → Complex,
      (1 - kwGraphTransition (triangularTorusGraph L) w
        (triangularTorusGraphPhase L rho 1 1)).det =
        surfaceQuadraticEvenPolynomial (triangularTorusGraph L)
          (triangularTorusSurfaceEdgeClass L)
          ((fun _ => (1 : Fin 2)), (fun _ => (1 : Fin 2))) w ^ 2) :
    triangularTorusWeightedSpinCharacterSum L
        (triangularTorusEdgeWeight L t1 t2 t3) a b ^ 2 =
      (1 - triangularTorusKWMatrix L t1 t2 t3 rho
        (ons_spinPhase L a) (ons_spinPhase L b)).det := by
  let lambda : SurfaceSpinStructure 1 :=
    ((fun _ => (1 : Fin 2)), (fun _ => (1 : Fin 2)))
  let mu : SurfaceSpinStructure 1 := ((fun _ => a), (fun _ => b))
  let weight := triangularTorusEdgeWeight L t1 t2 t3
  have hspin : lambda + mu = triangularTorusSurfaceSpin a b := by
    apply Prod.ext <;> funext i <;>
      simp [lambda, mu, triangularTorusSurfaceSpin]
  symm
  calc
    (1 - triangularTorusKWMatrix L t1 t2 t3 rho
        (ons_spinPhase L a) (ons_spinPhase L b)).det =
        (1 - triangularTorusSeamKWMatrix L t1 t2 t3 rho a b).det :=
      det_one_sub_triangularTorusKWMatrix_spin_eq_seam L t1 t2 t3 rho a b
    _ = (1 - surfaceTwistedKacWardMatrix (triangularTorusGraph L)
          (triangularTorusGraphPhase L rho 1 1)
          (triangularTorusSurfaceEdgeClass L) mu weight).det := by
      exact det_one_sub_triangularTorusSeamKWMatrix_eq_surfaceTwisted
        L t1 t2 t3 rho a b
    _ = surfaceQuadraticEvenPolynomial (triangularTorusGraph L)
          (triangularTorusSurfaceEdgeClass L) (lambda + mu) weight ^ 2 := by
      exact surface_twisted_kacWard_det_square_of_shifted_base
        (triangularTorusGraph L) (triangularTorusGraphPhase L rho 1 1)
        (triangularTorusSurfaceEdgeClass L) lambda hbase mu weight
    _ = surfaceQuadraticEvenPolynomial (triangularTorusGraph L)
          (triangularTorusSurfaceEdgeClass L)
          (triangularTorusSurfaceSpin a b) weight ^ 2 := by rw [hspin]
    _ = triangularTorusWeightedSpinCharacterSum L weight a b ^ 2 := by
      rw [triangularTorus_surfaceQuadraticEvenPolynomial_eq]

end StatMech.FrontierA
