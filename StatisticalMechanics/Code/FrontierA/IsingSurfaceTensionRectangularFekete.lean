/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingRectangularDobrushin
import Code.FrontierA.IsingSurfaceTensionFeketeIdentification

open Filter Topology

namespace StatMech.FrontierA

open StatMech.Ising

noncomputable section



theorem rectangularDobrushinArray_hasRectangularAreaBound
    (J beta : Real) :
    HasRectangularAreaBound (rectangularDobrushinArray J beta) := by
  refine ⟨2 * |beta| * |J|, by positivity, ?_⟩
  intro m n
  exact rectangularDobrushinArray_le_area J beta m n




theorem rectangularDobrushinArray_square_and_iterated_tendsto
    {J beta : Real} (hJ : 0 <= J) (hbeta : 0 <= beta)
    (hsub : SeparatelySubadditive (rectangularDobrushinArray J beta)) :
    Tendsto (fun n : Nat =>
        rectangularSurfaceDensity (rectangularDobrushinArray J beta) n n)
        atTop (nhds (rectangularSurfaceRate
          (rectangularDobrushinArray J beta))) /\
      Tendsto (fun k : Nat => (hsub.1 k).lim / (k : Real))
        atTop (nhds (rectangularSurfaceRate
          (rectangularDobrushinArray J beta))) :=
  square_and_iterated_surfaceDensity_tendsto_rate
    (rectangularDobrushinArray_nonneg hJ hbeta) hsub
    (rectangularDobrushinArray_hasRectangularAreaBound J beta)

end

end StatMech.FrontierA
