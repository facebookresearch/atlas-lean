/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopRectangularEmbedding
import Code.Onsager.SignedLoopThermodynamicGeneral





open MeasureTheory Filter Topology

namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierB

noncomputable section



theorem ons_canonicalRectDualPathRatio_tendsto_freeState
    (beta : Real) (hbeta : 0 < beta)
    (path : ∀ n, ons_RectDualPath (2 * n) (2 * n))
    (a b : Site 2)
    (hsource : ∀ᶠ n in atTop,
      ((ons_box2EquivRect n).symm (path n).source).1 = a)
    (htarget : ∀ᶠ n in atTop,
      ((ons_box2EquivRect n).symm (path n).target).1 = b) :
    Tendsto (fun n => ons_rectDualPathRatio
        (ons_rectDualStraightLineEmbedding (2 * n) (2 * n)) (path n) beta)
      atTop
      (nhds ((((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) ^ 2)) := by
  exact ons_rectDualPathRatio_tendsto_freeState beta hbeta
    (fun n => ons_rectDualStraightLineEmbedding (2 * n) (2 * n))
    path a b hsource htarget



theorem ons_canonicalRectDualPathCriticalRatio_tendsto_freeState
    (path : ∀ n, ons_RectDualPath (2 * n) (2 * n))
    (a b : Site 2)
    (hsource : ∀ᶠ n in atTop,
      ((ons_box2EquivRect n).symm (path n).source).1 = a)
    (htarget : ∀ᶠ n in atTop,
      ((ons_box2EquivRect n).symm (path n).target).1 = b) :
    Tendsto (fun n => ons_rectDualPathCriticalRatio
        (ons_rectDualStraightLineEmbedding (2 * n) (2 * n)) (path n))
      atTop
      (nhds ((((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 ons_betaC 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) ^ 2)) := by
  exact ons_rectDualPathCriticalRatio_tendsto_freeState
    (fun n => ons_rectDualStraightLineEmbedding (2 * n) (2 * n))
    path a b hsource htarget

end

end StatMech.Onsager
