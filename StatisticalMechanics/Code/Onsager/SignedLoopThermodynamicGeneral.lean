/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopThermodynamicLimit





open Finset SimpleGraph MeasureTheory Filter Topology

namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.FrontierB

noncomputable section



def ons_rectDualPathRatio {n : Nat}
    (embedding : KWStraightLineEmbedding
      (ons_rectDualGraph (2 * n) (2 * n)))
    (path : ons_RectDualPath (2 * n) (2 * n))
    (beta : Real) : Complex :=
  ((Real.tanh beta : Complex) ^
      (2 * (ons_rectDualPathDefect path).card) *
    ons_rectDualPathDefectKWDet embedding path (Real.tanh beta)) /
      ons_rectDualKWDet embedding (Real.tanh beta)




theorem ons_rectDualPathRatio_tendsto_freeState
    (beta : Real) (hbeta : 0 < beta)
    (embedding : ∀ n, KWStraightLineEmbedding
      (ons_rectDualGraph (2 * n) (2 * n)))
    (path : ∀ n, ons_RectDualPath (2 * n) (2 * n))
    (a b : Site 2)
    (hsource : ∀ᶠ n in atTop,
      ((ons_box2EquivRect n).symm (path n).source).1 = a)
    (htarget : ∀ᶠ n in atTop,
      ((ons_box2EquivRect n).symm (path n).target).1 = b) :
    Tendsto (fun n => ons_rectDualPathRatio (embedding n) (path n) beta)
      atTop
      (nhds ((((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) ^ 2)) := by
  let f : Nat → Real := fun n =>
    ∫ spin, spinProd {a, b} spin
      ∂(freeMeasure 2 n beta 0 : Measure (ConfigSpace (Site 2)))
  have hf : Tendsto f atTop
      (nhds (∫ spin, spinProd {a, b} spin
        ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2))))) := by
    simpa only [f] using
      integral_freeMeasure_spinProd_tendsto_freeState
        2 beta hbeta.le ({a, b} : Finset (Site 2))
  have hfComplex : Tendsto (fun n => (f n : Complex)) atTop
      (nhds (((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex)) := by
    simpa only [Function.comp_apply] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hf
  apply (hfComplex.pow 2).congr'
  filter_upwards [hsource, htarget] with n hs ht
  rw [show ons_rectDualPathRatio (embedding n) (path n) beta =
      (isingExpectation (ons_rectDualGraph (2 * n) (2 * n)) beta 0
        (fun spin => Ising.spin spin (path n).source *
          Ising.spin spin (path n).target) : Complex) ^ 2 by
    symm
    exact coe_ons_rectDualPath_finiteTwoPoint_sq_eq_kwDet_ratio
      (embedding n) (path n) hbeta]
  rw [show (isingExpectation (ons_rectDualGraph (2 * n) (2 * n))
      beta 0 (fun spin => Ising.spin spin (path n).source *
        Ising.spin spin (path n).target) : Complex) =
      (((∫ spin, spinProd
        {((ons_box2EquivRect n).symm (path n).source).1,
          ((ons_box2EquivRect n).symm (path n).target).1} spin
        ∂(freeMeasure 2 n beta 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) by
    exact_mod_cast ons_rectDualPath_twoPoint_eq_freeMeasure
      n beta (path n)]
  simp only [hs, ht, f]

end

end StatMech.Onsager
