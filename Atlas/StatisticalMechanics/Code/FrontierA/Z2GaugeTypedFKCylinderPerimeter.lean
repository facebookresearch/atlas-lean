/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierA.Z2GaugeTypedFKCylinderGeometry

namespace StatMech.FrontierA

noncomputable section




theorem cubicalXYWilson_central_perimeterLower_of_l1_exponential
    (n : Nat)
    (K : CubicalPlaquette (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n) -> Real)
    (hK : forall p, 0 < K p)
    (decay : Real) (hdecay : 0 < decay)
    (hcorr : forall uv, uv ∈
        (cubicalLowerComplementInnerVertices (centralSquareSheetHeight n)).product
          (cubicalXYSheetUpperVertices (centralSquareSheetHeight n)) ->
      multibondIsingTwoPoint cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) uv.1 uv.2 <=
        Real.exp (-decay * (cubicalDualL1 uv.1 uv.2 : Real))) :
    Real.exp
        (-(gaugePerimeterPenalty (Real.exp (-decay)) *
              (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)) *
            centralSquareSide n) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence K
        (cubicalXYLoop (centralSquareSheetHeight n)) := by
  apply cubicalXYWilson_perimeterLower_of_lowerSlab_exponential
    (a := centralSquareSide n) (b := centralSquareSide n)
    (c := centralSquareSide n + centralSquareSide n)
    (by simp [centralSquareSide]) (by simp [centralSquareSide])
    (by simp [centralSquareSide])
    (centralSquareSheetHeight n)
    (by simp [centralSquareSheetHeight, centralSquareSide])
    K hK decay
    (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)
    (centralSquareSide n) hdecay
    (fun uv => (cubicalDualL1 uv.1 uv.2 : Real))
  · exact cubicalLowerSlab_central_l1_ge_one n
  · exact hcorr
  · exact cubicalLowerSlab_central_exp_l1_sum_le decay hdecay n

end

end StatMech.FrontierA
