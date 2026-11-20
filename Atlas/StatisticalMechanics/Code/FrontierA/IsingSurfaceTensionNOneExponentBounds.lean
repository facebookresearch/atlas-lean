/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionNOneCoefficientSemantics









namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

private theorem spinCode_cases_lower (s k : Nat) :
    spinCode s k = 1 ∨ spinCode s k = -1 := by
  unfold spinCode
  split <;> simp

private theorem spinCode_mul_ge_neg_one (s t k : Nat) :
    -1 ≤ spinCode s k * spinCode t k := by
  rcases spinCode_cases_lower s k with hs | hs <;>
    rcases spinCode_cases_lower t k with ht | ht <;> simp [hs, ht]

theorem layerDotInt_ge_neg_nine (s t : Nat) : -9 ≤ layerDotInt s t := by
  unfold layerDotInt
  have h0 := spinCode_mul_ge_neg_one s t 0
  have h1 := spinCode_mul_ge_neg_one s t 1
  have h2 := spinCode_mul_ge_neg_one s t 2
  have h3 := spinCode_mul_ge_neg_one s t 3
  have h4 := spinCode_mul_ge_neg_one s t 4
  have h5 := spinCode_mul_ge_neg_one s t 5
  have h6 := spinCode_mul_ge_neg_one s t 6
  have h7 := spinCode_mul_ge_neg_one s t 7
  have h8 := spinCode_mul_ge_neg_one s t 8
  omega

set_option maxRecDepth 10000 in
theorem layerLateralInt_ge_neg_sixteen :
    ∀ s : Fin 512, -16 ≤ layerLateralInt s := by
  decide

set_option maxRecDepth 10000 in
theorem layerEndpointInt_ge_neg_seventeen :
    ∀ q : Fin 512, -17 ≤ layerLateralInt q + layerFaceInt q := by
  decide

theorem layerLateral_halfShift_nonneg (s : Fin 512) :
    0 ≤ halfShift (layerLateralInt s) 16 := by
  have h := layerLateralInt_ge_neg_sixteen s
  unfold halfShift
  omega

theorem layerEndpoint_halfShift_nonneg (q : Fin 512) :
    0 ≤ halfShift (layerLateralInt q + layerFaceInt q) 17 := by
  have h := layerEndpointInt_ge_neg_seventeen q
  unfold halfShift
  omega

theorem layerSeam_halfShift_nonneg (s q : Fin 512) :
    0 ≤ halfShift (layerDotInt s q) 9 := by
  have h := layerDotInt_ge_neg_nine s q
  unfold halfShift
  omega

theorem layerMiddle_halfShift_nonneg (s v : Fin 512) :
    0 ≤ halfShift
      (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26 := by
  have hd := layerDotInt_ge_neg_nine s v
  have he := layerEndpointInt_ge_neg_seventeen v
  unfold halfShift
  omega

set_option maxRecDepth 10000 in
theorem BiPoly.eval_rawMomentPoly_eq_list_stateSum
    (X Y : Real) (hX : X ≠ 0) :
    rawMomentPoly.eval X Y =
      ((List.range 512).map fun s =>
        X ^ halfShift (layerLateralInt s) 16 *
          ((List.range 512).map fun v =>
            X ^ halfShift
              (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26).sum *
          ((List.range 512).map fun q =>
            X ^ halfShift (layerLateralInt q + layerFaceInt q) 17 *
              Y ^ halfShift (layerDotInt s q) 9).sum).sum := by
  rw [BiPoly.eval_rawMomentPoly,
    weightedListEval_rawMomentCoefficientList_stateSum X Y hX]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  let sFin : Fin 512 := ⟨s, List.mem_range.mp hs⟩
  rw [Int.toNat_of_nonneg (layerLateral_halfShift_nonneg sFin)]
  apply congrArg₂
    (fun vSum qSum =>
      X ^ halfShift (layerLateralInt s) 16 * vSum * qSum)
  · apply congrArg List.sum
    apply List.map_congr_left
    intro v hv
    let vFin : Fin 512 := ⟨v, List.mem_range.mp hv⟩
    rw [Int.toNat_of_nonneg (layerMiddle_halfShift_nonneg sFin vFin)]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    let qFin : Fin 512 := ⟨q, List.mem_range.mp hq⟩
    rw [Int.toNat_of_nonneg (layerEndpoint_halfShift_nonneg qFin),
      Int.toNat_of_nonneg (layerSeam_halfShift_nonneg sFin qFin)]

private theorem list_range_sum_eq_finset_range_sum
    (f : Nat -> Real) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem BiPoly.eval_rawMomentPoly_eq_fin_stateSum
    (X Y : Real) (hX : X ≠ 0) :
    rawMomentPoly.eval X Y =
      ∑ s : Fin 512,
        X ^ halfShift (layerLateralInt s) 16 *
          (∑ v : Fin 512,
            X ^ halfShift
              (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26) *
          (∑ q : Fin 512,
            X ^ halfShift (layerLateralInt q + layerFaceInt q) 17 *
              Y ^ halfShift (layerDotInt s q) 9) := by
  rw [BiPoly.eval_rawMomentPoly_eq_list_stateSum X Y hX,
    list_range_sum_eq_finset_range_sum]
  exact (Fin.sum_univ_eq_sum_range
    (fun s : Nat =>
      X ^ halfShift (layerLateralInt s) 16 *
        ((List.range 512).map fun v =>
          X ^ halfShift
            (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26).sum *
        ((List.range 512).map fun q =>
          X ^ halfShift (layerLateralInt q + layerFaceInt q) 17 *
            Y ^ halfShift (layerDotInt s q) 9).sum) 512).symm.trans (by
      apply Finset.sum_congr rfl
      intro s hs
      apply congrArg₂
        (fun vSum qSum =>
          X ^ halfShift (layerLateralInt s) 16 * vSum * qSum)
      · rw [list_range_sum_eq_finset_range_sum]
        exact (Fin.sum_univ_eq_sum_range
          (fun v : Nat => X ^ halfShift
            (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26)
          512).symm
      · rw [list_range_sum_eq_finset_range_sum]
        exact (Fin.sum_univ_eq_sum_range
          (fun q : Nat =>
            X ^ halfShift (layerLateralInt q + layerFaceInt q) 17 *
              Y ^ halfShift (layerDotInt s q) 9) 512).symm)

end StatMech.FrontierA.NOneSymmetricMeanCertificate
