/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareBoundaryCompactAverage
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Hull











namespace StatMech.Universality

open Set Metric

noncomputable section



theorem fkIsingExpandingBoundarySquare_carrier_isCompact (k : Nat) :
    IsCompact
      (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) := by
  change IsCompact {z : Complex | ∃ a : FKIsingSquareWiredCarrier
      (fkIsingExpandingSquareSide k),
    dist z (fkIsingSquareWiredPerturbedCarrierPosition
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) a) ≤
        fkIsingExpandingSquareMesh k}
  rw [show {z : Complex | ∃ a : FKIsingSquareWiredCarrier
      (fkIsingExpandingSquareSide k),
    dist z (fkIsingSquareWiredPerturbedCarrierPosition
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) a) ≤
        fkIsingExpandingSquareMesh k} =
      ⋃ a : FKIsingSquareWiredCarrier (fkIsingExpandingSquareSide k),
        closedBall (fkIsingSquareWiredPerturbedCarrierPosition
          (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
          (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) a)
          (fkIsingExpandingSquareMesh k) by
      ext z
      simp [mem_closedBall]]
  exact isCompact_iUnion fun _ ↦ isCompact_closedBall _ _




theorem exists_fkIsingExpandingBoundarySquare_scaleDerivativeBound :
    ∃ C : Nat → NNReal, ∀ k z,
      z ∈ convexHull Real
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) →
      ‖deriv
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
          k) z‖₊ ≤ C k := by
  choose R hR using fun k ↦
    (fkIsingExpandingBoundarySquare_carrier_isCompact k).isBounded.subset_closedBall
      (0 : Complex)
  let F : Nat → Complex → Complex := fun k ↦
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k
  have hcontinuous : ∀ k, Continuous (fun z ↦ ‖deriv (F k) z‖₊) := by
    intro k
    exact continuous_nnnorm.comp
      ((fkIsingExpandingBoundarySquare_normalizedInterpolant_differentiable k).contDiff
        (n := 1)).continuous_deriv_one
  have hHull : ∀ k, convexHull Real
      (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) ⊆
        closedBall 0 (R k) := by
    intro k
    exact convexHull_min (hR k) (convex_closedBall 0 (R k))
  have hbdd : ∀ k, BddAbove
      ((fun z ↦ ‖deriv (F k) z‖₊) '' closedBall 0 (R k)) := by
    intro k
    exact (isCompact_closedBall 0 (R k)).bddAbove_image
      (hcontinuous k).continuousOn
  choose C hC using fun k ↦ bddAbove_def.mp (hbdd k)
  refine ⟨C, ?_⟩
  intro k z hz
  apply hC k
  exact ⟨z, hHull k hz, rfl⟩



theorem exists_fkIsingExpandingBoundarySquare_scaleLipschitzBound :
    ∃ C : Nat → NNReal, ∀ k,
      LipschitzOnWith (C k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) := by
  obtain ⟨C, hC⟩ := exists_fkIsingExpandingBoundarySquare_scaleDerivativeBound
  refine ⟨C, ?_⟩
  intro k
  let carrier :=
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k
  exact (convex_convexHull Real carrier).lipschitzOnWith_of_nnnorm_deriv_le
      (fun z _hz ↦
        fkIsingExpandingBoundarySquare_normalizedInterpolant_differentiable k z)
      (fun z hz ↦ hC k z hz) |>.mono
        (subset_convexHull Real carrier)




def lagrangeShrinkingTwoPointPosition (k : Nat) : Fin 2 → Complex :=
  ![0, ((k + 1 : Nat) : Complex)⁻¹]


def lagrangeShrinkingTwoPointValue : Fin 2 → Complex := ![0, 1]

theorem lagrangeShrinkingTwoPointPosition_injective (k : Nat) :
    Function.Injective (lagrangeShrinkingTwoPointPosition k) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    have hk : ((k : Complex) + 1) ≠ 0 := by
      exact_mod_cast (show k + 1 ≠ 0 by omega)
    apply hk
    simpa [lagrangeShrinkingTwoPointPosition] using hij.symm
  · exfalso
    have hk : ((k : Complex) + 1) ≠ 0 := by
      exact_mod_cast (show k + 1 ≠ 0 by omega)
    apply hk
    simpa [lagrangeShrinkingTwoPointPosition] using hij
  · rfl

theorem lagrangeShrinkingTwoPointValue_norm_le_one (i : Fin 2) :
    ‖lagrangeShrinkingTwoPointValue i‖ ≤ 1 := by
  fin_cases i <;> simp [lagrangeShrinkingTwoPointValue]

theorem lagrangeShrinkingTwoPointPosition_dist (k : Nat) :
    dist (lagrangeShrinkingTwoPointPosition k 0)
        (lagrangeShrinkingTwoPointPosition k 1) =
      1 / (k + 1 : Nat) := by
  change dist (0 : Complex) (((k + 1 : Nat) : Complex)⁻¹) =
    1 / ((k + 1 : Nat) : Real)
  rw [dist_eq_norm, zero_sub, norm_neg, norm_inv, Complex.norm_natCast]
  simp [div_eq_mul_inv]



theorem lagrangeShrinkingTwoPointInterpolant_eq (k : Nat) (z : Complex) :
    finiteLagrangeInterpolant (lagrangeShrinkingTwoPointPosition k)
      lagrangeShrinkingTwoPointValue z =
        ((k + 1 : Nat) : Complex) * z := by
  have herase0 : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have herase1 : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  rw [finiteLagrangeInterpolant, Fin.sum_univ_two]
  simp only [finiteLagrangeBasis, herase0, herase1]
  simp [lagrangeShrinkingTwoPointPosition, lagrangeShrinkingTwoPointValue]
  field_simp

theorem lagrangeShrinkingTwoPointInterpolant_deriv (k : Nat) (z : Complex) :
    deriv (finiteLagrangeInterpolant (lagrangeShrinkingTwoPointPosition k)
      lagrangeShrinkingTwoPointValue) z =
        ((k + 1 : Nat) : Complex) := by
  have hfun : finiteLagrangeInterpolant (lagrangeShrinkingTwoPointPosition k)
      lagrangeShrinkingTwoPointValue =
        fun w : Complex ↦ ((k + 1 : Nat) : Complex) * w := by
    funext w
    exact lagrangeShrinkingTwoPointInterpolant_eq k w
  rw [hfun]
  simpa only [id_eq, mul_one] using
    ((hasDerivAt_id z).const_mul ((k + 1 : Nat) : Complex)).deriv

theorem lagrangeShrinkingTwoPointPosition_zero_mem_convexHull (k : Nat) :
    (0 : Complex) ∈
      convexHull Real (Set.range (lagrangeShrinkingTwoPointPosition k)) := by
  apply subset_convexHull Real
  exact ⟨0, by simp [lagrangeShrinkingTwoPointPosition]⟩




theorem lagrangeShrinkingTwoPoint_no_uniform_derivative_bound :
    ¬ ∃ C : NNReal, ∀ k z,
      z ∈ convexHull Real
        (Set.range (lagrangeShrinkingTwoPointPosition k)) →
      ‖deriv (finiteLagrangeInterpolant (lagrangeShrinkingTwoPointPosition k)
        lagrangeShrinkingTwoPointValue) z‖₊ ≤ C := by
  rintro ⟨C, hC⟩
  let k := Nat.ceil C + 1
  have hbound := hC k 0
    (lagrangeShrinkingTwoPointPosition_zero_mem_convexHull k)
  rw [lagrangeShrinkingTwoPointInterpolant_deriv] at hbound
  have hnorm : ‖((k + 1 : Nat) : Complex)‖₊ =
      ((k + 1 : Nat) : NNReal) := by
    apply NNReal.eq
    exact Complex.norm_natCast (k + 1)
  rw [hnorm] at hbound
  have hceil : (C : Real) ≤ Nat.ceil C := Nat.le_ceil C
  have hboundReal : ((k + 1 : Nat) : Real) ≤ (C : Real) := by
    exact_mod_cast hbound
  simp only [k, Nat.cast_add, Nat.cast_one] at hboundReal
  nlinarith






noncomputable def
    fkIsingExpandingBoundarySquare_holderInterpolation_of_deriv_bound
    (C : NNReal)
    (hderiv : ∀ k z,
      z ∈ convexHull Real
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) →
      ‖deriv
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
          k) z‖₊ ≤ C) :
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.HolderInterpolation := by
  refine
    { exponent := 1
      exponent_pos := zero_lt_one
      constant := C
      holder := ?_ }
  intro k
  let carrier :=
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k
  let hull := convexHull Real carrier
  let F :=
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k
  have hF : Differentiable Complex F :=
    fkIsingExpandingBoundarySquare_normalizedInterpolant_differentiable k
  have hLipHull : LipschitzOnWith C F hull :=
    (convex_convexHull Real carrier).lipschitzOnWith_of_nnnorm_deriv_le
      (fun z _hz ↦ hF z)
      (fun z hz ↦ hderiv k z hz)
  exact
    (hLipHull.mono (subset_convexHull Real carrier)).holderOnWith





noncomputable def
    fkIsingExpandingBoundarySquare_holderInterpolation_of_scale_deriv_bound
    (C : Nat → NNReal)
    (hderiv : ∀ k z,
      z ∈ convexHull Real
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) →
      ‖deriv
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
          k) z‖₊ ≤ C k)
    (hC : BddAbove (Set.range C)) :
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.HolderInterpolation := by
  let C₀ : NNReal := Classical.choose (bddAbove_def.mp hC)
  have hC₀ : ∀ y ∈ Set.range C, y ≤ C₀ :=
    Classical.choose_spec (bddAbove_def.mp hC)
  apply fkIsingExpandingBoundarySquare_holderInterpolation_of_deriv_bound C₀
  intro k z hz
  exact (hderiv k z hz).trans (hC₀ (C k) ⟨k, rfl⟩)






theorem fkIsingExpandingBoundarySquare_entireSquarePrimitive_deriv_medial
    (k : Nat)
    (e : fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k) :
    deriv (isingFermionicEntireSquarePrimitive
      (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k))
      (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding k e) =
        (@FKIsingDobrushinDomain.normalizedFermionicObservable
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.P k)
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k)
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.decEqM k)
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.dobrushin k)
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k) e) ^ 2 := by
  rw [(isingFermionicEntireSquarePrimitive_hasDerivAt
    (fkIsingExpandingBoundarySquare_normalizedInterpolant_differentiable k)
    (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding k e)).deriv]
  rw [fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant_medial]




theorem
    fkIsingExpandingBoundarySquare_scalingLimit_of_deriv_and_dense_primitiveIm
    (C : NNReal)
    (hderiv : forall k z,
      z ∈ convexHull Real
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) ->
      ‖deriv
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
          k) z‖₊ ≤ C)
    (target Phi : Complex -> Complex)
    (htarget : DifferentiableOn Complex target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (htarget_ne : target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2)
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (E : StatMech.FrontierA.CompactExhaustion
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hidentifyDense : forall
      (phi psi : Nat -> Nat) (f : Complex -> Complex),
      StrictMono phi -> StrictMono psi ->
      TendstoLocallyUniformlyOn
        (fun k =>
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
            (phi (psi k))) f Filter.atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ->
      exists (S : Set Complex) (C : Real), Dense S ∧
        Set.EqOn
          (fun z => (isingFermionicEntireSquarePrimitive f z).im)
          (fun z => (Phi z).im + C) S ∧
        f fkIsingExpandingBoundarySquareCaratheodoryApproximation.root =
          target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) :
    TendstoLocallyUniformlyOn
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
        target Filter.atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ∧
      TendstoLocallyUniformlyOn
        (deriv ∘
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant)
        (deriv target) Filter.atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
  exact
    fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_dense_primitiveIm
      (fkIsingExpandingBoundarySquare_holderInterpolation_of_deriv_bound
        C hderiv)
      target Phi htarget htarget_ne hPhi hPhideriv E hidentifyDense

end

end StatMech.Universality
