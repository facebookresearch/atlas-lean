/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareGridConsistency









namespace StatMech.Universality

open Set

noncomputable section




theorem taylorWithinEval_three_eq_cubic_of_contDiffAt
    (g : Real -> Real) (s : Real) (hs : s ≠ 0)
    (hg0 : ContDiffAt Real 4 g 0) :
    taylorWithinEval g 3 (uIcc 0 s) 0 s = cubicTaylorPolynomial g s := by
  have hu : UniqueDiffOn Real (uIcc 0 s) :=
    uniqueDiffOn_Icc (by grind [uIcc])
  have hzero : (0 : Real) ∈ uIcc 0 s := left_mem_uIcc
  have hiter (j : Nat) (hj : j <= 4) :
      iteratedDerivWithin j g (uIcc 0 s) 0 = iteratedDeriv j g 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hg0.of_le (by exact_mod_cast hj)) hzero
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ, hiter, cubicTaylorPolynomial]
  ring



theorem cubicTaylor_remainder_le_of_contDiffOn
    (g : Real -> Real) (s M : Real) (hs : s ≠ 0)
    (hg0 : ContDiffAt Real 4 g 0)
    (hg : ContDiffOn Real 4 g (uIcc 0 s))
    (hM : forall t, t ∈ uIcc 0 s -> |iteratedDeriv 4 g t| <= M) :
    |g s - cubicTaylorPolynomial g s| <= M * |s| ^ 4 / 24 := by
  obtain ⟨t, ht, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (x := s) (x₀ := 0) hs.symm hg (n := 3)
  rw [<- taylorWithinEval_three_eq_cubic_of_contDiffAt g s hs hg0, hrem]
  rw [abs_div, abs_mul, abs_pow]
  norm_num
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (hM t (Ioo_subset_Icc_self ht)) (pow_nonneg (abs_nonneg s) 4))
    (by norm_num)


structure CenteredFourthOrderSegmentData
    (g : Real -> Real) (h M : Real) : Prop where
  atZero : ContDiffAt Real 4 g 0
  positive : ContDiffOn Real 4 g (uIcc 0 h)
  negative : ContDiffOn Real 4 g (uIcc 0 (-h))
  fourthPositive : forall t, t ∈ uIcc 0 h ->
    |iteratedDeriv 4 g t| <= M
  fourthNegative : forall t, t ∈ uIcc 0 (-h) ->
    |iteratedDeriv 4 g t| <= M



theorem CenteredFourthOrderSegmentData.ofContDiffOn
    {g : Real -> Real} {h M : Real} {U : Set Real}
    (hU : IsOpen U) (hzero : 0 ∈ U)
    (hpositive : uIcc 0 h ⊆ U)
    (hnegative : uIcc 0 (-h) ⊆ U)
    (hg : ContDiffOn Real 4 g U)
    (hM : forall t, t ∈ U -> |iteratedDeriv 4 g t| <= M) :
    CenteredFourthOrderSegmentData g h M where
  atZero := hg.contDiffAt (hU.mem_nhds hzero)
  positive := hg.mono hpositive
  negative := hg.mono hnegative
  fourthPositive t ht := hM t (hpositive ht)
  fourthNegative t ht := hM t (hnegative ht)



theorem centralSecondDifference_remainder_le_of_segmentData
    (g : Real -> Real) (h M : Real)
    (H : CenteredFourthOrderSegmentData g h M) :
    |(g h + g (-h) - 2 * g 0) - iteratedDeriv 2 g 0 * h ^ 2| <=
      M * |h| ^ 4 / 12 := by
  by_cases hh : h = 0
  · simp [hh]
    ring
  have hpos := cubicTaylor_remainder_le_of_contDiffOn
    g h M hh H.atZero H.positive H.fourthPositive
  have hneg := cubicTaylor_remainder_le_of_contDiffOn
    g (-h) M (neg_ne_zero.mpr hh) H.atZero H.negative H.fourthNegative
  have hid :
      (g h + g (-h) - 2 * g 0) - iteratedDeriv 2 g 0 * h ^ 2 =
        (g h - cubicTaylorPolynomial g h) +
          (g (-h) - cubicTaylorPolynomial g (-h)) := by
    unfold cubicTaylorPolynomial
    ring
  rw [hid]
  calc
    |(g h - cubicTaylorPolynomial g h) +
        (g (-h) - cubicTaylorPolynomial g (-h))| <=
      |g h - cubicTaylorPolynomial g h| +
        |g (-h) - cubicTaylorPolynomial g (-h)| := abs_add_le _ _
    _ <= M * |h| ^ 4 / 24 + M * |-h| ^ 4 / 24 :=
      add_le_add hpos hneg
    _ = M * |h| ^ 4 / 12 := by rw [abs_neg]; ring



theorem harmonicDirectionalFourNeighborStencil_le_of_segmentData
    (gOne gTwo : Real -> Real) (h MOne MTwo : Real)
    (HOne : CenteredFourthOrderSegmentData gOne h MOne)
    (HTwo : CenteredFourthOrderSegmentData gTwo h MTwo)
    (hharmonic : iteratedDeriv 2 gOne 0 + iteratedDeriv 2 gTwo 0 = 0) :
    |directionalFourNeighborStencil gOne gTwo h| <=
      (MOne + MTwo) * |h| ^ 4 / 12 := by
  have hOne := centralSecondDifference_remainder_le_of_segmentData
    gOne h MOne HOne
  have hTwo := centralSecondDifference_remainder_le_of_segmentData
    gTwo h MTwo HTwo
  have hid : directionalFourNeighborStencil gOne gTwo h =
      ((gOne h + gOne (-h) - 2 * gOne 0) -
        iteratedDeriv 2 gOne 0 * h ^ 2) +
      ((gTwo h + gTwo (-h) - 2 * gTwo 0) -
        iteratedDeriv 2 gTwo 0 * h ^ 2) := by
    unfold directionalFourNeighborStencil
    nlinarith
  rw [hid]
  calc
    |_ + _| <=
        |(gOne h + gOne (-h) - 2 * gOne 0) -
          iteratedDeriv 2 gOne 0 * h ^ 2| +
        |(gTwo h + gTwo (-h) - 2 * gTwo 0) -
          iteratedDeriv 2 gTwo 0 * h ^ 2| := abs_add_le _ _
    _ <= MOne * |h| ^ 4 / 12 + MTwo * |h| ^ 4 / 12 :=
      add_le_add hOne hTwo
    _ = (MOne + MTwo) * |h| ^ 4 / 12 := by ring



theorem complexDirectionalFourNeighborStencil_le_of_segmentData
    (f : Complex -> Real) (z vOne vTwo : Complex)
    (h MOne MTwo : Real)
    (HOne : CenteredFourthOrderSegmentData
      (fun t : Real => f (z + (t : Complex) * vOne)) h MOne)
    (HTwo : CenteredFourthOrderSegmentData
      (fun t : Real => f (z + (t : Complex) * vTwo)) h MTwo)
    (hharmonic : iteratedDeriv 2
        (fun t : Real => f (z + (t : Complex) * vOne)) 0 +
      iteratedDeriv 2
        (fun t : Real => f (z + (t : Complex) * vTwo)) 0 = 0) :
    |complexDirectionalFourNeighborStencil f z vOne vTwo h| <=
      (MOne + MTwo) * |h| ^ 4 / 12 := by
  rw [show complexDirectionalFourNeighborStencil f z vOne vTwo h =
      directionalFourNeighborStencil
        (fun t : Real => f (z + (t : Complex) * vOne))
        (fun t : Real => f (z + (t : Complex) * vTwo)) h by
    unfold complexDirectionalFourNeighborStencil
      directionalFourNeighborStencil
    push_cast
    simp only [add_zero, zero_mul, sub_eq_add_neg]
    ring]
  exact harmonicDirectionalFourNeighborStencil_le_of_segmentData
    (fun t : Real => f (z + (t : Complex) * vOne))
    (fun t : Real => f (z + (t : Complex) * vTwo))
    h MOne MTwo HOne HTwo hharmonic

end

end StatMech.Universality
