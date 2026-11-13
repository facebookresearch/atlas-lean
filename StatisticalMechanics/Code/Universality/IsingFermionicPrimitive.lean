/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareSwitching












open Complex

namespace StatMech.Universality

noncomputable section



def IsingSquareSHolomorphicQuad (A B C D : Complex) : Prop :=
  A - B = (starRingEnd Complex) A - (starRingEnd Complex) B ∧
  C - D = (starRingEnd Complex) D - (starRingEnd Complex) C ∧
  A - C = Complex.I * (D - B)



def isingPrimitiveSquareCombination (A B C D : Complex) : Complex :=
  A ^ 2 + Complex.I * B ^ 2 - C ^ 2 - Complex.I * D ^ 2


def isingPrimalPrimitiveLaplacian (A B C D : Complex) : Real :=
  (((1 + Complex.I) / 2) *
    isingPrimitiveSquareCombination A B C D).im


def isingDualPrimitiveLaplacian (A B C D : Complex) : Real :=
  -isingPrimalPrimitiveLaplacian A B C D



noncomputable def isingPrimalProjectionDivergence
    (north east south west : Complex) : Real :=
  Complex.normSq (isingProj (-Complex.I) north) -
      Complex.normSq (isingProj (-1) north) +
    Complex.normSq (isingProj 1 east) -
      Complex.normSq (isingProj (-Complex.I) east) +
    Complex.normSq (isingProj Complex.I south) -
      Complex.normSq (isingProj 1 south) +
    Complex.normSq (isingProj (-1) west) -
      Complex.normSq (isingProj Complex.I west)



noncomputable def isingPrimalProjectionDivergenceWithoutSouth
    (north east west : Complex) : Real :=
  Complex.normSq (isingProj (-Complex.I) north) -
      Complex.normSq (isingProj (-1) north) +
    Complex.normSq (isingProj 1 east) -
      Complex.normSq (isingProj (-Complex.I) east) +
    Complex.normSq (isingProj (-1) west) -
      Complex.normSq (isingProj Complex.I west)



theorem isingPrimalProjectionDivergenceWithoutSouth_add
    (north east south west : Complex) :
    isingPrimalProjectionDivergenceWithoutSouth north east west +
        (Complex.normSq (isingProj Complex.I south) -
          Complex.normSq (isingProj 1 south)) =
      isingPrimalProjectionDivergence north east south west := by
  unfold isingPrimalProjectionDivergenceWithoutSouth
    isingPrimalProjectionDivergence
  ring


theorem isingPrimalPrimitiveLaplacian_eq_projectionDivergence
    (north east south west : Complex) :
    isingPrimalPrimitiveLaplacian north east south west =
      isingPrimalProjectionDivergence north east south west := by
  unfold isingPrimalPrimitiveLaplacian isingPrimitiveSquareCombination
  unfold isingPrimalProjectionDivergence isingProj
  simp only [Complex.normSq_apply, map_neg, map_one, map_mul,
    Complex.conj_I, Complex.one_re, Complex.one_im, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, pow_two]
  norm_num
  ring



theorem isingSquareSHolomorphicQuad_of_projection_cycle
    (north east south west : Complex)
    (hNE : isingProj 1 north = isingProj 1 east)
    (hES : isingProj Complex.I east = isingProj Complex.I south)
    (hSW : isingProj (-1) south = isingProj (-1) west)
    (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north) :
    IsingSquareSHolomorphicQuad south west north east := by
  have hNEre := congrArg Complex.re hNE
  have hESre := congrArg Complex.re hES
  have hSWim := congrArg Complex.im hSW
  have hWNre := congrArg Complex.re hWN
  simp only [isingProj, map_one, map_neg, map_mul, Complex.conj_I,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    at hNEre hESre hSWim hWNre
  norm_num at hNEre hESre hSWim hWNre
  unfold IsingSquareSHolomorphicQuad
  constructor
  · apply Complex.ext
    · simp
    · simp
      linarith
  constructor
  · apply Complex.ext
    · simp
      linarith
    · simp
      ring
  · apply Complex.ext
    · simp
      linarith
    · simp
      linarith



def isingPrimitiveIncrement (F : Complex) : Real := Complex.normSq F



theorem isingProj_normSq_add_neg (e f : Complex)
    (he : Complex.normSq e = 1) :
    Complex.normSq (isingProj e f) +
        Complex.normSq (isingProj (-e) f) = Complex.normSq f := by
  simp only [isingProj, map_neg, map_sub, Complex.normSq_div,
    Complex.normSq_add, Complex.normSq_sub, Complex.normSq_mul,
    Complex.normSq_conj, Complex.normSq_neg, he, one_mul]
  norm_num [Complex.normSq_apply]
  ring




theorem isingProj_normSq_le_two_mul_diagonal_variation (f : Complex) :
    Complex.normSq f ≤
      2 *
        (|Complex.normSq (isingProj Complex.I f) -
              Complex.normSq (isingProj (-1) f)| +
          |Complex.normSq (isingProj 1 f) -
              Complex.normSq (isingProj Complex.I f)|) := by
  let a : Real := Complex.normSq (isingProj Complex.I f) -
    Complex.normSq (isingProj (-1) f)
  let b : Real := Complex.normSq (isingProj 1 f) -
    Complex.normSq (isingProj Complex.I f)
  have hsq : Complex.normSq f ^ 2 = 2 * (a ^ 2 + b ^ 2) := by
    dsimp [a, b]
    simp only [isingProj, map_neg, map_one, Complex.conj_I,
      Complex.normSq_mul, Complex.normSq_add, Complex.normSq_conj,
      Complex.normSq_neg]
    norm_num [Complex.normSq_apply]
    ring
  have hab : a ^ 2 + b ^ 2 ≤ (|a| + |b|) ^ 2 := by
    rw [add_sq, sq_abs, sq_abs]
    nlinarith [mul_nonneg (abs_nonneg a) (abs_nonneg b)]
  have hsquare : Complex.normSq f ^ 2 ≤ (2 * (|a| + |b|)) ^ 2 := by
    nlinarith [sq_nonneg (|a| + |b|)]
  have hnorm : 0 ≤ Complex.normSq f := Complex.normSq_nonneg f
  have habs : 0 ≤ 2 * (|a| + |b|) := by positivity
  change Complex.normSq f ≤ 2 * (|a| + |b|)
  nlinarith [sq_nonneg (Complex.normSq f + 2 * (|a| + |b|))]




theorem isingPrimitiveIncrement_local_closed
    (e u f : Complex) (he : Complex.normSq e = 1)
    (hu : Complex.normSq u = 1) :
    isingPrimitiveIncrement (isingProj e f) -
        isingPrimitiveIncrement (isingProj u f) +
      isingPrimitiveIncrement (isingProj (-e) f) -
        isingPrimitiveIncrement (isingProj (-u) f) = 0 := by
  have hePair := isingProj_normSq_add_neg e f he
  have huPair := isingProj_normSq_add_neg u f hu
  unfold isingPrimitiveIncrement at ⊢
  linarith


theorem isingPrimitiveSquareCombination_eq_normSq
    (A B C D : Complex) (h : IsingSquareSHolomorphicQuad A B C D) :
    isingPrimitiveSquareCombination A B C D =
      (1 + Complex.I) * (Complex.normSq (A - C) : Complex) := by
  rcases h with ⟨hAB, hCD, hCR⟩
  have hconj :
      (starRingEnd Complex) A - (starRingEnd Complex) C =
        -Complex.I *
          ((starRingEnd Complex) D - (starRingEnd Complex) B) := by
    have hc := congrArg (starRingEnd Complex) hCR
    simpa only [map_sub, map_mul, Complex.conj_I] using hc
  have hDB :
      (starRingEnd Complex) D - (starRingEnd Complex) B =
        Complex.I *
          ((starRingEnd Complex) A - (starRingEnd Complex) C) := by
    have hunit : Complex.I * (-Complex.I *
        ((starRingEnd Complex) D - (starRingEnd Complex) B)) =
        (starRingEnd Complex) D - (starRingEnd Complex) B := by
      calc
        Complex.I * (-Complex.I *
            ((starRingEnd Complex) D - (starRingEnd Complex) B)) =
          -(Complex.I * Complex.I) *
            ((starRingEnd Complex) D - (starRingEnd Complex) B) := by ring
        _ = (starRingEnd Complex) D - (starRingEnd Complex) B := by
          rw [Complex.I_mul_I]
          ring
    calc
      (starRingEnd Complex) D - (starRingEnd Complex) B =
          Complex.I * (-Complex.I *
            ((starRingEnd Complex) D - (starRingEnd Complex) B)) := hunit.symm
      _ = Complex.I *
          ((starRingEnd Complex) A - (starRingEnd Complex) C) := by
        rw [hconj]
  calc
    isingPrimitiveSquareCombination A B C D =
        (A - C) * (A + C) +
          Complex.I * (B - D) * (B + D) := by
      unfold isingPrimitiveSquareCombination
      ring
    _ = (A - C) * (A + C - B - D) := by
      rw [hCR]
      ring_nf
    _ = (A - C) *
        (((starRingEnd Complex) A - (starRingEnd Complex) B) +
          ((starRingEnd Complex) D - (starRingEnd Complex) C)) := by
      rw [← hAB, ← hCD]
      ring
    _ = (A - C) *
        (((starRingEnd Complex) A - (starRingEnd Complex) C) +
          ((starRingEnd Complex) D - (starRingEnd Complex) B)) := by
      ring
    _ = (A - C) *
        ((1 + Complex.I) *
          ((starRingEnd Complex) A - (starRingEnd Complex) C)) := by
      rw [hDB]
      ring
    _ = (1 + Complex.I) * (Complex.normSq (A - C) : Complex) := by
      rw [Complex.normSq_eq_conj_mul_self]
      simp only [map_sub, starRingEnd_apply]
      ring



theorem isingPrimalPrimitiveLaplacian_eq_normSq
    (A B C D : Complex) (h : IsingSquareSHolomorphicQuad A B C D) :
    isingPrimalPrimitiveLaplacian A B C D = Complex.normSq (A - C) := by
  rw [isingPrimalPrimitiveLaplacian,
    isingPrimitiveSquareCombination_eq_normSq A B C D h]
  simp [Complex.normSq_apply]
  ring

theorem isingPrimalPrimitiveLaplacian_nonneg
    (A B C D : Complex) (h : IsingSquareSHolomorphicQuad A B C D) :
    0 ≤ isingPrimalPrimitiveLaplacian A B C D := by
  rw [isingPrimalPrimitiveLaplacian_eq_normSq A B C D h]
  exact Complex.normSq_nonneg _



theorem isingPrimalPrimitiveLaplacian_rotate_two
    (A B C D : Complex) :
    isingPrimalPrimitiveLaplacian A B C D =
      -isingPrimalPrimitiveLaplacian C D A B := by
  have hcomb : isingPrimitiveSquareCombination C D A B =
      -isingPrimitiveSquareCombination A B C D := by
    unfold isingPrimitiveSquareCombination
    ring
  unfold isingPrimalPrimitiveLaplacian
  rw [hcomb]
  simp



theorem isingPrimalPrimitiveLaplacian_nonpos_of_rotated_quad
    (north east south west : Complex)
    (h : IsingSquareSHolomorphicQuad south west north east) :
    isingPrimalPrimitiveLaplacian north east south west ≤ 0 := by
  rw [isingPrimalPrimitiveLaplacian_rotate_two]
  exact neg_nonpos.mpr
    (isingPrimalPrimitiveLaplacian_nonneg south west north east h)




theorem isingPrimalProjectionDivergenceWithoutSouth_add_correction_nonpos
    (north east south west : Complex) (c g : Real)
    (hquad : IsingSquareSHolomorphicQuad south west north east)
    (hcorr : c * g =
      Complex.normSq (isingProj Complex.I south) -
        Complex.normSq (isingProj 1 south)) :
    isingPrimalProjectionDivergenceWithoutSouth north east west + c * g ≤ 0 := by
  rw [hcorr, isingPrimalProjectionDivergenceWithoutSouth_add,
    ← isingPrimalPrimitiveLaplacian_eq_projectionDivergence]
  exact isingPrimalPrimitiveLaplacian_nonpos_of_rotated_quad
    north east south west hquad


theorem isingDualPrimitiveLaplacian_eq_neg_normSq
    (A B C D : Complex) (h : IsingSquareSHolomorphicQuad A B C D) :
    isingDualPrimitiveLaplacian A B C D = -Complex.normSq (A - C) := by
  rw [isingDualPrimitiveLaplacian,
    isingPrimalPrimitiveLaplacian_eq_normSq A B C D h]

theorem isingDualPrimitiveLaplacian_nonpos
    (A B C D : Complex) (h : IsingSquareSHolomorphicQuad A B C D) :
    isingDualPrimitiveLaplacian A B C D ≤ 0 := by
  rw [isingDualPrimitiveLaplacian_eq_neg_normSq A B C D h]
  exact neg_nonpos.mpr (Complex.normSq_nonneg _)

end

end StatMech.Universality
