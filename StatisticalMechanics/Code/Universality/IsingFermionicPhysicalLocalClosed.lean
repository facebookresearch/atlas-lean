/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalPrimitiveBridge
import Code.Universality.IsingFermionicSquareWiredDoubleVisitPortGeometry











namespace StatMech.Universality

open Complex
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

private theorem complex_exp_pi_div_two_mul_I :
    Complex.exp ((Real.pi / 2 : Real) * Complex.I) = Complex.I := by
  convert Complex.exp_pi_div_two_mul_I using 2 <;> push_cast <;> ring

private theorem complex_exp_two_pi_mul_I :
    Complex.exp ((2 * Real.pi : Real) * Complex.I) = 1 := by
  calc
    Complex.exp ((2 * Real.pi : Real) * Complex.I) =
        Complex.exp ((Real.pi : Complex) * Complex.I) ^ 2 := by
      convert Complex.exp_nat_mul ((Real.pi : Complex) * Complex.I) 2 using 1 <;>
        push_cast <;> ring
    _ = 1 := by rw [Complex.exp_pi_mul_I]; norm_num

private theorem complex_exp_three_pi_mul_I :
    Complex.exp ((3 * Real.pi : Real) * Complex.I) = -1 := by
  calc
    Complex.exp ((3 * Real.pi : Real) * Complex.I) =
        Complex.exp ((Real.pi : Complex) * Complex.I) ^ 3 := by
      convert Complex.exp_nat_mul ((Real.pi : Complex) * Complex.I) 3 using 1 <;>
        push_cast <;> ring
    _ = -1 := by rw [Complex.exp_pi_mul_I]; norm_num

private theorem complex_exp_neg_pi_mul_I :
    Complex.exp (-(Real.pi : Complex) * Complex.I) = -1 := by
  rw [show -(Real.pi : Complex) * Complex.I =
      -((Real.pi : Complex) * Complex.I) by ring,
    Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

private theorem complex_exp_neg_pi_div_two_mul_I :
    Complex.exp (-(Real.pi / 2 : Real) * Complex.I) = -Complex.I := by
  rw [show -(Real.pi / 2 : Real) * Complex.I =
      -((Real.pi / 2 : Real) * Complex.I) by push_cast; ring,
    Complex.exp_neg, complex_exp_pi_div_two_mul_I]
  norm_num

private theorem complex_exp_neg_two_pi_mul_I :
    Complex.exp (-(2 * Real.pi : Real) * Complex.I) = 1 := by
  rw [show -(2 * Real.pi : Real) * Complex.I =
      -(((2 * Real.pi : Real) : Complex) * Complex.I) by push_cast; ring,
    Complex.exp_neg, complex_exp_two_pi_mul_I]
  norm_num

private theorem complex_exp_neg_three_pi_mul_I :
    Complex.exp (-(3 * Real.pi : Real) * Complex.I) = -1 := by
  rw [show -(3 * Real.pi : Real) * Complex.I =
      -(((3 * Real.pi : Real) : Complex) * Complex.I) by push_cast; ring,
    Complex.exp_neg, complex_exp_three_pi_mul_I]
  norm_num



theorem conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    (t z : Complex)
    (h : t * z ^ 2 = (Complex.normSq z : Complex)) :
    (starRingEnd Complex) z = t * z := by
  by_cases hz : z = 0
  · simp [hz]
  · apply (mul_right_cancel₀ hz)
    rw [mul_assoc, ← pow_two, h, Complex.normSq_eq_conj_mul_self]



theorem isingFermionic_horizontal_normSq_balance
    (W E S N : Complex)
    (hW : (starRingEnd Complex) W = W)
    (hE : (starRingEnd Complex) E = -E)
    (hS : (starRingEnd Complex) S = Complex.I * S)
    (hN : (starRingEnd Complex) N = -Complex.I * N)
    (hcontour : W - E = Complex.I * (S - N)) :
    Complex.normSq W + Complex.normSq E =
      Complex.normSq S + Complex.normSq N := by
  have hnorm := congrArg Complex.normSq hcontour
  rw [Complex.normSq_mul, Complex.normSq_I, one_mul,
    Complex.normSq_sub, Complex.normSq_sub] at hnorm
  have hWE : (W * (starRingEnd Complex) E).re = 0 := by
    have hc : (starRingEnd Complex) (W * (starRingEnd Complex) E) =
        -(W * (starRingEnd Complex) E) := by
      calc
        (starRingEnd Complex) (W * (starRingEnd Complex) E) =
            (starRingEnd Complex) W * E := by simp
        _ = W * E := by rw [hW]
        _ = -(W * (starRingEnd Complex) E) := by rw [hE]; ring
    have hre := congrArg Complex.re hc
    change (W * (starRingEnd Complex) E).re =
      -(W * (starRingEnd Complex) E).re at hre
    linarith
  have hSN : (S * (starRingEnd Complex) N).re = 0 := by
    have hc : (starRingEnd Complex) (S * (starRingEnd Complex) N) =
        -(S * (starRingEnd Complex) N) := by
      calc
        (starRingEnd Complex) (S * (starRingEnd Complex) N) =
            (starRingEnd Complex) S * N := by simp
        _ = (Complex.I * S) * N := by rw [hS]
        _ = -(S * (starRingEnd Complex) N) := by rw [hN]; ring
    have hre := congrArg Complex.re hc
    change (S * (starRingEnd Complex) N).re =
      -(S * (starRingEnd Complex) N).re at hre
    linarith
  linarith



theorem isingFermionic_vertical_normSq_balance
    (W E S N : Complex)
    (hW : (starRingEnd Complex) W = -Complex.I * W)
    (hE : (starRingEnd Complex) E = Complex.I * E)
    (hS : (starRingEnd Complex) S = S)
    (hN : (starRingEnd Complex) N = -N)
    (hcontour : W - E = Complex.I * (S - N)) :
    Complex.normSq W + Complex.normSq E =
      Complex.normSq S + Complex.normSq N := by
  have hnorm := congrArg Complex.normSq hcontour
  rw [Complex.normSq_mul, Complex.normSq_I, one_mul,
    Complex.normSq_sub, Complex.normSq_sub] at hnorm
  have hWE : (W * (starRingEnd Complex) E).re = 0 := by
    have hc : (starRingEnd Complex) (W * (starRingEnd Complex) E) =
        -(W * (starRingEnd Complex) E) := by
      calc
        (starRingEnd Complex) (W * (starRingEnd Complex) E) =
            (starRingEnd Complex) W * E := by simp
        _ = (-Complex.I * W) * E := by rw [hW]
        _ = -(W * (starRingEnd Complex) E) := by rw [hE]; ring
    have hre := congrArg Complex.re hc
    change (W * (starRingEnd Complex) E).re =
      -(W * (starRingEnd Complex) E).re at hre
    linarith
  have hSN : (S * (starRingEnd Complex) N).re = 0 := by
    have hc : (starRingEnd Complex) (S * (starRingEnd Complex) N) =
        -(S * (starRingEnd Complex) N) := by
      calc
        (starRingEnd Complex) (S * (starRingEnd Complex) N) =
            (starRingEnd Complex) S * N := by simp
        _ = S * N := by rw [hS]
        _ = -(S * (starRingEnd Complex) N) := by rw [hN]; ring
    have hre := congrArg Complex.re hc
    change (S * (starRingEnd Complex) N).re =
      -(S * (starRingEnd Complex) N).re at hre
    linarith
  linarith



theorem isingFermionic_horizontal_sum_balance
    (W E S N : Complex)
    (hW : (starRingEnd Complex) W = W)
    (hE : (starRingEnd Complex) E = -E)
    (hS : (starRingEnd Complex) S = Complex.I * S)
    (hN : (starRingEnd Complex) N = -Complex.I * N)
    (hcontour : W - E = Complex.I * (S - N)) :
    W + E = S + N := by
  have hc := congrArg (starRingEnd Complex) hcontour
  simp only [map_sub, map_mul, Complex.conj_I, hW, hE, hS, hN] at hc
  have hrhs : -Complex.I *
      (Complex.I * S - -Complex.I * N) = S + N := by
    rw [show -Complex.I * (Complex.I * S - -Complex.I * N) =
        -(Complex.I * Complex.I) * (S + N) by ring,
      Complex.I_mul_I]
    ring
  rw [hrhs] at hc
  simpa only [sub_neg_eq_add] using hc


theorem isingFermionic_vertical_sum_balance
    (W E S N : Complex)
    (hW : (starRingEnd Complex) W = -Complex.I * W)
    (hE : (starRingEnd Complex) E = Complex.I * E)
    (hS : (starRingEnd Complex) S = S)
    (hN : (starRingEnd Complex) N = -N)
    (hcontour : W - E = Complex.I * (S - N)) :
    W + E = S + N := by
  have hc := congrArg (starRingEnd Complex) hcontour
  simp only [map_sub, map_mul, Complex.conj_I, hW, hE, hS, hN] at hc
  have hc' : -Complex.I * (W + E) =
      -Complex.I * (S + N) := by
    calc
      -Complex.I * (W + E) = -Complex.I * W - Complex.I * E := by ring
      _ = -Complex.I * (S - -N) := hc
      _ = -Complex.I * (S + N) := by ring
  exact mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) hc'



theorem isingProj_add_of_complementary_arg
    (e x y : Complex) (he : Complex.normSq e = 1)
    (hx : (starRingEnd Complex) x = e * x)
    (hy : (starRingEnd Complex) y = -e * y) :
    isingProj e (x + y) = x := by
  rw [isingProj_add, isingProj_of_arg e x he hx]
  suffices isingProj e y = 0 by rw [this, add_zero]
  unfold isingProj
  rw [hy]
  rw [show (starRingEnd Complex) e * (-e * y) =
      -((starRingEnd Complex) e * e) * y by ring,
    ← Complex.normSq_eq_conj_mul_self, he]
  push_cast
  ring



theorem fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal) :
    fkIsingSquareWiredDirectedTangentCode n hn (.bond (e, .west)) = 3 ∧
      fkIsingSquareWiredDirectedTangentCode n hn (.bond (e, .east)) = 7 ∧
      fkIsingSquareWiredDirectedTangentCode n hn (.bond (e, .south)) = 9 ∧
      fkIsingSquareWiredDirectedTangentCode n hn (.bond (e, .north)) = 13 := by
  simp [fkIsingSquareWiredDirectedTangentCode,
    fkIsingSquareWiredCarrierTangentCode,
    fkIsingSquareWiredObservationCorrection,
    fkIsingSquareCornerTangentCode, fkIsingSquareDartDirection,
    fkIsingSquareSideCorner, FKIsingSquareDirection.eighthTurn, haxis]



theorem fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical) :
    fkIsingSquareWiredDirectedTangentCode n hn (.bond (e, .west)) = 5 ∧
      fkIsingSquareWiredDirectedTangentCode n hn (.bond (e, .east)) = 9 ∧
      fkIsingSquareWiredDirectedTangentCode n hn (.bond (e, .south)) = 11 ∧
      fkIsingSquareWiredDirectedTangentCode n hn (.bond (e, .north)) = 15 := by
  simp [fkIsingSquareWiredDirectedTangentCode,
    fkIsingSquareWiredCarrierTangentCode,
    fkIsingSquareWiredObservationCorrection,
    fkIsingSquareCornerTangentCode, fkIsingSquareDartDirection,
    fkIsingSquareSideCorner, FKIsingSquareDirection.eighthTurn, haxis]

theorem fkIsingSquareWiredDirectedTangent_horizontal_local
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal) :
    fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) = 1 ∧
      fkIsingSquareWiredDirectedTangent n hn (.dart (e, .east)) = -1 ∧
      fkIsingSquareWiredDirectedTangent n hn (.dart (e, .south)) = Complex.I ∧
      fkIsingSquareWiredDirectedTangent n hn (.dart (e, .north)) = -Complex.I := by
  have hterminal := fkIsingSquareWiredDirectedTangentCode_terminal n hn
  have hW : fkIsingSquareWiredDirectedTangentCode n hn (.dart (e, .west)) = 3 := by
    simp [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareCornerTangentCode, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, FKIsingSquareDirection.eighthTurn, haxis]
  have hE : fkIsingSquareWiredDirectedTangentCode n hn (.dart (e, .east)) = 7 := by
    simp [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareCornerTangentCode, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, FKIsingSquareDirection.eighthTurn, haxis]
  have hS : fkIsingSquareWiredDirectedTangentCode n hn (.dart (e, .south)) = 9 := by
    simp [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareCornerTangentCode, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, FKIsingSquareDirection.eighthTurn, haxis]
  have hN : fkIsingSquareWiredDirectedTangentCode n hn (.dart (e, .north)) = 13 := by
    simp [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareCornerTangentCode, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, FKIsingSquareDirection.eighthTurn, haxis]
  constructor
  · simp only [fkIsingSquareWiredDirectedTangent, hterminal, hW]
    convert Complex.exp_zero using 2 <;> push_cast <;> ring
  constructor
  · simp only [fkIsingSquareWiredDirectedTangent, hterminal, hE]
    norm_num
    rw [show -(Complex.I * (4 * ((Real.pi : Complex) / 4))) =
        -((Real.pi : Complex) * Complex.I) by ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  constructor
  · simp only [fkIsingSquareWiredDirectedTangent, hterminal, hS]
    norm_num
    rw [show -(Complex.I * (6 * ((Real.pi : Complex) / 4))) =
        -(Real.pi : Complex) * Complex.I -
          (Real.pi / 2 : Real) * Complex.I by push_cast; ring,
      Complex.exp_sub, complex_exp_neg_pi_mul_I,
      complex_exp_pi_div_two_mul_I]
    norm_num
  · simp only [fkIsingSquareWiredDirectedTangent, hterminal, hN]
    norm_num
    rw [show -(Complex.I * (10 * ((Real.pi : Complex) / 4))) =
        -(2 * Real.pi : Real) * Complex.I -
          (Real.pi / 2 : Real) * Complex.I by push_cast; ring,
      Complex.exp_sub, complex_exp_neg_two_pi_mul_I,
      complex_exp_pi_div_two_mul_I]
    norm_num


theorem fkIsingSquareWiredDirectedTangent_vertical_local
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical) :
    fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) = -Complex.I ∧
      fkIsingSquareWiredDirectedTangent n hn (.dart (e, .east)) = Complex.I ∧
      fkIsingSquareWiredDirectedTangent n hn (.dart (e, .south)) = 1 ∧
      fkIsingSquareWiredDirectedTangent n hn (.dart (e, .north)) = -1 := by
  have hterminal := fkIsingSquareWiredDirectedTangentCode_terminal n hn
  have hW : fkIsingSquareWiredDirectedTangentCode n hn (.dart (e, .west)) = 5 := by
    simp [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareCornerTangentCode, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, FKIsingSquareDirection.eighthTurn, haxis]
  have hE : fkIsingSquareWiredDirectedTangentCode n hn (.dart (e, .east)) = 9 := by
    simp [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareCornerTangentCode, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, FKIsingSquareDirection.eighthTurn, haxis]
  have hS : fkIsingSquareWiredDirectedTangentCode n hn (.dart (e, .south)) = 11 := by
    simp [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareCornerTangentCode, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, FKIsingSquareDirection.eighthTurn, haxis]
  have hN : fkIsingSquareWiredDirectedTangentCode n hn (.dart (e, .north)) = 15 := by
    simp [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareCornerTangentCode, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, FKIsingSquareDirection.eighthTurn, haxis]
  constructor
  · simp only [fkIsingSquareWiredDirectedTangent, hterminal, hW]
    norm_num
    rw [show -(Complex.I * (2 * ((Real.pi : Complex) / 4))) =
        -(Real.pi / 2 : Real) * Complex.I by push_cast; ring,
      complex_exp_neg_pi_div_two_mul_I]
  constructor
  · simp only [fkIsingSquareWiredDirectedTangent, hterminal, hE]
    norm_num
    rw [show -(Complex.I * (6 * ((Real.pi : Complex) / 4))) =
        -(Real.pi : Complex) * Complex.I -
          (Real.pi / 2 : Real) * Complex.I by push_cast; ring,
      Complex.exp_sub, complex_exp_neg_pi_mul_I,
      complex_exp_pi_div_two_mul_I]
    norm_num
  constructor
  · simp only [fkIsingSquareWiredDirectedTangent, hterminal, hS]
    norm_num
    rw [show -(Complex.I * (8 * ((Real.pi : Complex) / 4))) =
        -(2 * Real.pi : Real) * Complex.I by push_cast; ring,
      complex_exp_neg_two_pi_mul_I]
  · simp only [fkIsingSquareWiredDirectedTangent, hterminal, hN]
    norm_num
    rw [show -(Complex.I * (12 * ((Real.pi : Complex) / 4))) =
        -(3 * Real.pi : Real) * Complex.I by push_cast; ring,
      complex_exp_neg_three_pi_mul_I]




theorem fkIsingSquareWiredPrimitiveIncrement_local_closed
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .west)) +
        fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .east)) =
      fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .south)) +
        fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .north)) := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let W := D.fermionicObservable (.dart (e, .west))
  let E := D.fermionicObservable (.dart (e, .east))
  let S := D.fermionicObservable (.dart (e, .south))
  let N := D.fermionicObservable (.dart (e, .north))
  have hcontour : W - E = Complex.I * (S - N) := by
    simpa only [W, E, S, N, D] using
      fkIsingSquareWired_fermionicObservable_contour_relation n hn e
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z * D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareWiredPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareWired_tangent_mul_observable_sq_eq_increment n hn z
  unfold fkIsingSquareWiredPrimitiveIncrement isingPrimitiveIncrement
  change Complex.normSq W + Complex.normSq E =
    Complex.normSq S + Complex.normSq N
  cases haxis : (fkIsingSquareOrientedEdge n e).axis with
  | horizontal =>
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨hW, hE, hS, hN⟩
      apply isingFermionic_horizontal_normSq_balance W E S N
      · simpa only [W, hW, one_mul] using hline (.dart (e, .west))
      · simpa only [E, hE, neg_mul, one_mul] using hline (.dart (e, .east))
      · simpa only [S, hS] using hline (.dart (e, .south))
      · simpa only [N, hN, neg_mul] using hline (.dart (e, .north))
      · exact hcontour
  | vertical =>
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨hW, hE, hS, hN⟩
      apply isingFermionic_vertical_normSq_balance W E S N
      · simpa only [W, hW, neg_mul] using hline (.dart (e, .west))
      · simpa only [E, hE] using hline (.dart (e, .east))
      · simpa only [S, hS, one_mul] using hline (.dart (e, .south))
      · simpa only [N, hN, neg_mul, one_mul] using hline (.dart (e, .north))
      · exact hcontour



theorem fkIsingSquareWired_fermionicObservable_opposite_sum
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (e, .west)) +
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (e, .east)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (e, .south)) +
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (e, .north)) := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let W := D.fermionicObservable (.dart (e, .west))
  let E := D.fermionicObservable (.dart (e, .east))
  let S := D.fermionicObservable (.dart (e, .south))
  let N := D.fermionicObservable (.dart (e, .north))
  have hcontour : W - E = Complex.I * (S - N) := by
    simpa only [W, E, S, N, D] using
      fkIsingSquareWired_fermionicObservable_contour_relation n hn e
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z * D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareWiredPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareWired_tangent_mul_observable_sq_eq_increment n hn z
  change W + E = S + N
  cases haxis : (fkIsingSquareOrientedEdge n e).axis with
  | horizontal =>
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨hW, hE, hS, hN⟩
      apply isingFermionic_horizontal_sum_balance W E S N
      · simpa only [W, hW, one_mul] using hline (.dart (e, .west))
      · simpa only [E, hE, neg_mul, one_mul] using hline (.dart (e, .east))
      · simpa only [S, hS] using hline (.dart (e, .south))
      · simpa only [N, hN, neg_mul] using hline (.dart (e, .north))
      · exact hcontour
  | vertical =>
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨hW, hE, hS, hN⟩
      apply isingFermionic_vertical_sum_balance W E S N
      · simpa only [W, hW, neg_mul] using hline (.dart (e, .west))
      · simpa only [E, hE] using hline (.dart (e, .east))
      · simpa only [S, hS, one_mul] using hline (.dart (e, .south))
      · simpa only [N, hN, neg_mul, one_mul] using hline (.dart (e, .north))
      · exact hcontour



noncomputable def fkIsingSquareWiredFullMedialObservable
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) : Complex :=
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
      (.dart (e, .west)) +
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
      (.dart (e, .east))

theorem fkIsingSquareWiredFullMedialObservable_eq_south_add_north
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredFullMedialObservable n hn e =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (e, .south)) +
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (e, .north)) :=
  fkIsingSquareWired_fermionicObservable_opposite_sum n hn e



theorem fkIsingSquareWiredFullMedialObservable_projection
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (s : FKIsingMedialSide) :
    isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (e, s)))
        (fkIsingSquareWiredFullMedialObservable n hn e) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (e, s)) := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let W := D.fermionicObservable (.dart (e, .west))
  let E := D.fermionicObservable (.dart (e, .east))
  let S := D.fermionicObservable (.dart (e, .south))
  let N := D.fermionicObservable (.dart (e, .north))
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z * D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareWiredPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareWired_tangent_mul_observable_sq_eq_increment n hn z
  have hsum : W + E = S + N := by
    simpa only [W, E, S, N, D] using
      fkIsingSquareWired_fermionicObservable_opposite_sum n hn e
  change isingProj _ (W + E) = _
  cases haxis : (fkIsingSquareOrientedEdge n e).axis with
  | horizontal =>
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨htW, htE, htS, htN⟩
      cases s
      · rw [htW]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [W, htW, one_mul] using hline (.dart (e, .west))
        · simpa only [E, htE, neg_mul, one_mul] using hline (.dart (e, .east))
      · rw [htE, add_comm]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [E, htE] using hline (.dart (e, .east))
        · simpa only [W, htW, one_mul, neg_neg, neg_one_mul] using
            hline (.dart (e, .west))
      · rw [htS, hsum]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [S, htS] using hline (.dart (e, .south))
        · simpa only [N, htN, neg_mul, neg_neg] using hline (.dart (e, .north))
      · rw [htN, hsum, add_comm]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [N, htN, neg_mul] using hline (.dart (e, .north))
        · simpa only [S, htS, neg_neg] using hline (.dart (e, .south))
  | vertical =>
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨htW, htE, htS, htN⟩
      cases s
      · rw [htW]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [W, htW, neg_mul] using hline (.dart (e, .west))
        · simpa only [E, htE, neg_neg] using hline (.dart (e, .east))
      · rw [htE, add_comm]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [E, htE] using hline (.dart (e, .east))
        · simpa only [W, htW, neg_mul, neg_neg] using hline (.dart (e, .west))
      · rw [htS, hsum]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [S, htS, one_mul] using hline (.dart (e, .south))
        · simpa only [N, htN, neg_mul, one_mul] using hline (.dart (e, .north))
      · rw [htN, hsum, add_comm]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [N, htN, neg_mul, one_mul] using hline (.dart (e, .north))
        · simpa only [S, htS, one_mul, neg_neg, neg_one_mul] using
            hline (.dart (e, .south))



theorem fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (s : FKIsingMedialSide) :
    fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, s)) =
      Complex.normSq
        (isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (e, s)))
          (fkIsingSquareWiredFullMedialObservable n hn e)) := by
  unfold fkIsingSquareWiredPrimitiveIncrement isingPrimitiveIncrement
  rw [fkIsingSquareWiredFullMedialObservable_projection]



theorem fkIsingSquareWired_normSq_full_eq_west_add_east_increment
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    Complex.normSq (fkIsingSquareWiredFullMedialObservable n hn e) =
      fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .west)) +
        fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .east)) := by
  rw [fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection,
    fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection]
  cases haxis : (fkIsingSquareOrientedEdge n e).axis with
  | horizontal =>
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨hW, hE, -, -⟩
      rw [hW, hE]
      exact (isingProj_normSq_add_neg 1 _ (by norm_num)).symm
  | vertical =>
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨hW, hE, -, -⟩
      rw [hW, hE]
      convert (isingProj_normSq_add_neg (-Complex.I) _ (by norm_num)).symm using 1 <;>
        ring



theorem fkIsingSquareWired_normSq_full_eq_south_add_north_increment
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    Complex.normSq (fkIsingSquareWiredFullMedialObservable n hn e) =
      fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .south)) +
        fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .north)) := by
  rw [fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection,
    fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection]
  cases haxis : (fkIsingSquareOrientedEdge n e).axis with
  | horizontal =>
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨-, -, hS, hN⟩
      rw [hS, hN]
      exact (isingProj_normSq_add_neg Complex.I _ (by norm_num)).symm
  | vertical =>
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨-, -, hS, hN⟩
      rw [hS, hN]
      exact (isingProj_normSq_add_neg 1 _ (by norm_num)).symm

end

end StatMech.Universality
