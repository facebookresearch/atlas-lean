/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexSectorPerronLogConcavity
import Mathlib.Algebra.Polynomial.Eval.Degree










open Finset Matrix

namespace StatMech.FrontierD

noncomputable section

open Polynomial


noncomputable def sixVertexShiftedSectorTransferPolynomial
    (N n : Nat) : Matrix (SixVertexSector N n) (SixVertexSector N n) Real[X] := by
  classical
  exact fun x y =>
    if sixVertexSectorRow x = sixVertexSectorRow y then C 2
    else if SixVertexInterlaced
        (sixVertexSectorRow x) (sixVertexSectorRow y) then
      (C 2 + X) ^ sixVertexRowDistance
        (sixVertexSectorRow x) (sixVertexSectorRow y)
    else 0

theorem eval_sixVertexShiftedSectorTransferPolynomial_apply
    (N n : Nat) (t : Real) (x y : SixVertexSector N n) :
    eval t (sixVertexShiftedSectorTransferPolynomial N n x y) =
      sixVertexSectorTransfer N n (2 + t) x y := by
  classical
  unfold sixVertexShiftedSectorTransferPolynomial sixVertexSectorTransfer
  unfold sixVertexTransfer
  by_cases hxy : sixVertexSectorRow x = sixVertexSectorRow y
  · simp [hxy]
  · by_cases hinter : SixVertexInterlaced
        (sixVertexSectorRow x) (sixVertexSectorRow y)
    · simp [hxy, hinter]
    · simp [hxy, hinter]

theorem map_sixVertexShiftedSectorTransferPolynomial
    (N n : Nat) (t : Real) :
    (sixVertexShiftedSectorTransferPolynomial N n).map (evalRingHom t) =
      sixVertexSectorTransfer N n (2 + t) := by
  ext x y
  exact eval_sixVertexShiftedSectorTransferPolynomial_apply N n t x y


def Polynomial.CoeffNonnegative (p : Real[X]) : Prop :=
  forall k, 0 <= p.coeff k

theorem Polynomial.coeffNonnegative_zero :
    Polynomial.CoeffNonnegative (0 : Real[X]) := by
  intro k
  simp

theorem Polynomial.coeffNonnegative_one :
    Polynomial.CoeffNonnegative (1 : Real[X]) := by
  intro k
  simp only [Polynomial.coeff_one]
  split <;> positivity

theorem Polynomial.coeffNonnegative_add
    {p q : Real[X]} (hp : Polynomial.CoeffNonnegative p)
    (hq : Polynomial.CoeffNonnegative q) :
    Polynomial.CoeffNonnegative (p + q) := by
  intro k
  rw [Polynomial.coeff_add]
  exact add_nonneg (hp k) (hq k)

theorem Polynomial.coeffNonnegative_mul
    {p q : Real[X]} (hp : Polynomial.CoeffNonnegative p)
    (hq : Polynomial.CoeffNonnegative q) :
    Polynomial.CoeffNonnegative (p * q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg fun ij _ => mul_nonneg (hp ij.1) (hq ij.2)

theorem Polynomial.coeffNonnegative_pow
    {p : Real[X]} (hp : Polynomial.CoeffNonnegative p) (m : Nat) :
    Polynomial.CoeffNonnegative (p ^ m) := by
  induction m with
  | zero => exact Polynomial.coeffNonnegative_one
  | succ m ih =>
      rw [pow_succ]
      exact Polynomial.coeffNonnegative_mul ih hp

theorem Polynomial.coeffNonnegative_sum
    {alpha : Type*} (s : Finset alpha) (f : alpha -> Real[X])
    (hf : ∀ i ∈ s, Polynomial.CoeffNonnegative (f i)) :
    Polynomial.CoeffNonnegative (∑ i ∈ s, f i) := by
  intro k
  rw [← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply]
  exact Finset.sum_nonneg fun i hi => hf i hi k

theorem Polynomial.coeffNonnegative_two_add_X :
    Polynomial.CoeffNonnegative (C 2 + X : Real[X]) := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    norm_num
  · by_cases hk1 : k = 1
    · subst k
      norm_num
    · have hk1' : 1 ≠ k := Ne.symm hk1
      simp [Polynomial.coeff_add, Polynomial.coeff_C,
        Polynomial.coeff_X, hk0, hk1']

theorem sixVertexShiftedSectorTransferPolynomial_coeffNonnegative
    (N n : Nat) (x y : SixVertexSector N n) :
    Polynomial.CoeffNonnegative
      (sixVertexShiftedSectorTransferPolynomial N n x y) := by
  classical
  unfold sixVertexShiftedSectorTransferPolynomial
  split
  · intro k
    by_cases hk : k = 0
    · subst k
      norm_num
    · simp [Polynomial.coeff_C, hk]
  · split
    · exact Polynomial.coeffNonnegative_pow
        Polynomial.coeffNonnegative_two_add_X _
    · exact Polynomial.coeffNonnegative_zero

theorem sixVertexShiftedSectorTransferPolynomial_pow_coeffNonnegative
    (N n M : Nat) (x y : SixVertexSector N n) :
    Polynomial.CoeffNonnegative
      ((sixVertexShiftedSectorTransferPolynomial N n ^ M) x y) := by
  induction M generalizing x y with
  | zero =>
      simp only [pow_zero, Matrix.one_apply]
      split
      · exact Polynomial.coeffNonnegative_one
      · exact Polynomial.coeffNonnegative_zero
  | succ M ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Polynomial.coeffNonnegative_sum
      intro z hz
      exact Polynomial.coeffNonnegative_mul (ih x z)
        (sixVertexShiftedSectorTransferPolynomial_coeffNonnegative N n z y)


noncomputable def sixVertexShiftedSectorTracePolynomial
    (N M n : Nat) : Real[X] :=
  Matrix.trace (sixVertexShiftedSectorTransferPolynomial N n ^ M)

theorem eval_sixVertexShiftedSectorTracePolynomial
    (N M n : Nat) (t : Real) :
    eval t (sixVertexShiftedSectorTracePolynomial N M n) =
      Matrix.trace (sixVertexSectorTransfer N n (2 + t) ^ M) := by
  unfold sixVertexShiftedSectorTracePolynomial
  change (evalRingHom t)
      (Matrix.trace (sixVertexShiftedSectorTransferPolynomial N n ^ M)) = _
  rw [AddMonoidHom.map_trace, Matrix.map_pow,
    map_sixVertexShiftedSectorTransferPolynomial]



noncomputable def sixVertexMarkedSectorTraceCoefficient
    (N M n k : Nat) : Real :=
  (sixVertexShiftedSectorTracePolynomial N M n).coeff k

theorem sixVertexMarkedSectorTraceCoefficient_nonneg
    (N M n k : Nat) :
    0 <= sixVertexMarkedSectorTraceCoefficient N M n k := by
  unfold sixVertexMarkedSectorTraceCoefficient
  apply (show Polynomial.CoeffNonnegative
      (sixVertexShiftedSectorTracePolynomial N M n) from ?_)
  unfold sixVertexShiftedSectorTracePolynomial Matrix.trace
  apply Polynomial.coeffNonnegative_sum
  intro x hx
  exact sixVertexShiftedSectorTransferPolynomial_pow_coeffNonnegative
    N n M x x


noncomputable def sixVertexMarkedFugacityPolynomial
    (N M k : Nat) : Real[X] :=
  ∑ n ∈ Finset.range (N + 1),
    Polynomial.monomial n (sixVertexMarkedSectorTraceCoefficient N M n k)

theorem coeff_sixVertexMarkedFugacityPolynomial
    (N M k n : Nat) (hn : n <= N) :
    (sixVertexMarkedFugacityPolynomial N M k).coeff n =
      sixVertexMarkedSectorTraceCoefficient N M n k := by
  classical
  simp [sixVertexMarkedFugacityPolynomial, Polynomial.coeff_monomial, hn]



noncomputable def sixVertexMarkedTraceLogConcavityDifference
    (N M n : Nat) : Real[X] :=
  sixVertexShiftedSectorTracePolynomial N M n ^ 2 -
    sixVertexShiftedSectorTracePolynomial N M (n - 1) *
      sixVertexShiftedSectorTracePolynomial N M (n + 1)

theorem eval_sixVertexMarkedTraceLogConcavityDifference
    (N M n : Nat) (t : Real) :
    eval t (sixVertexMarkedTraceLogConcavityDifference N M n) =
      Matrix.trace (sixVertexSectorTransfer N n (2 + t) ^ M) ^ 2 -
        Matrix.trace (sixVertexSectorTransfer N (n - 1) (2 + t) ^ M) *
          Matrix.trace
            (sixVertexSectorTransfer N (n + 1) (2 + t) ^ M) := by
  simp [sixVertexMarkedTraceLogConcavityDifference,
    eval_sixVertexShiftedSectorTracePolynomial]



theorem coeff_sixVertexMarkedTraceLogConcavityDifference
    (N M n k : Nat) :
    (sixVertexMarkedTraceLogConcavityDifference N M n).coeff k =
      ∑ ij ∈ Finset.antidiagonal k,
        (sixVertexMarkedSectorTraceCoefficient N M n ij.1 *
            sixVertexMarkedSectorTraceCoefficient N M n ij.2 -
          sixVertexMarkedSectorTraceCoefficient N M (n - 1) ij.1 *
            sixVertexMarkedSectorTraceCoefficient N M (n + 1) ij.2) := by
  unfold sixVertexMarkedTraceLogConcavityDifference
  simp only [pow_two, Polynomial.coeff_sub, Polynomial.coeff_mul,
    sixVertexMarkedSectorTraceCoefficient]
  rw [Finset.sum_sub_distrib]

theorem coeff_sixVertexMarkedTraceLogConcavityDifference_eq_sum_range
    (N M n k : Nat) :
    (sixVertexMarkedTraceLogConcavityDifference N M n).coeff k =
      ∑ i ∈ Finset.range (k + 1),
        (sixVertexMarkedSectorTraceCoefficient N M n i *
            sixVertexMarkedSectorTraceCoefficient N M n (k - i) -
          sixVertexMarkedSectorTraceCoefficient N M (n - 1) i *
            sixVertexMarkedSectorTraceCoefficient N M (n + 1) (k - i)) := by
  rw [coeff_sixVertexMarkedTraceLogConcavityDifference]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ k



def SixVertexMarkedAntidiagonalSuffixNonnegative
    (N M n : Nat) : Prop :=
  forall k r : Nat, r <= k ->
    0 <= ∑ i ∈ (Finset.range (k + 1)).filter (fun i => r <= i),
      (sixVertexMarkedSectorTraceCoefficient N M n i *
          sixVertexMarkedSectorTraceCoefficient N M n (k - i) -
        sixVertexMarkedSectorTraceCoefficient N M (n - 1) i *
          sixVertexMarkedSectorTraceCoefficient N M (n + 1) (k - i))


def SixVertexMarkedTraceCoefficientwiseLogConcave
    (N M n : Nat) : Prop :=
  forall k, 0 <=
    (sixVertexMarkedTraceLogConcavityDifference N M n).coeff k

theorem
    SixVertexMarkedAntidiagonalSuffixNonnegative.coefficientwiseLogConcave
    {N M n : Nat}
    (h : SixVertexMarkedAntidiagonalSuffixNonnegative N M n) :
    SixVertexMarkedTraceCoefficientwiseLogConcave N M n := by
  intro k
  rw [coeff_sixVertexMarkedTraceLogConcavityDifference_eq_sum_range]
  have hk := h k 0 (Nat.zero_le k)
  simpa using hk



theorem Polynomial.eval_nonneg_of_coeff_nonneg
    (p : Real[X]) (t : Real) (ht : 0 <= t)
    (hcoeff : forall k, 0 <= p.coeff k) :
    0 <= p.eval t := by
  rw [Polynomial.eval_eq_sum_range]
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (hcoeff k) (pow_nonneg ht k)



theorem sixVertexSectorTrace_logConcave_of_markedCoefficientwise
    (N M n : Nat) {c : Real} (hc : 2 <= c)
    (hcoeff : SixVertexMarkedTraceCoefficientwiseLogConcave N M n) :
    Matrix.trace (sixVertexSectorTransfer N (n - 1) c ^ M) *
        Matrix.trace (sixVertexSectorTransfer N (n + 1) c ^ M) <=
      Matrix.trace (sixVertexSectorTransfer N n c ^ M) ^ 2 := by
  let t := c - 2
  have ht : 0 <= t := by dsimp [t]; linarith
  have hnonneg := Polynomial.eval_nonneg_of_coeff_nonneg
    (sixVertexMarkedTraceLogConcavityDifference N M n) t ht hcoeff
  rw [eval_sixVertexMarkedTraceLogConcavityDifference] at hnonneg
  have hct : 2 + t = c := by dsimp [t]; ring
  rw [hct] at hnonneg
  linarith



theorem sixVertexSectorTraceLogConcave_of_markedCoefficientwise
    (N : Nat) {c : Real} (hc : 2 <= c)
    (hcoeff : forall M n : Nat, 0 < M -> 0 < n -> n < N ->
      SixVertexMarkedTraceCoefficientwiseLogConcave N M n) :
    SixVertexSectorTraceLogConcave N c := by
  intro M n hM hn0 hnN
  rw [sixVertexSectorTraceProfile_eq (by omega),
    sixVertexSectorTraceProfile_eq (by omega),
    sixVertexSectorTraceProfile_eq (by omega)]
  exact sixVertexSectorTrace_logConcave_of_markedCoefficientwise
    N M n hc (hcoeff M n hM hn0 hnN)

end

end StatMech.FrontierD
