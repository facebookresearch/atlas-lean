/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexMarkedTraceExpansion








open Finset Matrix

namespace StatMech.FrontierD

noncomputable section

open Polynomial

theorem sixVertexShiftedSectorTransferPolynomial_particleHole
    {N n : Nat} (hn : n <= N) (x y : SixVertexSector N n) :
    sixVertexShiftedSectorTransferPolynomial N (N - n)
        (sixVertexSectorParticleHoleEquiv N n hn x)
        (sixVertexSectorParticleHoleEquiv N n hn y) =
      sixVertexShiftedSectorTransferPolynomial N n x y := by
  classical
  let e := sixVertexSectorParticleHoleEquiv N n hn
  have heinj : Function.Injective
      (fun x : SixVertexSector N n => sixVertexSectorRow (e x)) :=
    sixVertexSectorRow_injective.comp e.injective
  by_cases hxy : x = y
  · subst y
    simp [sixVertexShiftedSectorTransferPolynomial]
  · have hexy : sixVertexSectorRow (e x) ≠ sixVertexSectorRow (e y) := by
      intro h
      exact hxy (heinj h)
    dsimp [e] at hexy
    have hrowxy : sixVertexSectorRow x ≠ sixVertexSectorRow y := by
      intro h
      exact hxy (sixVertexSectorRow_injective h)
    by_cases hinter : SixVertexInterlaced
        (sixVertexSectorRow x) (sixVertexSectorRow y)
    · have hinter' := (sixVertexInterlaced_particleHole_iff hn x y).mpr hinter
      simp [sixVertexShiftedSectorTransferPolynomial, hrowxy, hexy,
        hinter, hinter', sixVertexRowDistance_particleHole hn x y]
    · have hinter' : ¬ SixVertexInterlaced
          (sixVertexSectorRow (e x)) (sixVertexSectorRow (e y)) := by
        exact fun h => hinter ((sixVertexInterlaced_particleHole_iff hn x y).mp h)
      change ¬ SixVertexInterlaced
        (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn x))
        (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn y)) at hinter'
      simp [sixVertexShiftedSectorTransferPolynomial, hrowxy, hexy,
        hinter, hinter']



theorem matrix_trace_pow_eq_of_equiv
    {alpha beta R : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta] [CommSemiring R]
    (e : alpha ≃ beta) (A : Matrix alpha alpha R) (B : Matrix beta beta R)
    (hentry : forall x y, B (e x) (e y) = A x y) (M : Nat) :
    Matrix.trace (B ^ M) = Matrix.trace (A ^ M) := by
  have hpow : forall m x y, (B ^ m) (e x) (e y) = (A ^ m) x y := by
    intro m
    induction m with
    | zero =>
        intro x y
        by_cases hxy : x = y
        · subst y
          simp
        · have hexy : e x ≠ e y := fun h => hxy (e.injective h)
          simp [hxy, hexy]
    | succ m ih =>
        intro x y
        rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
        calc
          ∑ z : beta, (B ^ m) (e x) z * B z (e y) =
              ∑ z : alpha, (B ^ m) (e x) (e z) * B (e z) (e y) := by
            symm
            apply Fintype.sum_equiv e
            intro z
            rfl
          _ = ∑ z : alpha, (A ^ m) x z * A z y := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [ih, hentry]
  unfold Matrix.trace
  calc
    ∑ y : beta, (B ^ M) y y =
        ∑ x : alpha, (B ^ M) (e x) (e x) := by
      symm
      apply Fintype.sum_equiv e
      intro x
      rfl
    _ = ∑ x : alpha, (A ^ M) x x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hpow M x x

theorem sixVertexShiftedSectorTracePolynomial_particleHole
    {N n : Nat} (hn : n <= N) (M : Nat) :
    sixVertexShiftedSectorTracePolynomial N M (N - n) =
      sixVertexShiftedSectorTracePolynomial N M n := by
  unfold sixVertexShiftedSectorTracePolynomial
  apply matrix_trace_pow_eq_of_equiv
    (sixVertexSectorParticleHoleEquiv N n hn)
  exact sixVertexShiftedSectorTransferPolynomial_particleHole hn

theorem sixVertexMarkedSectorTraceCoefficient_particleHole
    {N n : Nat} (hn : n <= N) (M k : Nat) :
    sixVertexMarkedSectorTraceCoefficient N M (N - n) k =
      sixVertexMarkedSectorTraceCoefficient N M n k := by
  unfold sixVertexMarkedSectorTraceCoefficient
  rw [sixVertexShiftedSectorTracePolynomial_particleHole hn]

theorem sixVertexMarkedTraceLogConcavityDifference_particleHole
    {N n : Nat} (hn0 : 0 < n) (hnN : n < N) (M : Nat) :
    sixVertexMarkedTraceLogConcavityDifference N M (N - n) =
      sixVertexMarkedTraceLogConcavityDifference N M n := by
  have hn : n <= N := hnN.le
  have hnPrev : n - 1 <= N := by omega
  have hnNext : n + 1 <= N := by omega
  have hmid := sixVertexShiftedSectorTracePolynomial_particleHole hn M
  have hprev := sixVertexShiftedSectorTracePolynomial_particleHole hnPrev M
  have hnext := sixVertexShiftedSectorTracePolynomial_particleHole hnNext M
  unfold sixVertexMarkedTraceLogConcavityDifference
  rw [hmid]
  rw [show N - n - 1 = N - (n + 1) by omega, hnext]
  rw [show N - n + 1 = N - (n - 1) by omega, hprev]
  ring



theorem markedCoefficientwiseLogConcave_of_lowerHalf_suffix
    (N M : Nat)
    (hsuffix : forall n : Nat, 0 < n -> n <= N / 2 ->
      SixVertexMarkedAntidiagonalSuffixNonnegative N M n) :
    forall n : Nat, 0 < n -> n < N ->
      SixVertexMarkedTraceCoefficientwiseLogConcave N M n := by
  intro n hn0 hnN
  by_cases hnHalf : n <= N / 2
  · exact (hsuffix n hn0 hnHalf).coefficientwiseLogConcave
  · let m := N - n
    have hm0 : 0 < m := by dsimp [m]; omega
    have hmHalf : m <= N / 2 := by dsimp [m]; omega
    have hm := (hsuffix m hm0 hmHalf).coefficientwiseLogConcave
    intro k
    rw [← sixVertexMarkedTraceLogConcavityDifference_particleHole
      hn0 hnN M]
    exact hm k

end

end StatMech.FrontierD
