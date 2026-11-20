/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.PositiveTransferPerron

open Finset Matrix Filter Topology

namespace StatMech.Ising

noncomputable section

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]



theorem hermitian_twoTail_contraction_eq_sum_sq
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (a : alpha -> Real) (n : Nat) :
    (∑ i, a i * ((A ^ (2 * n)) *ᵥ a) i) =
      ∑ i, ((A ^ n) *ᵥ a) i ^ 2 := by
  rw [show 2 * n = n + n by omega, pow_add, ← Matrix.mulVec_mulVec]
  let v : alpha -> Real := (A ^ n) *ᵥ a
  change (∑ i, a i * ((A ^ n) *ᵥ v) i) = ∑ i, v i ^ 2
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (∑ i, a i * ((A ^ n) i j * v j)) =
      (∑ i, a i * (A ^ n) i j) * v j by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  have hpow : (A ^ n).IsHermitian := hHerm.pow n
  have hinner : (∑ i, a i * (A ^ n) i j) = v j := by
    unfold v Matrix.mulVec dotProduct
    apply Finset.sum_congr rfl
    intro i hi
    have hs := hpow.apply j i
    simp only [star_trivial] at hs
    rw [hs]
    ring
  rw [hinner]
  ring



theorem positiveTransfer_centerObservable_tendsto
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hpos : forall i j, 0 < A i j)
    (a : alpha -> Real) (ha : forall i, 0 < a i)
    (obs : alpha -> Real) :
    exists lam : Real, 0 < lam ∧
      exists u : EuclideanSpace Real alpha,
        (forall i, 0 < u i) ∧ norm u = 1 ∧
        A *ᵥ (fun i => u i) = lam • (fun i => u i) ∧
        Tendsto
          (fun n : Nat =>
            (∑ i, obs i * ((A ^ n) *ᵥ a) i ^ 2) /
              ∑ i, ((A ^ n) *ᵥ a) i ^ 2)
          atTop
          (nhds ((∑ i, obs i * (u i) ^ 2) /
            ∑ i, (u i) ^ 2)) := by
  obtain ⟨lam, hlam, u, hupos, hunorm, hueig, c, hc, hcoord⟩ :=
    positiveTransfer_normalized_mulVec_tendsto_apply A hHerm hpos a ha
  refine ⟨lam, hlam, u, hupos, hunorm, hueig, ?_⟩
  let x : Nat -> alpha -> Real := fun n i => ((A ^ n) *ᵥ a) i / lam ^ n
  let num : Nat -> Real := fun n => ∑ i, obs i * (x n i) ^ 2
  let den : Nat -> Real := fun n => ∑ i, (x n i) ^ 2
  let numLim : Real := c ^ 2 * ∑ i, obs i * (u i) ^ 2
  let denLim : Real := c ^ 2 * ∑ i, (u i) ^ 2
  have hx (i : alpha) : Tendsto (fun n => x n i) atTop (nhds (c * u i)) := by
    simpa only [x] using hcoord i
  have hnum : Tendsto num atTop (nhds numLim) := by
    have hsum : Tendsto num atTop
        (nhds (∑ i, obs i * (c * u i) ^ 2)) := by
      apply tendsto_finsetSum Finset.univ
      intro i hi
      exact ((hx i).pow 2).const_mul (obs i)
    have heq : (∑ i, obs i * (c * u i) ^ 2) = numLim := by
      dsimp [numLim]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq] at hsum
    exact hsum
  have hden : Tendsto den atTop (nhds denLim) := by
    have hsum : Tendsto den atTop (nhds (∑ i, (c * u i) ^ 2)) := by
      apply tendsto_finsetSum Finset.univ
      intro i hi
      exact (hx i).pow 2
    have heq : (∑ i, (c * u i) ^ 2) = denLim := by
      dsimp [denLim]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq] at hsum
    exact hsum
  have husq : 0 < ∑ i, (u i) ^ 2 := by
    apply Finset.sum_pos'
    · intro i hi
      positivity
    · let i : alpha := Classical.choice inferInstance
      exact ⟨i, Finset.mem_univ i, sq_pos_of_pos (hupos i)⟩
  have hdenLim : denLim ≠ 0 := (mul_pos (sq_pos_of_pos hc) husq).ne'
  have hratio := hnum.div hden hdenLim
  have hlimit : numLim / denLim =
      (∑ i, obs i * (u i) ^ 2) / ∑ i, (u i) ^ 2 := by
    dsimp [numLim, denLim]
    field_simp [hc.ne']
  rw [hlimit] at hratio
  apply hratio.congr'
  filter_upwards with n
  have hpow : lam ^ n ≠ 0 := pow_ne_zero n hlam.ne'
  dsimp [num, den, x]
  rw [show (∑ i, obs i * ((A ^ n) *ᵥ a) i ^ 2) =
      (lam ^ n) ^ 2 *
        ∑ i, obs i * (((A ^ n) *ᵥ a) i / lam ^ n) ^ 2 by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp,
    show (∑ i, ((A ^ n) *ᵥ a) i ^ 2) =
      (lam ^ n) ^ 2 * ∑ i, (((A ^ n) *ᵥ a) i / lam ^ n) ^ 2 by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp]
  field_simp

end

end StatMech.Ising
