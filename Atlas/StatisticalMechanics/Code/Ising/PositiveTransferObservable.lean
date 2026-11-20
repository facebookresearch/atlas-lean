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




theorem positiveTransfer_endpointObservable_tendsto
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hpos : forall i j, 0 < A i j)
    (a ell : alpha -> Real) (ha : forall i, 0 < a i)
    (hell : forall i, 0 < ell i) (obs : alpha -> Real) :
    exists lam : Real, 0 < lam ∧
      exists u : EuclideanSpace Real alpha,
        (forall i, 0 < u i) ∧ norm u = 1 ∧
        A *ᵥ (fun i => u i) = lam • (fun i => u i) ∧
        Tendsto
          (fun n : Nat =>
            (∑ i, ell i * obs i * ((A ^ n) *ᵥ a) i) /
              ∑ i, ell i * ((A ^ n) *ᵥ a) i)
          atTop
          (nhds ((∑ i, ell i * obs i * u i) /
            ∑ i, ell i * u i)) := by
  obtain ⟨lam, hlam, u, hupos, hunorm, hueig, c, hc, hcoord⟩ :=
    positiveTransfer_normalized_mulVec_tendsto_apply A hHerm hpos a ha
  refine ⟨lam, hlam, u, hupos, hunorm, hueig, ?_⟩
  let num : Nat -> Real := fun n =>
    ∑ i, ell i * obs i * (((A ^ n) *ᵥ a) i / lam ^ n)
  let den : Nat -> Real := fun n =>
    ∑ i, ell i * (((A ^ n) *ᵥ a) i / lam ^ n)
  let numLim : Real := c * ∑ i, ell i * obs i * u i
  let denLim : Real := c * ∑ i, ell i * u i
  have hnum : Tendsto num atTop (nhds numLim) := by
    have hsum : Tendsto num atTop
        (nhds (∑ i, ell i * obs i * (c * u i))) := by
      apply tendsto_finsetSum Finset.univ
      intro i hi
      exact (hcoord i).const_mul (ell i * obs i)
    have heq : (∑ i, ell i * obs i * (c * u i)) = numLim := by
      dsimp [numLim]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq] at hsum
    exact hsum
  have hden : Tendsto den atTop (nhds denLim) := by
    have hsum : Tendsto den atTop
        (nhds (∑ i, ell i * (c * u i))) := by
      apply tendsto_finsetSum Finset.univ
      intro i hi
      exact (hcoord i).const_mul (ell i)
    have heq : (∑ i, ell i * (c * u i)) = denLim := by
      dsimp [denLim]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq] at hsum
    exact hsum
  have hsumpos : 0 < ∑ i, ell i * u i := by
    apply Finset.sum_pos'
    · intro i hi
      exact (mul_pos (hell i) (hupos i)).le
    · let i : alpha := Classical.choice inferInstance
      exact ⟨i, Finset.mem_univ i, mul_pos (hell i) (hupos i)⟩
  have hdenLim : denLim ≠ 0 := (mul_pos hc hsumpos).ne'
  have hratio : Tendsto (fun n => num n / den n) atTop
      (nhds (numLim / denLim)) := hnum.div hden hdenLim
  have hlimit : numLim / denLim =
      (∑ i, ell i * obs i * u i) / ∑ i, ell i * u i := by
    dsimp [numLim, denLim]
    field_simp [hc.ne']
  rw [hlimit] at hratio
  apply hratio.congr'
  filter_upwards with n
  have hpow : lam ^ n ≠ 0 := pow_ne_zero n hlam.ne'
  dsimp [num, den]
  rw [show (∑ i, ell i * obs i * ((A ^ n) *ᵥ a) i) =
      lam ^ n *
        ∑ i, ell i * obs i * (((A ^ n) *ᵥ a) i / lam ^ n) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp,
    show (∑ i, ell i * ((A ^ n) *ᵥ a) i) =
      lam ^ n *
        ∑ i, ell i * (((A ^ n) *ᵥ a) i / lam ^ n) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp]
  field_simp



theorem positiveTransfer_twoBoundary_endpointObservable_common
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hpos : forall i j, 0 < A i j)
    (a b ell : alpha -> Real)
    (ha : forall i, 0 < a i) (hb : forall i, 0 < b i)
    (hell : forall i, 0 < ell i) (obs : alpha -> Real) :
    exists m : Real,
      Tendsto
        (fun n : Nat =>
          (∑ i, ell i * obs i * ((A ^ n) *ᵥ a) i) /
            ∑ i, ell i * ((A ^ n) *ᵥ a) i)
        atTop (nhds m) ∧
      Tendsto
        (fun n : Nat =>
          (∑ i, ell i * obs i * ((A ^ n) *ᵥ b) i) /
            ∑ i, ell i * ((A ^ n) *ᵥ b) i)
        atTop (nhds m) := by
  obtain ⟨lamA, hlamA, u, hupos, hunorm, hueig, hlimA⟩ :=
    positiveTransfer_endpointObservable_tendsto
      A hHerm hpos a ell ha hell obs
  obtain ⟨lamB, hlamB, v, hvpos, hvnorm, hveig, hlimB⟩ :=
    positiveTransfer_endpointObservable_tendsto
      A hHerm hpos b ell hb hell obs
  have huv : u = v := positiveTransfer_positive_unit_eigenvector_unique
    A hHerm hpos hupos hvpos hunorm hvnorm hueig hveig
  let m : Real := (∑ i, ell i * obs i * u i) / ∑ i, ell i * u i
  refine ⟨m, ?_, ?_⟩
  · exact hlimA
  · rw [← huv] at hlimB
    exact hlimB

end

end StatMech.Ising
