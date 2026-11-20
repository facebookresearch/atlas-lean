/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Ising.PressureBCIndep

open scoped BigOperators
open Finset

namespace StatMech.Ising

open StatMech.Lattice

variable {d : ℕ}



def interfaceField (i : Fin d) : ConfigSpace (Site d) :=
  fun x => decide (0 ≤ x i)

@[simp] theorem interfaceField_apply (i : Fin d) (x : Site d) :
    interfaceField i x = decide (0 ≤ x i) := rfl



noncomputable def finiteInterfaceFreeEnergy
    (i : Fin d) (n : ℕ) (beta : ℝ) : ℝ :=
  Real.log (fvZ (plusField d) n (bondFinsetTouch d n) beta 0) -
    Real.log (fvZ (interfaceField i) n (bondFinsetTouch d n) beta 0)



noncomputable def fvMeanNegEnergy
    (eta : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (beta h : ℝ) : ℝ :=
  (∑ tau : {x // x ∈ box d n} → Bool,
      fvWeight eta n B beta h tau * (-fvEnergy eta n B h tau)) /
    fvZ eta n B beta h



theorem fvMeanNegEnergy_eq_sum_prob
    (eta : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (beta h : ℝ) :
    fvMeanNegEnergy eta n B beta h =
      ∑ tau : {x // x ∈ box d n} → Bool,
        fvProb eta n B beta h tau * (-fvEnergy eta n B h tau) := by
  unfold fvMeanNegEnergy fvProb
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro tau _
  ring



theorem hasDerivAt_fvWeight_beta
    (eta : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (beta h : ℝ)
    (tau : {x // x ∈ box d n} → Bool) :
    HasDerivAt (fun b => fvWeight eta n B b h tau)
      (fvWeight eta n B beta h tau * (-fvEnergy eta n B h tau)) beta := by
  unfold fvWeight
  convert (Real.hasDerivAt_exp (-beta * fvEnergy eta n B h tau)).comp beta
      ((hasDerivAt_id beta).neg.mul_const (fvEnergy eta n B h tau)) using 1
  all_goals ring


theorem hasDerivAt_fvZ_beta
    (eta : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (beta h : ℝ) :
    HasDerivAt (fun b => fvZ eta n B b h)
      (∑ tau : {x // x ∈ box d n} → Bool,
        fvWeight eta n B beta h tau * (-fvEnergy eta n B h tau)) beta := by
  unfold fvZ
  simpa using
    (HasDerivAt.fun_sum (u := Finset.univ)
      (fun tau _ => hasDerivAt_fvWeight_beta eta n B beta h tau))



theorem hasDerivAt_log_fvZ_beta
    (eta : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (beta h : ℝ) :
    HasDerivAt (fun b => Real.log (fvZ eta n B b h))
      (fvMeanNegEnergy eta n B beta h) beta := by
  exact (hasDerivAt_fvZ_beta eta n B beta h).log
    (fvZ_ne_zero eta n B beta h)



theorem hasDerivAt_finiteInterfaceFreeEnergy
    (i : Fin d) (n : ℕ) (beta : ℝ) :
    HasDerivAt (finiteInterfaceFreeEnergy i n)
      (fvMeanNegEnergy (plusField d) n (bondFinsetTouch d n) beta 0 -
        fvMeanNegEnergy (interfaceField i) n (bondFinsetTouch d n) beta 0) beta := by
  exact (hasDerivAt_log_fvZ_beta (plusField d) n (bondFinsetTouch d n) beta 0).sub
    (hasDerivAt_log_fvZ_beta (interfaceField i) n (bondFinsetTouch d n) beta 0)



@[simp] theorem finiteInterfaceFreeEnergy_zero (i : Fin d) (n : ℕ) :
    finiteInterfaceFreeEnergy i n 0 = 0 := by
  simp [finiteInterfaceFreeEnergy, fvZ, fvWeight]



theorem boundary_free_logFvZ_sub_abs_le
    (eta : ConfigSpace (Site d)) (n : ℕ) (beta h : ℝ) :
    |Real.log (fvZ eta n (bondFinsetTouch d n) beta h) -
        Real.log (fvZ (minusField d) n (bondFinsetInternal d n) beta h)|
      ≤ |beta| * ((bondFinsetTouch d n) \ (bondFinsetInternal d n)).card :=
  logFvZ_sub_abs_le eta (minusField d) n
    (bondFinsetTouch d n) (bondFinsetInternal d n) beta h
    (bondFinsetInternal_subset_touch n)
    (fun tau _e he => bond_internal_indep eta (minusField d) n tau he)



theorem finiteInterfaceFreeEnergy_abs_le
    (i : Fin d) (n : ℕ) (beta : ℝ) :
    |finiteInterfaceFreeEnergy i n beta| ≤
      2 * |beta| * ((bondFinsetTouch d n) \ (bondFinsetInternal d n)).card := by
  let freeLog :=
    Real.log (fvZ (minusField d) n (bondFinsetInternal d n) beta 0)
  have hplus := boundary_free_logFvZ_sub_abs_le (plusField d) n beta 0
  have hmix := boundary_free_logFvZ_sub_abs_le (interfaceField i) n beta 0
  change |Real.log (fvZ (plusField d) n (bondFinsetTouch d n) beta 0) -
      Real.log (fvZ (interfaceField i) n (bondFinsetTouch d n) beta 0)| ≤ _
  calc
    |Real.log (fvZ (plusField d) n (bondFinsetTouch d n) beta 0) -
        Real.log (fvZ (interfaceField i) n (bondFinsetTouch d n) beta 0)|
        ≤ |Real.log (fvZ (plusField d) n (bondFinsetTouch d n) beta 0) - freeLog| +
          |freeLog - Real.log (fvZ (interfaceField i) n (bondFinsetTouch d n) beta 0)| :=
            abs_sub_le _ _ _
    _ ≤ |beta| * ((bondFinsetTouch d n) \ (bondFinsetInternal d n)).card +
          |beta| * ((bondFinsetTouch d n) \ (bondFinsetInternal d n)).card := by
        apply add_le_add
        · simpa [freeLog] using hplus
        · simpa [freeLog, abs_sub_comm] using hmix
    _ = 2 * |beta| * ((bondFinsetTouch d n) \ (bondFinsetInternal d n)).card := by ring

end StatMech.Ising
