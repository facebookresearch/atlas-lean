/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.TracePowWalk



















namespace StatMech.Onsager

open Matrix BigOperators



noncomputable def ons_loopWeight {E : Type*} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    {n : ℕ} [NeZero n] (v : Fin n → E) : ℂ := ∏ k : Fin n, Λ (v k) (v (k + 1))



def ons_cyclicShift {E : Type*} {n : ℕ} [NeZero n] (v : Fin n → E) : Fin n → E :=
  fun k => v (k + 1)



theorem ons_loopWeight_cyclicShift {E} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    {n : ℕ} [NeZero n] (v : Fin n → E) :
    ons_loopWeight Λ (ons_cyclicShift v) = ons_loopWeight Λ v := by
  unfold ons_loopWeight ons_cyclicShift
  exact Equiv.prod_comp (Equiv.addRight (1 : Fin n)) (fun k => Λ (v k) (v (k + 1)))




theorem ons_trace_pow_eq_loopWeight_sum {E} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    (n : ℕ) [NeZero n] (hn : 0 < n) :
    (Λ ^ n).trace = ∑ v : Fin n → E, ons_loopWeight Λ v := by
  unfold ons_loopWeight
  exact ons_trace_pow_eq_walk_sum Λ n hn



theorem ons_loopWeight_cyclicShift_iterate {E} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    {n : ℕ} [NeZero n] (v : Fin n → E) (j : ℕ) :
    ons_loopWeight Λ (ons_cyclicShift^[j] v) = ons_loopWeight Λ v := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ons_loopWeight_cyclicShift, ih]

end StatMech.Onsager
