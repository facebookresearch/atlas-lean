/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKMedialLoopTurningFiber

open Finset

namespace StatMech.FrontierD

noncomputable section


def forcedBoolModeSum {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (S : Finset alpha) (forced : alpha -> Bool)
    (f : alpha -> Bool -> Real) : Real :=
  ∑ mode : alpha -> Bool,
    if forall x, x ∈ S -> mode x = forced x then
      ∏ x, f x (mode x)
    else 0



theorem forcedBoolModeSum_eq_product {alpha : Type*} [Fintype alpha]
    [DecidableEq alpha] (S : Finset alpha) (forced : alpha -> Bool)
    (f : alpha -> Bool -> Real) :
    forcedBoolModeSum S forced f =
      ∏ x : alpha,
        if x ∈ S then f x (forced x) else f x false + f x true := by
  classical
  let g : alpha -> Bool -> Real := fun x b =>
    if x ∈ S then if b = forced x then f x b else 0 else f x b
  have hpoint (mode : alpha -> Bool) :
      (if forall x, x ∈ S -> mode x = forced x then
          ∏ x, f x (mode x)
        else 0) =
        ∏ x, g x (mode x) := by
    by_cases hmode : forall x, x ∈ S -> mode x = forced x
    · rw [if_pos hmode]
      apply Finset.prod_congr rfl
      intro x hx
      by_cases hxS : x ∈ S
      · simp [g, hxS, hmode x hxS]
      · simp [g, hxS]
    · rw [if_neg hmode]
      push Not at hmode
      obtain ⟨x, hxS, hxne⟩ := hmode
      symm
      apply (Finset.prod_eq_zero (Finset.mem_univ x))
      simp [g, hxS, hxne]
  unfold forcedBoolModeSum
  simp_rw [hpoint]
  rw [← Fintype.prod_sum]
  apply Finset.prod_congr rfl
  intro x hx
  rw [Fintype.sum_bool]
  by_cases hxS : x ∈ S
  · cases hforced : forced x <;> simp [g, hxS, hforced]
  · simp [g, hxS, add_comm]


theorem sum_boolMode_product_eq {alpha : Type*} [Fintype alpha]
    [DecidableEq alpha]
    (f : alpha -> Bool -> Real) :
    (∑ mode : alpha -> Bool, ∏ x, f x (mode x)) =
      ∏ x : alpha, (f x false + f x true) := by
  rw [← Fintype.prod_sum]
  apply Finset.prod_congr rfl
  intro x hx
  rw [Fintype.sum_bool]
  exact add_comm _ _




theorem sum_boolMode_product_le_pow_mul_forced
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (S : Finset alpha) (forced : alpha -> Bool)
    (f : alpha -> Bool -> Real) (K : Real)
    (hf : forall x b, 0 <= f x b)
    (hlocal : forall x, x ∈ S ->
      f x false + f x true <= K * f x (forced x)) :
    (∑ mode : alpha -> Bool, ∏ x, f x (mode x)) <=
      K ^ S.card * forcedBoolModeSum S forced f := by
  classical
  rw [sum_boolMode_product_eq, forcedBoolModeSum_eq_product]
  let a : alpha -> Real := fun x => f x false + f x true
  let b : alpha -> Real := fun x =>
    if x ∈ S then f x (forced x) else a x
  calc
    (∏ x : alpha, a x) <=
        ∏ x : alpha, if x ∈ S then K * f x (forced x) else a x := by
      apply Finset.prod_le_prod
      · intro x hx
        exact add_nonneg (hf x false) (hf x true)
      · intro x hx
        by_cases hxS : x ∈ S
        · simpa [hxS] using hlocal x hxS
        · simp [hxS]
    _ = K ^ S.card * ∏ x : alpha, b x := by
      rw [show (∏ x : alpha,
          if x ∈ S then K * f x (forced x) else a x) =
          (∏ x ∈ S, K * f x (forced x)) *
            ∏ x ∈ (Finset.univ.filter fun x : alpha => x ∉ S), a x by
        rw [Finset.prod_ite]
        simp]
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      unfold b
      rw [show (∏ x : alpha, if x ∈ S then f x (forced x) else a x) =
          (∏ x ∈ S, f x (forced x)) *
            ∏ x ∈ (Finset.univ.filter fun x : alpha => x ∉ S), a x by
        rw [Finset.prod_ite]
        simp]
      ring
    _ = K ^ S.card *
        ∏ x : alpha,
          if x ∈ S then f x (forced x) else f x false + f x true := by
      rfl

end

end StatMech.FrontierD
