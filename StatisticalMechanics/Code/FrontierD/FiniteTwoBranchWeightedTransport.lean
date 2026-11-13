/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib

open Finset

namespace StatMech.FrontierD

noncomputable section



theorem fintype_sum_comp_le_sum_of_injective
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    (map : Source -> Target) (hinjective : Function.Injective map)
    (weight : Target -> Real) (hnonneg : forall target, 0 <= weight target) :
    (∑ source, weight (map source)) <= ∑ target, weight target := by
  classical
  calc
    (∑ source, weight (map source)) =
        ∑ target ∈ Finset.image map Finset.univ, weight target := by
      rw [Finset.sum_image hinjective.injOn]
    _ <= ∑ target ∈ Finset.univ, weight target := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (by simp)
        (fun target _ _ => hnonneg target)
    _ = ∑ target, weight target := rfl



theorem fintype_sum_le_of_twoBranchWeight
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    (branch : Bool -> Source -> Target)
    (hinjective : forall choice, Function.Injective (branch choice))
    (sourceWeight : Source -> Real) (targetWeight : Target -> Real)
    (htargetNonneg : forall target, 0 <= targetWeight target)
    (hlocal : forall source,
      2 * sourceWeight source <=
        targetWeight (branch false source) +
          targetWeight (branch true source)) :
    (∑ source, sourceWeight source) <= ∑ target, targetWeight target := by
  have hfalse := fintype_sum_comp_le_sum_of_injective
    (branch false) (hinjective false) targetWeight htargetNonneg
  have htrue := fintype_sum_comp_le_sum_of_injective
    (branch true) (hinjective true) targetWeight htargetNonneg
  have hsum :
      2 * (∑ source, sourceWeight source) <=
        (∑ source, targetWeight (branch false source)) +
          (∑ source, targetWeight (branch true source)) := by
    calc
      2 * (∑ source, sourceWeight source) =
          ∑ source, 2 * sourceWeight source := by
        rw [Finset.mul_sum]
      _ <= ∑ source,
          (targetWeight (branch false source) +
            targetWeight (branch true source)) :=
        Finset.sum_le_sum (fun source _ => hlocal source)
      _ = (∑ source, targetWeight (branch false source)) +
          (∑ source, targetWeight (branch true source)) :=
        Finset.sum_add_distrib
  linarith


theorem two_mul_le_add_of_sq_le_mul
    {x y z : Real} (hx : 0 <= x) (hy : 0 <= y) (hz : 0 <= z)
    (hprod : z ^ 2 <= x * y) :
    2 * z <= x + y := by
  have hamgm : 2 * x * y <= x ^ 2 + y ^ 2 := two_mul_le_add_sq x y
  have hsquares : (2 * z) ^ 2 <= (x + y) ^ 2 := by
    nlinarith
  exact (sq_le_sq₀ (by positivity) (add_nonneg hx hy)).mp hsquares




theorem two_mul_pow_le_pow_add_pow_of_twice_le_add
    {c : Real} (hc : 1 <= c) {source first second : Nat}
    (hgrade : 2 * source <= first + second) :
    2 * c ^ source <= c ^ first + c ^ second := by
  have hpow : c ^ (2 * source) <= c ^ (first + second) :=
    pow_le_pow_right₀ hc hgrade
  have hprod : (c ^ source) ^ 2 <= c ^ first * c ^ second := by
    simpa [pow_add, pow_mul, mul_comm] using hpow
  exact two_mul_le_add_of_sq_le_mul (pow_nonneg (by linarith) _)
    (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _) hprod

end

end StatMech.FrontierD
