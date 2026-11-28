/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.NumberTheory.ZetaValues
import MathlibExt.NumberTheory.MultipleZeta.OddSquareStrictSums

/-! # Tests for strictly nested sums of reciprocal odd squares -/

open MetaMathlibExt MultipleZeta

-- The empty tuple contributes exactly one term, with an empty product.
example :
    ∑' m : StrictDecreasingTuple 0, ∏ j, ((2 * ((m.1 j : ℕ) : ℝ) - 1) ^ 2)⁻¹ = 1 := by
  rw [tsum_eq_single StrictDecreasingTuple.empty]
  · simp
  · intro m hm
    exact (hm m.eq_empty).elim

-- Independently evaluate the depth-one sum by subtracting the even terms of the Basel series.
example :
    ∑' m : StrictDecreasingTuple 1, ∏ j, ((2 * ((m.1 j : ℕ) : ℝ) - 1) ^ 2)⁻¹ =
      Real.pi ^ 2 / 8 := by
  let e : ℕ ≃ StrictDecreasingTuple 1 :=
    { toFun := fun n => ⟨fun _ => n.succPNat, fun i j hij => by
        rw [Subsingleton.elim i j] at hij
        exact (lt_irrefl j hij).elim⟩
      invFun := fun m => (m.1 0).natPred
      left_inv := Nat.natPred_succPNat
      right_inv := fun m => Subtype.ext (funext fun j => by
        rw [Subsingleton.elim j 0]
        exact PNat.succPNat_natPred _) }
  let f (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2
  have he : HasSum (fun n : ℕ => f (2 * n)) ((1 / 4) * (Real.pi ^ 2 / 6)) := by
    refine (hasSum_zeta_two.mul_left (1 / 4)).congr_fun fun n => ?_
    simp only [f, Nat.cast_mul, Nat.cast_ofNat, mul_pow, one_div, mul_inv]
    norm_num
  have hi : Function.Injective (fun n : ℕ => 2 * n + 1) :=
    (add_left_injective 1).comp (mul_right_injective₀ (by decide))
  have ho : Summable (fun n : ℕ => f (2 * n + 1)) := hasSum_zeta_two.summable.comp_injective hi
  have h := (he.even_add_odd ho.hasSum).unique hasSum_zeta_two
  have hOdd : (∑' n : ℕ, f (2 * n + 1)) = Real.pi ^ 2 / 8 := by linarith
  rw [← e.tsum_eq, ← hOdd]
  refine tsum_congr fun n => ?_
  rw [Fin.prod_univ_one]
  change ((2 * ((n.succPNat : ℕ) : ℝ) - 1) ^ 2)⁻¹ = f (2 * n + 1)
  simp only [f, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_mul, one_div]
  congr 2
  ring

-- A concrete depth-two tuple pairs the odd squares 25 and 9, not 25 and 25.
example :
    ∃ m : StrictDecreasingTuple 2, m.1 0 = 3 ∧ m.1 1 = 2 ∧
      (∏ j, ((2 * ((m.1 j : ℕ) : ℝ) - 1) ^ 2)⁻¹) = (1 : ℝ) / 225 := by
  let m : StrictDecreasingTuple 2 := ⟨fun j => if j = 0 then 3 else 2, by decide⟩
  refine ⟨m, rfl, rfl, ?_⟩
  rw [Fin.prod_univ_two]
  change ((2 * (3 : ℝ) - 1) ^ 2)⁻¹ * ((2 * (2 : ℝ) - 1) ^ 2)⁻¹ = _
  norm_num

-- A client can use the public formula with no access to its private proof helpers.
example :
    ∑' m : StrictDecreasingTuple 2, ∏ j, ((2 * ((m.1 j : ℕ) : ℝ) - 1) ^ 2)⁻¹ =
      Real.pi ^ 4 / 384 := by
  rw [tsum_strictDecreasing_prod_inv_odd_sq_eq]
  norm_num [Nat.factorial]
  ring
