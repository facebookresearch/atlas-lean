/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.SlepianWolf

open InformationTheory

/-- Boundary check: the second-coordinate chain rule instantiates
on a two-by-two joint law, in both bits and nats form, and the
binning average for `k = 2`, `M = 2` is `C(2, 2) / 2 = 1 / 2`. -/
example (p : PMF (Fin 2 × Fin 2)) :
    shannonEntropy p =
      shannonEntropy (p.map Prod.snd) +
        finiteConditionalEntropy (p.map (Equiv.prodComm (Fin 2) (Fin 2))) ∧
    shannonEntropy p * Real.log 2 =
      shannonEntropy (p.map Prod.snd) * Real.log 2 +
        finiteConditionalEntropy (p.map (Equiv.prodComm (Fin 2) (Fin 2))) * Real.log 2 ∧
    (∑ b : Fin 2 → Fin 2, binCollisions b) / (2 : ℝ) ^ 2 =
      ((Nat.choose 2 2 : ℝ)) / 2 :=
  ⟨shannonEntropy_eq_add_finiteConditionalEntropy_snd p,
    shannonEntropy_mul_log_two_eq_add_finiteConditionalEntropy_snd p, by
    have h := expected_bin_collisions (k := 2) (M := 2) (by norm_num)
    simpa using h⟩

/-- Binning check: for `k = 3`, `M = 2` the average number of
colliding pairs is `C(3, 2) / 2 = 3 / 2`. -/
example : (∑ b : Fin 3 → Fin 2, binCollisions b) / (2 : ℝ) ^ 3 =
    ((Nat.choose 3 2 : ℝ)) / 2 := by
  have h := expected_bin_collisions (k := 3) (M := 2) (by norm_num)
  simpa using h

/-- A constant two-item binning has exactly one colliding pair. -/
example : binCollisions (![0, 0] : Fin 2 → Fin 2) = 1 := by
  norm_num [binCollisions, ← Finset.univ_product_univ, Finset.univ_fin2]
  decide

/-- Distinct bins have no colliding pair. -/
example : binCollisions (![0, 1] : Fin 2 → Fin 2) = 0 := by
  norm_num [binCollisions, ← Finset.univ_product_univ, Finset.univ_fin2]

/-- Exhausting all four binnings gives the average without the general theorem. -/
example : (∑ b : Fin 2 → Fin 2, binCollisions b) / (2 : ℝ) ^ 2 = 1 / 2 := by
  have hcount : (∑ b : Fin 2 → Fin 2,
      (Finset.univ.filter (fun ij : Fin 2 × Fin 2 =>
        ij.1 < ij.2 ∧ b ij.1 = b ij.2)).card) = 2 := by decide
  norm_num [binCollisions, ← Nat.cast_sum, hcount]

/-- Empty binnings have zero collisions. -/
example : (∑ b : Fin 0 → Fin 2, binCollisions b) / (2 : ℝ) ^ 0 = 0 := by
  simp [binCollisions]

/-- A singleton cannot collide with another item. -/
example : (∑ b : Fin 1 → Fin 2, binCollisions b) / (2 : ℝ) ^ 1 = 0 := by
  norm_num [binCollisions, ← Nat.cast_sum]
