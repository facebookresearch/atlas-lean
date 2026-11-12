/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Concentration.BoundedDifferences

/-- Boundary check: the one-sided statement for a single coordinate
(binary alphabet, uniform weights) has the stated shape. -/
example (f : (Fin 1 → Fin 2) → ℝ) (t : ℝ) (ht : 0 < t)
    (hbd : ∀ (i : Fin 1) (x y : Fin 1 → Fin 2),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ 1) :
    (∑ x ∈ Finset.univ.filter
        (fun x => t ≤ f x - ∑ y, (∏ i, (fun _a => (1 : ℝ) / 2) (y i)) * f y),
        ∏ i, (fun _a => (1 : ℝ) / 2) (x i)) ≤
      Real.exp (-2 * t ^ 2 / ∑ _i : Fin 1, (1 : ℝ) ^ 2) :=
  mcdiarmid_product (fun _i _a => 1 / 2) (fun _ _ => by norm_num)
    (fun _ => by norm_num [Finset.sum_const, Finset.card_univ]) f (fun _ => 1)
    (fun _ => by norm_num) (by norm_num) t ht hbd
