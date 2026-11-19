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

/-- Two independent binary coordinates with different marginals:
the first is uniform and the second has weights `1/3, 2/3`.
The positive-sensitivity two-sided API handles this non-iid product. -/
example (f : (Fin 2 → Fin 2) → ℝ) (t : ℝ) (ht : 0 < t)
    (hbd : ∀ (i : Fin 2) (x y : Fin 2 → Fin 2),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ 1) :
    let p : Fin 2 → Fin 2 → ℝ :=
      fun i a => if i = 0 then 1 / 2 else if a = 0 then 1 / 3 else 2 / 3
    (∑ x ∈ Finset.univ.filter
        (fun x => t ≤ |f x - ∑ y, (∏ i, p i (y i)) * f y|),
        ∏ i, p i (x i)) ≤
      2 * Real.exp (-2 * t ^ 2 / ∑ _i : Fin 2, (1 : ℝ) ^ 2) := by
  dsimp only
  exact mcdiarmid_product_two_sided
    (fun i a => if i = 0 then 1 / 2 else if a = 0 then 1 / 3 else 2 / 3)
    (fun i a => by fin_cases i <;> fin_cases a <;> norm_num)
    (fun i => by fin_cases i <;> norm_num [Fin.sum_univ_two])
    f (fun _ => 1) (fun _ => by norm_num)
    (by norm_num [Fin.sum_univ_two]) t ht hbd

/-- Endpoint check: with zero sensitivities (`c = 0`) the upper tail of a
constant function is exactly `0`. -/
example (t : ℝ) (ht : 0 < t) :
    (∑ x ∈ Finset.univ.filter
        (fun x : (Fin 1 → Fin 2) => t ≤ (fun _ : Fin 1 → Fin 2 => (5 : ℝ)) x
          - ∑ y : (Fin 1 → Fin 2), (∏ i, (fun _a => (1 : ℝ) / 2) (y i)) * (fun _ => (5 : ℝ)) y),
        ∏ i, (fun _a => (1 : ℝ) / 2) (x i)) = 0 :=
  mcdiarmid_product_of_sum_sq_eq_zero (fun _i _a => 1 / 2) (fun _ _ => by norm_num)
    (fun _ => by norm_num [Finset.sum_const, Finset.card_univ]) (fun _ => (5 : ℝ))
    (fun _ => (0 : ℝ)) (by simp) t ht (fun _ _ _ _ => by simp)

/-- Endpoint check: the wrapper without the positivity hypothesis applies
at zero sensitivity, where the right-hand side is `Real.exp 0 = 1`. -/
example (t : ℝ) (ht : 0 < t) :
    (∑ x ∈ Finset.univ.filter
        (fun x : (Fin 1 → Fin 2) => t ≤ (fun _ : Fin 1 → Fin 2 => (5 : ℝ)) x
          - ∑ y : (Fin 1 → Fin 2), (∏ i, (fun _a => (1 : ℝ) / 2) (y i)) * (fun _ => (5 : ℝ)) y),
        ∏ i, (fun _a => (1 : ℝ) / 2) (x i)) ≤
      Real.exp (-2 * t ^ 2 / ∑ _i : Fin 1, (0 : ℝ) ^ 2) :=
  mcdiarmid_product_general (fun _i _a => 1 / 2) (fun _ _ => by norm_num)
    (fun _ => by norm_num [Finset.sum_const, Finset.card_univ]) (fun _ => (5 : ℝ))
    (fun _ => (0 : ℝ)) (fun _ => by norm_num) t ht (fun _ _ _ _ => by simp)

/-- Endpoint check: the two-sided wrapper without the positivity
hypothesis applies at zero sensitivity. -/
example (t : ℝ) (ht : 0 < t) :
    (∑ x ∈ Finset.univ.filter
        (fun x : (Fin 1 → Fin 2) => t ≤ |(fun _ : Fin 1 → Fin 2 => (5 : ℝ)) x
          - ∑ y : (Fin 1 → Fin 2), (∏ i, (fun _a => (1 : ℝ) / 2) (y i)) * (fun _ => (5 : ℝ)) y|),
        ∏ i, (fun _a => (1 : ℝ) / 2) (x i)) ≤
      2 * Real.exp (-2 * t ^ 2 / ∑ _i : Fin 1, (0 : ℝ) ^ 2) :=
  mcdiarmid_product_two_sided_general (fun _i _a => 1 / 2) (fun _ _ => by norm_num)
    (fun _ => by norm_num [Finset.sum_const, Finset.card_univ]) (fun _ => (5 : ℝ))
    (fun _ => (0 : ℝ)) (fun _ => by norm_num) t ht (fun _ _ _ _ => by simp)
