/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GeneralizedEulerianGamma

open MetaMathlibExt

-- The empty permutation contributes one, including when its cycle weight is zero.
example (q t : ℚ) : generalizedEulerianP q t (-1) 1 0 = 1 := by
  have h := (generalizedEulerianP_neg_one q t 0).2.1
  simpa [Finset.univ_unique, cycleQuotientCount_eq, excedanceCount] using h

-- The four-cycle 0 → 1 → 2 → 3 → 0 occurs with a negative integer exponent.
example : (2 : ℤ) - excedanceCount 4 (finRotate 4) = -1 ∧
    doubleExcedanceCount (finRotate 4) = 2 := by decide

-- Of the nine derangements on four points, five contribute to the unsigned sum.
example (t : ℚ) : generalizedEulerianP 1 t (-1) 1 4 = 5 := by
  have h := (generalizedEulerianP_neg_one 1 t 2).2
  have hc : (Finset.univ.filter (fun w : Equiv.Perm (Fin 4) ↦
      Fintype.card (Function.fixedPoints w) = 0 ∧ excedanceCount 4 w = 2 ∧
        doubleExcedanceCount w = 0)).card = 5 := by decide
  simp at hc
  simpa [hc] using h.1.trans h.2

-- The empty permutation has weight one, even when a parameter vanishes.
example (q t x y : ℚ) (hxy : x ≠ y) : generalizedEulerianP q t x y 0 = 1 := by
  rw [generalizedEulerianP_eq_sum_perm q t x y hxy]
  simp [Finset.univ_unique, cycleQuotientCount_eq, excedanceCount]

-- A singleton contributes both a cycle and a fixed point, but neither kind of excedance.
example (q t x y : ℚ) (hxy : x ≠ y) : generalizedEulerianP q t x y 1 = q * t * (x + y) := by
  rw [generalizedEulerianP_eq_sum_perm (q := q) (t := t) (x := x) (y := y) (hxy := hxy) (n := 1)]
  have hOne : (default : Equiv.Perm (Fin 1)) = 1 := Subsingleton.elim _ _
  have hfix : Fintype.card (Function.fixedPoints (1 : Equiv.Perm (Fin 1))) = 1 := by decide
  simp only [Finset.univ_unique, Finset.sum_singleton, hOne, cycleQuotientCount_eq, hfix]
  have he : excedanceCount 1 (1 : Equiv.Perm (Fin 1)) = 0 := by decide
  simp [he]

private def permThree (i : Fin 3) (j : Fin 2) : Equiv.Perm (Fin 3) :=
  Equiv.Perm.decomposeFin.symm (i, Equiv.Perm.decomposeFin.symm (j, 1))

private lemma sum_perm_three (f : Equiv.Perm (Fin 3) → ℚ) :
    ∑ w, f w = ∑ i : Fin 3, ∑ j : Fin 2, f (permThree i j) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp f, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp
      (fun w : Equiv.Perm (Fin 2) ↦ f (Equiv.Perm.decomposeFin.symm (i, w))), Fintype.sum_prod_type]
  simp only [Finset.univ_unique, Finset.sum_singleton,
    Subsingleton.elim (default : Equiv.Perm (Fin 1)) 1, permThree]

private noncomputable def stats (w : Equiv.Perm (Fin 3)) : ℕ × ℕ × ℕ × ℕ :=
  (cycleQuotientCount w, Fintype.card (Function.fixedPoints w),
    excedanceCount 3 w, excedanceCount 3 w⁻¹)

private lemma cycles_insert {n : ℕ} (p : Fin (n + 1)) (w : Equiv.Perm (Fin n)) :
    cycleQuotientCount (Equiv.Perm.decomposeFin.symm (p, w)) =
      cycleQuotientCount w + if p = 0 then 1 else 0 := by
  refine Fin.cases ?_ (fun j ↦ ?_) p
  · simp [cycleQuotientCount_decomposeFin_zero]
  · simp [cycleQuotientCount_decomposeFin_succ]

private lemma stats_permThree (i : Fin 3) (j : Fin 2) :
    stats (permThree i j) = if i = 0 ∧ j = 0 then (3, 3, 0, 0)
      else if i = 0 ∨ j = 0 then (2, 1, 1, 1)
      else if i = 1 then (1, 0, 2, 1) else (1, 0, 1, 2) := by
  have h : cycleQuotientCount (1 : Equiv.Perm (Fin 1)) = 1 := by
    rw [cycleQuotientCount_eq, Equiv.Perm.cycleType_one]
    decide
  have hcycle : cycleQuotientCount (permThree i j) =
      (1 + if j = 0 then 1 else 0) + if i = 0 then 1 else 0 := by
    rw [permThree, cycles_insert, cycles_insert, h]
  rw [stats, hcycle]
  clear hcycle
  revert i j
  decide

-- The identity, the three transpositions with one fixed point, and the two three-cycles.
private lemma value_three (q t x y : ℚ) (hxy : x ≠ y) :
    generalizedEulerianP q t x y 3 = (q * t * (x + y)) ^ 3 +
      3 * q ^ 2 * t * (x + y) * x * y + q * x * y * (x + y) := by
  rw [generalizedEulerianP_eq_sum_perm q t x y hxy, sum_perm_three]
  let wt : ℕ × ℕ × ℕ × ℕ → ℚ := fun (c, f, a, b) ↦
    q ^ c * t ^ f * x ^ a * y ^ b * (x + y) ^ f
  change ∑ i : Fin 3, ∑ j : Fin 2, wt (stats (permThree i j)) = _
  simp_rw [stats_permThree, Fin.sum_univ_three, Fin.sum_univ_two]
  norm_num [wt]
  ring

example : generalizedEulerianP (-1 / 2) (1 / 3) 2 (-1 / 2) 3 = 23 / 64 := by
  norm_num [value_three]

-- With zero rise weight, the identity is the only surviving permutation.
example : generalizedEulerianP (2 / 3) (-5 / 2) 0 (3 / 5) 3 = -1 := by
  norm_num [value_three]
