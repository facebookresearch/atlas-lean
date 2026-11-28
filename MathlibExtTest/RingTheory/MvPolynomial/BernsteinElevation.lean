/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.MvPolynomial.BernsteinElevation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation

open MvPolynomial

-- Elevating a genuinely quadratic coordinate while retaining a second variable.
example (p : MvPolynomial (Fin 2) ℝ)
    (hp : p.degreeOf 0 ≤ 2) (k : Fin 2 → ℕ) :
    bernsteinCoeff (Function.update (fun _ : Fin 2 => 2) 0 3) p
        (Function.update k 0 2) =
      (2 / 3 : ℝ) * bernsteinCoeff (fun _ : Fin 2 => 2) p (Function.update k 0 1) +
      (1 / 3 : ℝ) * bernsteinCoeff (fun _ : Fin 2 => 2) p (Function.update k 0 2) := by
  convert bernsteinCoeff_elevate_succ (n := fun _ : Fin 2 => 2)
    (p := p) (r := 0) (k := k) (j := 1) hp (by decide) using 1
  norm_num

-- A zero degree coordinate can be elevated without changing either endpoint.
example (p : MvPolynomial (Fin 1) ℝ) :
    bernsteinCoeff (fun _ : Fin 1 => 1) p (fun _ => 0) =
      bernsteinCoeff (fun _ : Fin 1 => 0) p (fun _ => 0) := by
  have hu : Function.update (fun _ : Fin 1 => 0) 0 1 = fun _ => 1 := by
    ext i
    fin_cases i
    rfl
  simpa [hu] using bernsteinCoeff_elevate_zero
    (n := fun _ : Fin 1 => 0) (p := p) (r := 0) (k := fun _ => 0)

-- The upper endpoint drops the out-of-range old coefficient with weight zero.
example (p : MvPolynomial (Fin 2) ℝ) (hp : p.degreeOf 1 ≤ 3) (k : Fin 2 → ℕ) :
    bernsteinCoeff (Function.update (fun _ : Fin 2 => 3) 1 4) p
        (Function.update k 1 4) =
      bernsteinCoeff (fun _ : Fin 2 => 3) p (Function.update k 1 3) :=
  bernsteinCoeff_elevate_top k hp

-- A concrete mixed polynomial: x² - x + 7/20 + x*y.
private noncomputable def mixed : MvPolynomial (Fin 2) ℝ :=
  monomial (Finsupp.single 0 2) 1 + monomial (Finsupp.single 0 1) (-1) + C (7/20) +
    monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1

private theorem mixed_degree (i : Fin 2) : mixed.degreeOf i ≤ ![2, 1] i := by
  unfold mixed
  repeat apply (degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
  all_goals first
    | solve | simp
    | rw [degreeOf_monomial_eq _ _ (by norm_num)]
      fin_cases i <;> norm_num [Finsupp.single_apply]

-- All six original coefficients, including the negative interior one.
private theorem mixed_coeff (i : Fin 3) (j : Fin 2) :
    bernsteinCoeff ![2, 1] mixed ![i, j] =
      ![![7/20, 7/20], ![-3/20, 7/20], ![7/20, 27/20]] i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [mixed, bernsteinCoeff_add, bernsteinCoeff_monomial,
      Fin.prod_univ_two, Finsupp.single_apply, Nat.choose]

-- All eight elevated coefficients: the enclosure strictly improves.
private theorem mixed_elevated_coeff (i : Fin 4) (j : Fin 2) :
    bernsteinCoeff ![3, 1] mixed ![i, j] =
      ![![7/20, 7/20], ![1/60, 7/20], ![1/60, 41/60], ![7/20, 27/20]] i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [mixed, bernsteinCoeff_add, bernsteinCoeff_monomial,
      Fin.prod_univ_two, Finsupp.single_apply, Nat.choose]

-- Positivity becomes visible after a single elevation, while all coefficients
-- at the original degree were not positive.
example : bernsteinCoeff ![2, 1] mixed ![1, 0] < 0 := by
  have h := mixed_coeff (1 : Fin 3) (0 : Fin 2)
  norm_num at h
  rw [h]
  norm_num

example (x : Fin 2 → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 1) : 0 < eval x mixed := by
  apply eval_pos_of_bernsteinCoeff (n := ![3, 1])
    (fun i => (mixed_degree i).trans (by fin_cases i <;> norm_num)) hx
  intro k
  have heq : (fun i => (k i : ℕ)) = ![(k 0 : ℕ), (k 1 : ℕ)] := by
    ext i
    fin_cases i <;> rfl
  have hpos (i : Fin 4) (j : Fin 2) :
      0 < bernsteinCoeff ![3, 1] mixed ![i, j] := by
    rw [mixed_elevated_coeff i j]
    fin_cases i <;> fin_cases j <;> norm_num
  rw [heq]
  exact hpos (k 0) (k 1)

-- The elevated expansion is still the same polynomial, at every argument.
example : mixed = ∑ k : (i : Fin 2) → Fin (![3, 1] i + 1),
    C (bernsteinCoeff ![3, 1] mixed (fun i => k i)) *
      bernstein ![3, 1] (fun i => k i) :=
  eq_sum_bernstein (fun i => (mixed_degree i).trans (by fin_cases i <;> norm_num))

-- Arbitrarily large, unequal elevations retain an interval proved at degree (2,1).
example (m : Fin 2 → ℕ) (hm : ∀ i, ![2, 1] i ≤ m i)
    (k : Fin 2 → ℕ) (hk : ∀ i, k i ≤ m i) :
    bernsteinCoeff m mixed k ∈ Set.Icc (-3/20) (27/20) := by
  apply bernsteinCoeff_mem_Icc_of_le mixed_degree hm _ k hk
  intro l hl
  let i : Fin 3 := ⟨l 0, by have := hl 0; simp at this; omega⟩
  let j : Fin 2 := ⟨l 1, by have := hl 1; simp at this; omega⟩
  have heq : l = ![(i : ℕ), (j : ℕ)] := by
    ext a
    fin_cases a <;> rfl
  rw [heq, mixed_coeff i j]
  have hbound : ∀ (a : Fin 3) (b : Fin 2),
      ![![7/20, 7/20], ![-3/20, 7/20], ![7/20, 27/20]] a b ∈
        Set.Icc (-3/20 : ℝ) (27/20) := by
    intro a b
    fin_cases a <;> fin_cases b <;> norm_num [Set.mem_Icc]
  exact hbound i j

-- Empty variable types are supported by the iterated theorem.
example (p : MvPolynomial (Fin 0) ℝ) (n m k : Fin 0 → ℕ) (L U : ℝ)
    (hb : ∀ l, bernsteinCoeff n p l ∈ Set.Icc L U) :
    bernsteinCoeff m p k ∈ Set.Icc L U :=
  bernsteinCoeff_mem_Icc_of_le (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (fun l _ => hb l) k (fun i => Fin.elim0 i)

-- The degree hypothesis matters: the totalized conversion at degree zero
-- does not represent x, and elevation is not allowed to preserve its zero bounds.
example : bernsteinCoeff (fun _ : Fin 1 => 1) (monomial (Finsupp.single 0 1) 1)
    (fun _ => 1) ≠ bernsteinCoeff (fun _ : Fin 1 => 0)
      (monomial (Finsupp.single 0 1) 1) (fun _ => 0) := by
  norm_num [bernsteinCoeff_monomial, Fin.prod_univ_one, Finsupp.single_apply]

-- Affine pullbacks, including collapsed boxes, inherit degree elevation bounds.
example {n m : Fin 2 → ℕ} {p : MvPolynomial (Fin 2) ℝ} {L U : ℝ}
    (a b : Fin 2 → ℝ) (hp : ∀ i, p.degreeOf i ≤ n i) (hnm : ∀ i, n i ≤ m i)
    (hb : ∀ k, (∀ i, k i ≤ n i) → bernsteinCoeff n (boxPullback a b p) k ∈ Set.Icc L U)
    (k : Fin 2 → ℕ) (hk : ∀ i, k i ≤ m i) :
    bernsteinCoeff m (boxPullback a b p) k ∈ Set.Icc L U :=
  bernsteinCoeff_mem_Icc_of_le (fun i => (degreeOf_boxPullback_le a b p i).trans (hp i))
    hnm hb k hk

#print axioms MvPolynomial.bernsteinCoeff_elevate_succ
#print axioms MvPolynomial.bernsteinCoeff_mem_Icc_of_le
