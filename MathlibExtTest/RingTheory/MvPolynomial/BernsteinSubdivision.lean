/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.MvPolynomial.BernsteinSubdivision
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

open MvPolynomial

example : bernsteinSubdivideLeft (0 : Fin 2) (1/2)
    (fun k => (k 0 : ℝ)^2 + k 1) ![2, 1] = 5/2 := by
  norm_num [bernsteinSubdivideLeft, bernsteinPolynomial.deCasteljau, Function.update]

example : bernsteinSubdivideRight ![2, 1] (0 : Fin 2) (1/2)
    (fun k => (k 0 : ℝ)^2 + k 1) ![1, 0] = 5/2 := by
  norm_num [bernsteinSubdivideRight, bernsteinPolynomial.deCasteljau, Function.update]

-- Complete degree-(2,1) child tables, including the untouched second coordinate.
example (i : Fin 3) (j : Fin 2) :
    bernsteinSubdivideLeft (0 : Fin 2) (1/2) (fun k => (k 0 : ℝ)^2 + k 1) ![i, j] =
      (![0, 1/2, 3/2] i) + j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [bernsteinSubdivideLeft, bernsteinPolynomial.deCasteljau, Function.update]

example (i : Fin 3) (j : Fin 2) :
    bernsteinSubdivideRight ![2, 1] (0 : Fin 2) (1/2) (fun k => (k 0 : ℝ)^2 + k 1)
      ![i, j] = (![3/2, 5/2, 4] i) + j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [bernsteinSubdivideRight, bernsteinPolynomial.deCasteljau, Function.update]

-- A zero-degree coordinate has identical children for every cut, even outside [0,1].
example (t : ℝ) (c : (Fin 2 → ℕ) → ℝ) :
    bernsteinSubdivideLeft 0 t c ![0, 2] = c ![0, 2] ∧
    bernsteinSubdivideRight ![0, 3] 0 t c ![0, 2] = c ![0, 2] := by
  norm_num [bernsteinSubdivideLeft, bernsteinSubdivideRight, bernsteinPolynomial.deCasteljau]
  congr 1
  ext i
  fin_cases i <;> simp [Function.update]

-- Empty variable types still admit expansion and enclosure.
example (c : (Fin 0 → ℕ) → ℝ) {L U : ℝ}
    (hc : ∀ k, c k ∈ Set.Icc L U) :
    eval (fun i => Fin.elim0 i) (bernsteinExpansion (fun i => Fin.elim0 i) c) ∈
      Set.Icc L U := by
  apply eval_bernsteinExpansion_mem_Icc (fun i => Fin.elim0 i)
  exact fun k _ => hc k

-- Parent coverage includes a collapsed second coordinate and a midpoint first cut.
example : Set.Icc (![2, 7] : Fin 2 → ℝ) ![6, 7] =
    Set.Icc ![2, 7] ![4, 7] ∪ Set.Icc ![4, 7] ![6, 7] := by
  convert Set.Icc_eq_union_update (![2, 7] : Fin 2 → ℝ) ![6, 7] 0
    (m := 4) (by norm_num) using 1
  congr 2 <;> ext i <;> fin_cases i <;> norm_num [Function.update]

-- Parent-to-child enclosure is exercised at an asymmetric cut, then fed
-- directly into evaluation on the unit cube for both child polynomials.
example (x : Fin 2 → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 1) :
    eval x (bernsteinExpansion ![2, 1] (bernsteinSubdivideLeft 0 (1/3)
      (fun k => (k 0 : ℝ)^2 + k 1))) ∈ Set.Icc 0 5 ∧
    eval x (bernsteinExpansion ![2, 1] (bernsteinSubdivideRight ![2, 1] 0 (1/3)
      (fun k => (k 0 : ℝ)^2 + k 1))) ∈ Set.Icc 0 5 := by
  have hc (k : Fin 2 → ℕ) (hk : ∀ i, k i ≤ ![2, 1] i) :
      (k 0 : ℝ)^2 + k 1 ∈ Set.Icc (0 : ℝ) 5 := by
    have h0 : k 0 ≤ 2 := hk 0
    have h1 : k 1 ≤ 1 := hk 1
    interval_cases h : k 0 <;> interval_cases h' : k 1 <;> norm_num
  have hrep (q : MvPolynomial (Fin 2) ℝ) :
      q = boxPullback (fun _ => 0) (fun _ => 1) q := by
    simp [boxPullback]
  constructor
  · exact eval_mem_Icc_of_bernsteinExpansion_box (hrep _) hx
      (bernsteinSubdivideLeft_mem_Icc (by norm_num) hc)
  · exact eval_mem_Icc_of_bernsteinExpansion_box (hrep _) hx
      (bernsteinSubdivideRight_mem_Icc (by norm_num) hc)

-- Full pipeline on a shifted box with one collapsed coordinate: reconstruct
-- each child from the parent's canonical coefficients, then bound actual values.
example (p : MvPolynomial (Fin 2) ℝ) (hp : ∀ i, p.degreeOf i ≤ ![2, 1] i)
    (x : Fin 2 → ℝ) (hx : ∀ i, x i ∈ Set.Icc (![2, 7] i) (![4, 7] i))
    (hc : ∀ k, (∀ i, k i ≤ ![2, 1] i) →
      bernsteinSubdivideLeft 0 (1/2)
        (bernsteinCoeff ![2, 1] (boxPullback ![2, 7] ![6, 7] p)) k ∈ Set.Icc (-3) 5) :
    eval x p ∈ Set.Icc (-3) 5 := by
  have hrep := bernsteinExpansion_subdivideLeft_box hp ![2, 7] ![6, 7] 0 (1/2)
  have hcut : Function.update (![6, 7] : Fin 2 → ℝ) 0 4 = ![4, 7] := by
    ext i
    fin_cases i <;> norm_num [Function.update]
  norm_num only [Matrix.cons_val_zero] at hrep
  rw [hcut] at hrep
  exact eval_mem_Icc_of_bernsteinExpansion_box hrep hx hc

example (p : MvPolynomial (Fin 2) ℝ) (hp : ∀ i, p.degreeOf i ≤ ![2, 1] i)
    (x : Fin 2 → ℝ) (hx : ∀ i, x i ∈ Set.Icc (![4, 7] i) (![6, 7] i))
    (hc : ∀ k, (∀ i, k i ≤ ![2, 1] i) →
      bernsteinSubdivideRight ![2, 1] 0 (1/2)
        (bernsteinCoeff ![2, 1] (boxPullback ![2, 7] ![6, 7] p)) k ∈ Set.Icc (-2) 6) :
    eval x p ∈ Set.Icc (-2) 6 := by
  have hrep := bernsteinExpansion_subdivideRight_box hp ![2, 7] ![6, 7] 0 (1/2)
  have hcut : Function.update (![2, 7] : Fin 2 → ℝ) 0 4 = ![4, 7] := by
    ext i
    fin_cases i <;> norm_num [Function.update]
  norm_num only [Matrix.cons_val_zero] at hrep
  rw [hcut] at hrep
  exact eval_mem_Icc_of_bernsteinExpansion_box hrep hx hc

#print axioms bernsteinExpansion_subdivideLeft_box
#print axioms bernsteinExpansion_subdivideRight_box
#print axioms eval_mem_Icc_of_bernsteinExpansion_box
#print axioms Set.Icc_eq_union_update
