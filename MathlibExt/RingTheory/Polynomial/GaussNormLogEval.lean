/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Polynomial_log_abv_eval_eq_log_gaussNorm_add_sum.lean`
and
`P2M/Sol/S_Polynomial_log_abv_eval_eq_log_gaussNorm_add_sum.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Polynomial.GaussNorm

import Mathlib.Algebra.Order.Ring.IsNonarchimedean

@[expose] public section

namespace Polynomial

private theorem gaussNorm_one_X_sub_C_aux {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (a : K) :
    (X - C a).gaussNorm v 1 = max 1 (v a) := by
  have hc1 : (X - C a : K[X]).coeff 1 = 1 := by
    rw [coeff_sub, coeff_X_one, coeff_C_succ, sub_zero]
  have hc0 : (X - C a : K[X]).coeff 0 = -a := by
    rw [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
  apply le_antisymm
  · have h := isNonarchimedean_gaussNorm v hv zero_le_one (X : K[X]) (-C a)
    rw [sub_eq_add_neg]
    refine h.trans (le_of_eq ?_)
    rw [← C_neg, gaussNorm_C, ← monomial_one_one_eq_X, gaussNorm_monomial]
    simp
  · apply max_le
    · have h := (X - C a).le_gaussNorm v zero_le_one 1
      rwa [hc1, map_one, one_pow, mul_one] at h
    · have h := (X - C a).le_gaussNorm v zero_le_one 0
      rwa [hc0, AbsoluteValue.map_neg, pow_zero, mul_one] at h

private theorem gaussNorm_one_multiset_prod_aux {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (s : Multiset K[X]) :
    s.prod.gaussNorm v 1 = (s.map fun q => q.gaussNorm v 1).prod := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero, Multiset.prod_zero, ← C_1, gaussNorm_C, map_one]
  | cons q s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, gaussNorm_mul hv one_pos, ih]

private theorem abv_eval_eq_gaussNorm_mul_prod_aux {K : Type*} [Field K] [IsAlgClosed K]
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (p : K[X]) {z : K} (hz : v z ≤ 1) :
    v (p.eval z)
      = p.gaussNorm v 1 * ((p.roots.filter fun a => v a ≤ 1).map fun a => v (z - a)).prod := by
  have hout : ∀ a : K, ¬ v a ≤ 1 → v (z - a) = max 1 (v a) := by
    intro a ha'
    have ha := not_le.mp ha'
    have hne : v z ≠ v (-a) := by
      rw [AbsoluteValue.map_neg]
      exact (hz.trans_lt ha).ne
    have hmax : v (z + -a) = max (v z) (v (-a)) :=
      IsNonarchimedean.add_eq_max_of_ne (fun x => AbsoluteValue.map_neg v x) hv hne
    rw [sub_eq_add_neg, hmax, AbsoluteValue.map_neg,
      max_eq_right (hz.trans ha.le), max_eq_right ha.le]
  have hin : ∀ a : K, v a ≤ 1 → max 1 (v a) = 1 := fun a ha => max_eq_left ha
  have key : ∀ s : Multiset K, (s.map fun a => v (z - a)).prod
      = (s.map fun a => max 1 (v a)).prod
        * ((s.filter fun a => v a ≤ 1).map fun a => v (z - a)).prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      by_cases ha : v a ≤ 1
      · rw [Multiset.filter_cons_of_pos (p := fun a => v a ≤ 1) s ha]
        simp only [Multiset.map_cons, Multiset.prod_cons, ih, hin a ha]
        ring
      · rw [Multiset.filter_cons_of_neg (p := fun a => v a ≤ 1) s ha]
        simp only [Multiset.map_cons, Multiset.prod_cons, ih, hout a ha]
        ring
  have hp := (IsAlgClosed.splits p).eq_prod_roots
  have h1 : v (p.eval z) = v p.leadingCoeff * (p.roots.map fun a => v (z - a)).prod := by
    conv_lhs => rw [hp]
    rw [eval_mul, eval_C, eval_multiset_prod, map_mul, map_multiset_prod, Multiset.map_map,
      Multiset.map_map]
    congr 1
    apply congrArg
    apply Multiset.map_congr rfl
    intro a _
    simp
  have h2 : p.gaussNorm v 1 = v p.leadingCoeff * (p.roots.map fun a => max 1 (v a)).prod := by
    conv_lhs => rw [hp]
    rw [gaussNorm_mul hv one_pos, gaussNorm_C, gaussNorm_one_multiset_prod_aux v hv,
      Multiset.map_map]
    congr 1
    apply congrArg
    apply Multiset.map_congr rfl
    intro a _
    simp [gaussNorm_one_X_sub_C_aux v hv]
  rw [h1, h2, key p.roots, mul_assoc]

/-- For a nonzero polynomial over an algebraically closed field with a
nonarchimedean absolute value, the logarithm of the absolute value at a point
of the closed unit disk is the logarithm of the Gauss norm plus the sum of
`log (v (z - a))` over the roots `a` in the closed unit disk, counted with
multiplicity. -/
public theorem log_abv_eval_eq_log_gaussNorm_add_sum {K : Type*} [Field K] [IsAlgClosed K]
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (p : K[X]) (hp : p ≠ 0)
    {z : K} (hz : v z ≤ 1) (hpz : p.eval z ≠ 0) :
    Real.log (v (p.eval z)) = Real.log (p.gaussNorm v 1)
      + ((p.roots.filter fun a => v a ≤ 1).map fun a => Real.log (v (z - a))).sum := by
  have hne : ∀ a ∈ (p.roots.filter fun a => v a ≤ 1), v (z - a) ≠ 0 := by
    intro a ha h
    have hr : p.eval a = 0 := (mem_roots hp).mp (Multiset.mem_filter.mp ha).1
    rw [AbsoluteValue.eq_zero, sub_eq_zero] at h
    subst h
    exact hpz hr
  have hgN : p.gaussNorm v 1 ≠ 0 :=
    (gaussNorm_eq_zero_iff v p (fun x hx => (AbsoluteValue.eq_zero v).mp hx) one_pos).not.mpr hp
  have hall : ∀ x ∈ ((p.roots.filter fun a => v a ≤ 1).map fun a => v (z - a)), x ≠ 0 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
    exact hne a ha
  have hprod : ((p.roots.filter fun a => v a ≤ 1).map fun a => v (z - a)).prod ≠ 0 :=
    Multiset.prod_ne_zero fun h0 => hall 0 h0 rfl
  rw [abv_eval_eq_gaussNorm_mul_prod_aux v hv p hz, Real.log_mul hgN hprod,
    Real.log_multiset_prod hall, Multiset.map_map]
  rfl

end Polynomial
