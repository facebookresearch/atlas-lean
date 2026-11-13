/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Inequality.FGT
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

namespace MathlibExtTest.Economics.Inequality.FGT

open MathlibExt.Economics.Poverty
open Finset

theorem test_fgt_total :
    fgt 10 1 (![2, 8, 12, 20] : Fin 4 → ℝ) Finset.univ = 1 / 4 := by
  have _ := fgt_eq_sum_groups (z := 10) (α := 1)
    (x := (![2, 8, 12, 20] : Fin 4 → ℝ)) (s := (Finset.univ : Finset (Fin 4)))
    (t := (Finset.univ : Finset (Fin 2))) (g := (![0, 1, 0, 1] : Fin 4 → Fin 2))
    (fun i _ => Finset.mem_univ _)
  have h0lt : (2 : ℝ) < 10 := by norm_num
  have h1lt : (8 : ℝ) < 10 := by norm_num
  have h2nlt : ¬ (12 : ℝ) < 10 := by norm_num
  have h3nlt : ¬ (20 : ℝ) < 10 := by norm_num
  unfold fgt
  rw [Fin.sum_univ_four]
  simp [fgtTerm, h0lt, h1lt, h2nlt, h3nlt, Real.rpow_one]
  norm_num

theorem test_fgt_group0 :
    fgt 10 1 (![2, 8, 12, 20] : Fin 4 → ℝ)
      (Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 0)) =
      2 / 5 := by
  have _ := fgt_eq_sum_groups (z := 10) (α := 1)
    (x := (![2, 8, 12, 20] : Fin 4 → ℝ)) (s := (Finset.univ : Finset (Fin 4)))
    (t := (Finset.univ : Finset (Fin 2))) (g := (![0, 1, 0, 1] : Fin 4 → Fin 2))
    (fun i _ => Finset.mem_univ _)
  have h0lt : (2 : ℝ) < 10 := by norm_num
  have h2nlt : ¬ (12 : ℝ) < 10 := by norm_num
  have hfilter : Finset.univ.filter
      (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 0) =
      ({0, 2} : Finset (Fin 4)) := by decide
  rw [hfilter]
  unfold fgt
  simp [fgtTerm, h0lt, h2nlt, Real.rpow_one]
  norm_num

theorem test_fgt_group1 :
    fgt 10 1 (![2, 8, 12, 20] : Fin 4 → ℝ)
      (Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 1)) =
      1 / 10 := by
  have _ := fgt_eq_sum_groups (z := 10) (α := 1)
    (x := (![2, 8, 12, 20] : Fin 4 → ℝ)) (s := (Finset.univ : Finset (Fin 4)))
    (t := (Finset.univ : Finset (Fin 2))) (g := (![0, 1, 0, 1] : Fin 4 → Fin 2))
    (fun i _ => Finset.mem_univ _)
  have h1lt : (8 : ℝ) < 10 := by norm_num
  have h3nlt : ¬ (20 : ℝ) < 10 := by norm_num
  have hfilter : Finset.univ.filter
      (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 1) =
      ({1, 3} : Finset (Fin 4)) := by decide
  rw [hfilter]
  unfold fgt
  simp [fgtTerm, h1lt, h3nlt, Real.rpow_one]
  norm_num

theorem test_fgt_decomp_rhs :
    (∑ k ∈ (Finset.univ : Finset (Fin 2)),
      (((Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = k)).card /
        (Finset.univ : Finset (Fin 4)).card : ℝ)) *
      fgt 10 1 (![2, 8, 12, 20] : Fin 4 → ℝ)
        (Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = k))) =
      1 / 4 := by
  have hdecomp := fgt_eq_sum_groups (z := 10) (α := 1)
    (x := (![2, 8, 12, 20] : Fin 4 → ℝ)) (s := (Finset.univ : Finset (Fin 4)))
    (t := (Finset.univ : Finset (Fin 2))) (g := (![0, 1, 0, 1] : Fin 4 → Fin 2))
    (fun i _ => Finset.mem_univ _)
  have h0lt : (2 : ℝ) < 10 := by norm_num
  have h1lt : (8 : ℝ) < 10 := by norm_num
  have h2nlt : ¬ (12 : ℝ) < 10 := by norm_num
  have h3nlt : ¬ (20 : ℝ) < 10 := by norm_num
  have hg0 : fgt 10 1 (![2, 8, 12, 20] : Fin 4 → ℝ)
      (Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 0)) =
      2 / 5 := by
    have hfilter : Finset.univ.filter
        (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 0) =
        ({0, 2} : Finset (Fin 4)) := by decide
    rw [hfilter]
    unfold fgt
    simp [fgtTerm, h0lt, h2nlt, Real.rpow_one]
    norm_num
  have hg1 : fgt 10 1 (![2, 8, 12, 20] : Fin 4 → ℝ)
      (Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 1)) =
      1 / 10 := by
    have hfilter : Finset.univ.filter
        (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 1) =
        ({1, 3} : Finset (Fin 4)) := by decide
    rw [hfilter]
    unfold fgt
    simp [fgtTerm, h1lt, h3nlt, Real.rpow_one]
    norm_num
  have hc0 : (((Finset.univ.filter
      (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 0)).card : ℝ)) = 2 := by
    have h : (Finset.univ.filter
        (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 0)).card = 2 := by decide
    rw [h]
    norm_num
  have hc1 : (((Finset.univ.filter
      (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 1)).card : ℝ)) = 2 := by
    have h : (Finset.univ.filter
        (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 1)).card = 2 := by decide
    rw [h]
    norm_num
  have hcs : (((Finset.univ : Finset (Fin 4))).card : ℝ) = 4 := by
    have h : ((Finset.univ : Finset (Fin 4))).card = 4 := by decide
    rw [h]
    norm_num
  rw [Fin.sum_univ_two]
  rw [hg0, hg1, hc0, hc1, hcs]
  norm_num

theorem test_fgt_decomp_numeric :
    (1 / 4 : ℝ) = (1 / 2) * (2 / 5) + (1 / 2) * (1 / 10) := by
  have h0lt : (2 : ℝ) < 10 := by norm_num
  have h1lt : (8 : ℝ) < 10 := by norm_num
  have h2nlt : ¬ (12 : ℝ) < 10 := by norm_num
  have h3nlt : ¬ (20 : ℝ) < 10 := by norm_num
  have htotal : fgt 10 1 (![2, 8, 12, 20] : Fin 4 → ℝ) Finset.univ = 1 / 4 := by
    unfold fgt
    rw [Fin.sum_univ_four]
    simp [fgtTerm, h0lt, h1lt, h2nlt, h3nlt, Real.rpow_one]
    norm_num
  have hg0 : fgt 10 1 (![2, 8, 12, 20] : Fin 4 → ℝ)
      (Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 0)) =
      2 / 5 :=
    test_fgt_group0
  have hg1 : fgt 10 1 (![2, 8, 12, 20] : Fin 4 → ℝ)
      (Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 1)) =
      1 / 10 :=
    test_fgt_group1
  have hc0 : (((Finset.univ.filter
      (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 0)).card : ℝ)) = 2 := by
    have h : (Finset.univ.filter
        (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 0)).card = 2 := by decide
    rw [h]
    norm_num
  have hc1 : (((Finset.univ.filter
      (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 1)).card : ℝ)) = 2 := by
    have h : (Finset.univ.filter
        (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 1)).card = 2 := by decide
    rw [h]
    norm_num
  have hcs : (((Finset.univ : Finset (Fin 4))).card : ℝ) = 4 := by
    have h : ((Finset.univ : Finset (Fin 4))).card = 4 := by decide
    rw [h]
    norm_num
  have hdecomp := fgt_eq_sum_groups (z := 10) (α := 1)
    (x := (![2, 8, 12, 20] : Fin 4 → ℝ)) (s := (Finset.univ : Finset (Fin 4)))
    (t := (Finset.univ : Finset (Fin 2))) (g := (![0, 1, 0, 1] : Fin 4 → Fin 2))
    (fun i _ => Finset.mem_univ _)
  have hrhs : (∑ k ∈ (Finset.univ : Finset (Fin 2)),
      (((Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = k)).card /
        (Finset.univ : Finset (Fin 4)).card : ℝ)) *
      fgt 10 1 (![2, 8, 12, 20] : Fin 4 → ℝ)
        (Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = k))) =
      (1 / 2) * (2 / 5) + (1 / 2) * (1 / 10) := by
    rw [Fin.sum_univ_two]
    rw [hg0, hg1, hc0, hc1, hcs]
    norm_num
  have h := hdecomp.trans hrhs
  rw [htotal] at h
  exact h

theorem test_empty_weight :
    ((((Finset.univ.filter
      (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = 2)).card /
      (Finset.univ : Finset (Fin 4)).card : ℝ))) = 0 := by
  have _ := fgt_eq_sum_groups (z := 10) (α := 1)
    (x := (![2, 8, 12, 20] : Fin 4 → ℝ)) (s := (Finset.univ : Finset (Fin 4)))
    (t := (Finset.univ : Finset (Fin 3))) (g := (![0, 1, 0, 1] : Fin 4 → Fin 3))
    (fun i _ => Finset.mem_univ _)
  have hempty : Finset.univ.filter
      (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = 2) =
      (∅ : Finset (Fin 4)) := by decide
  have hcard : (Finset.univ.filter
      (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = 2)).card = 0 := by
    rw [hempty]
    simp
  simp [hcard]

theorem test_empty_decomp :
    (∑ k ∈ (Finset.univ : Finset (Fin 3)),
      (((Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = k)).card /
        (Finset.univ : Finset (Fin 4)).card : ℝ)) *
      fgt 10 1 (![2, 8, 12, 20] : Fin 4 → ℝ)
        (Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = k))) =
      1 / 4 := by
  have hdecomp := fgt_eq_sum_groups (z := 10) (α := 1)
    (x := (![2, 8, 12, 20] : Fin 4 → ℝ)) (s := (Finset.univ : Finset (Fin 4)))
    (t := (Finset.univ : Finset (Fin 3))) (g := (![0, 1, 0, 1] : Fin 4 → Fin 3))
    (fun i _ => Finset.mem_univ _)
  have h0lt : (2 : ℝ) < 10 := by norm_num
  have h1lt : (8 : ℝ) < 10 := by norm_num
  have h2nlt : ¬ (12 : ℝ) < 10 := by norm_num
  have h3nlt : ¬ (20 : ℝ) < 10 := by norm_num
  have hg0 : fgt 10 1 (![2, 8, 12, 20] : Fin 4 → ℝ)
      (Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = 0)) =
      2 / 5 := by
    have hfilter : Finset.univ.filter
        (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = 0) =
        ({0, 2} : Finset (Fin 4)) := by decide
    rw [hfilter]
    unfold fgt
    simp [fgtTerm, h0lt, h2nlt, Real.rpow_one]
    norm_num
  have hg1 : fgt 10 1 (![2, 8, 12, 20] : Fin 4 → ℝ)
      (Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = 1)) =
      1 / 10 := by
    have hfilter : Finset.univ.filter
        (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = 1) =
        ({1, 3} : Finset (Fin 4)) := by decide
    rw [hfilter]
    unfold fgt
    simp [fgtTerm, h1lt, h3nlt, Real.rpow_one]
    norm_num
  have hg2 : fgt 10 1 (![2, 8, 12, 20] : Fin 4 → ℝ)
      (Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = 2)) =
      0 := by
    have hempty : Finset.univ.filter
        (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = 2) =
        (∅ : Finset (Fin 4)) := by decide
    rw [hempty]
    unfold fgt
    simp
  have hc0 : (((Finset.univ.filter
      (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = 0)).card : ℝ)) = 2 := by
    have h : (Finset.univ.filter
        (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = 0)).card = 2 := by decide
    rw [h]
    norm_num
  have hc1 : (((Finset.univ.filter
      (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = 1)).card : ℝ)) = 2 := by
    have h : (Finset.univ.filter
        (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = 1)).card = 2 := by decide
    rw [h]
    norm_num
  have hc2 : (((Finset.univ.filter
      (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = 2)).card : ℝ)) = 0 := by
    have hempty : Finset.univ.filter
        (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = 2) =
        (∅ : Finset (Fin 4)) := by decide
    have h : (Finset.univ.filter
        (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 3) i = 2)).card = 0 := by
      rw [hempty]
      simp
    rw [h]
    norm_num
  have hcs : (((Finset.univ : Finset (Fin 4))).card : ℝ) = 4 := by
    have h : ((Finset.univ : Finset (Fin 4))).card = 4 := by decide
    rw [h]
    norm_num
  rw [Fin.sum_univ_three]
  rw [hg0, hg1, hg2, hc0, hc1, hc2, hcs]
  norm_num

end MathlibExtTest.Economics.Inequality.FGT