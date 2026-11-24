/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.LinearAlgebra.Matrix.SinkhornMargins
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Entropy-minimizing table uniqueness

## i. Overview

For a positive kernel `K` and positive scaling factors `a`
and `b`, let `T i j = a i * K i j * b j` and consider the
entropy functional `F(S) = ∑ i j, S i j * log (S i j / K i j)`
over nonnegative tables `S` with the same row and column
margins as `T`. The entrywise KL identity writes
`F(S) - F(T)` as a sum of nonnegative terms
`T i j * klFun (S i j / T i j)`, so equality of the entropy
values forces `S = T`: the minimizing table is unique. The
scaling factors are not unique, since replacing `(a, b)` by
`(c * a, b / c)` for nonzero `c` gives the same table. No
existence or convergence claim for scaling factors is made.

## ii. Key results

- `SinkhornMargins.scaled_table_gauge`: gauge invariance for
  general finite index types.
- `SinkhornMargins.entropy_minimizer_unique`: entropy
  equality holds if and only if the tables agree.
- `SinkhornMargins.entropy_minimizer_unique_scaledTable`:
  the same criterion for the finite `scaledTable` API.

## iii. Table of contents

- A. Gauge invariance and uniqueness

## iv. References

- R. Sinkhorn and P. Knopp, concerning nonnegative matrices
  and doubly stochastic matrices, *Pacific J. Math.* 21,
  1967.
-/

@[expose] public section

namespace SinkhornMargins

open InformationTheory

/-! ## A. Gauge invariance and uniqueness -/

/-- Gauge nonuniqueness of scaling factors: replacing `(a, b)`
by `(c • a, c⁻¹ • b)`-style componentwise rescaling with
`c > 0` gives the same scaled table. -/
theorem scaled_table_gauge {ι κ : Type*} (K : ι → κ → ℝ)
    (a : ι → ℝ) (b : κ → ℝ) {c : ℝ} (hc : c ≠ 0) :
    (fun i j => (c * a i) * K i j * (b j / c))
      = fun i j => a i * K i j * b j := by
  funext i j
  field_simp

private lemma klFun_scaled_entry {s t k ai bj : ℝ} (hk : 0 < k) (hai : 0 < ai)
    (hbj : 0 < bj) (hs : 0 ≤ s) (ht : t = ai * k * bj) :
    t * klFun (s / t) = s * Real.log (s / k) - t * Real.log (t / k)
      + (t - s) * (1 + Real.log ai + Real.log bj) := by
  have hai0 : ai ≠ 0 := ne_of_gt hai
  have hk0 : k ≠ 0 := ne_of_gt hk
  have hbj0 : bj ≠ 0 := ne_of_gt hbj
  have htpos : 0 < t := by
    rw [ht]
    exact mul_pos (mul_pos hai hk) hbj
  have ht0 : t ≠ 0 := ne_of_gt htpos
  have htk : t / k = ai * bj := by
    rw [ht, div_eq_iff hk0]
    ring
  have hlogtk : Real.log (t / k) = Real.log ai + Real.log bj := by
    rw [htk, Real.log_mul hai0 hbj0]
  have hlogt : Real.log t = Real.log ai + Real.log k + Real.log bj := by
    rw [ht, Real.log_mul (mul_ne_zero hai0 hk0) hbj0, Real.log_mul hai0 hk0]
  by_cases hs0 : s = 0
  · subst hs0
    rw [zero_div, klFun_zero, hlogtk]
    ring
  · have h1 : Real.log (s / t) = Real.log s - Real.log t :=
      Real.log_div hs0 ht0
    have h2 : Real.log (s / k) = Real.log s - Real.log k :=
      Real.log_div hs0 hk0
    rw [klFun_apply, h1, h2, hlogtk, hlogt]
    field_simp
    ring

/-- Uniqueness of the entropy-minimizing table: under the
certificate hypotheses (positive `K`, `a`, `b`; nonnegative
`S` with the same row and column margins as the scaled table
`T i j = a i * K i j * b j`), the entropy functional
`F(S) = ∑ i j, S i j * log (S i j / K i j)` equals `F(T)` if
and only if `S = T`. The minimizing table is unique even
though its scaling factors are not. -/
theorem entropy_minimizer_unique {ι κ : Type*}
    [Fintype ι] [Fintype κ] (K S : ι → κ → ℝ) (a : ι → ℝ)
    (b : κ → ℝ) (hK : ∀ i j, 0 < K i j) (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) (hS : ∀ i j, 0 ≤ S i j)
    (hrow : ∀ i, ∑ j, S i j = ∑ j, a i * K i j * b j)
    (hcol : ∀ j, ∑ i, S i j = ∑ i, a i * K i j * b j) :
    ((∑ i, ∑ j, S i j * Real.log (S i j / K i j))
      = ∑ i, ∑ j, (a i * K i j * b j)
          * Real.log ((a i * K i j * b j) / K i j))
    ↔ S = fun i j => a i * K i j * b j := by
  constructor
  · intro hF
    have hT : ∀ i j, 0 < a i * K i j * b j :=
      fun i j => mul_pos (mul_pos (ha i) (hK i j)) (hb j)
    have hentry : ∀ i j, (a i * K i j * b j) * klFun (S i j / (a i * K i j * b j))
          = S i j * Real.log (S i j / K i j)
            - (a i * K i j * b j) * Real.log ((a i * K i j * b j) / K i j)
            + ((a i * K i j * b j) - S i j) * (1 + Real.log (a i) + Real.log (b j)) :=
      fun i j => klFun_scaled_entry (hK i j) (ha i) (hb j) (hS i j) rfl
    have hrowD : ∀ i, ∑ j, (a i * K i j * b j - S i j) = 0 := by
      intro i
      rw [Finset.sum_sub_distrib, hrow i, sub_self]
    have hcolD : ∀ j, ∑ i, (a i * K i j * b j - S i j) = 0 := by
      intro j
      rw [Finset.sum_sub_distrib, hcol j, sub_self]
    have hA : (∑ i, ∑ j, ((a i * K i j * b j - S i j) * (1 + Real.log (a i)))) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Finset.sum_mul, hrowD i, zero_mul]
    have hB : (∑ i, ∑ j, ((a i * K i j * b j - S i j) * Real.log (b j))) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.sum_mul, hcolD j, zero_mul]
    have hDL : (∑ i, ∑ j, ((a i * K i j * b j - S i j)
        * (1 + Real.log (a i) + Real.log (b j)))) = 0 := by
      have hsplit : ∀ i j, (a i * K i j * b j - S i j) * (1 + Real.log (a i) + Real.log (b j))
            = (a i * K i j * b j - S i j) * (1 + Real.log (a i))
              + (a i * K i j * b j - S i j) * Real.log (b j) := by
        intro i j; ring
      simp_rw [hsplit, Finset.sum_add_distrib]
      rw [hA, hB, add_zero]
    have hsum : (∑ i, ∑ j, (a i * K i j * b j) * klFun (S i j / (a i * K i j * b j)))
          = (∑ i, ∑ j, S i j * Real.log (S i j / K i j))
            - (∑ i, ∑ j, (a i * K i j * b j) * Real.log ((a i * K i j * b j) / K i j)) := by
      simp_rw [hentry, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hDL, add_zero]
    rw [hF, sub_self] at hsum
    have hnonneg : ∀ i j, 0 ≤ (a i * K i j * b j) * klFun (S i j / (a i * K i j * b j)) := by
      intro i j
      exact mul_nonneg (le_of_lt (hT i j))
        (klFun_nonneg (div_nonneg (hS i j) (le_of_lt (hT i j))))
    have hzero : ∀ i j, (a i * K i j * b j) * klFun (S i j / (a i * K i j * b j)) = 0 := by
      have houter : ∀ i ∈ Finset.univ,
          (∑ j, (a i * K i j * b j) * klFun (S i j / (a i * K i j * b j))) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => Finset.sum_nonneg (fun j _ => hnonneg i j))).mp hsum
      intro i j
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg i j)).mp
        (houter i (Finset.mem_univ i)) j (Finset.mem_univ j)
    funext i j
    have hz := hzero i j
    have hTpos := hT i j
    have ht0 : (a i * K i j * b j) ≠ 0 := ne_of_gt hTpos
    have hkl : klFun (S i j / (a i * K i j * b j)) = 0 := by
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h ht0
      · exact h
    have hdiv1 : S i j / (a i * K i j * b j) = 1 :=
      (klFun_eq_zero_iff (div_nonneg (hS i j) (le_of_lt hTpos))).mp hkl
    exact (div_eq_one_iff_eq ht0).mp hdiv1
  · intro h
    rw [h]

/-- Uniqueness of the entropy-minimizing table for the
finite `scaledTable` API: under the certificate hypotheses,
with `S` having the same margins as `scaledTable a K b`, the
entropy values agree if and only if `S` is that scaled
table. -/
theorem entropy_minimizer_unique_scaledTable {m n : ℕ}
    (K S : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ)
    (b : Fin n → ℝ) (hK : ∀ i j, 0 < K i j) (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) (hS : ∀ i j, 0 ≤ S i j)
    (hrow : ∀ i, ∑ j, S i j = ∑ j, scaledTable a K b i j)
    (hcol : ∀ j, ∑ i, S i j = ∑ i, scaledTable a K b i j) :
    ((∑ i, ∑ j, S i j * Real.log (S i j / K i j))
      = ∑ i, ∑ j, scaledTable a K b i j
          * Real.log (scaledTable a K b i j / K i j))
    ↔ S = scaledTable a K b :=
  entropy_minimizer_unique K S a b hK ha hb hS hrow hcol

end SinkhornMargins
