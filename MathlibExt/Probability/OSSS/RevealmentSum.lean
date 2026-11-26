/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Summing revealment bounds over translated profiles

Combinatorial bounds for revealment estimates in the Duminil-Copin–Raoufi–Tassion argument: when
the decision tree explores from `∂Λ_r` with `r` uniform in `[1, n]`, the probability of revealing
an edge at distance `j` from `∂Λ_r` is bounded by a one-arm probability `μ(j)`, and summing over
`r` gives at most `2 ∑_{j ≤ n} μ(j)`, since each distance arises from at most two values of `r`.

## Main results

* `StatMech.OSSS.sum_reindex_le_card_smul`: reindexing a sum through a map with fibres of size at
  most `C`.
* `StatMech.OSSS.sum_translate_le`: `∑_{k=1}^{n} g |k - r| ≤ 2 ∑_{j=0}^{n} g j`.
* `StatMech.OSSS.revealment_sum_bound`, `revealment_family_sum_le`: the bounds in terms of
  `sup_x ∑_j μ x j`.

## References

* H. Duminil-Copin, A. Raoufi, V. Tassion, *Sharp phase transition for the random-cluster and
  Potts models via decision trees*, Ann. of Math. 189 (2019), 75–99.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace StatMech
namespace OSSS

/-- If `φ` maps `S` into `T` with fibres of size at most `C`, then `∑_{a ∈ S} g (φ a) ≤ C ∑_{b ∈ T}
g b` for `g ≥ 0`. -/
theorem sum_reindex_le_card_smul {α β : Type*} [DecidableEq β] (S : Finset α) (φ : α → β)
    (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) (T : Finset β) (himg : ∀ a ∈ S, φ a ∈ T)
    (C : ℕ) (hfib : ∀ b ∈ T, (S.filter (fun a => φ a = b)).card ≤ C) :
    ∑ a ∈ S, g (φ a) ≤ (C : ℝ) * ∑ b ∈ T, g b := by
  rw [← Finset.sum_fiberwise_of_maps_to himg (fun a => g (φ a)), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have heq : ∀ a ∈ S.filter (fun a => φ a = b), g (φ a) = g b := by
    intro a ha; rw [Finset.mem_filter] at ha; rw [ha.2]
  rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfib b hb) (hg b)

private theorem translate_fibre_card_le (n r j : ℕ) :
    ((Finset.Icc 1 n).filter (fun k : ℕ => ((k : ℤ) - (r : ℤ)).natAbs = j)).card ≤ 2 := by
  apply le_trans (Finset.card_le_card (t := ({r + j, r - j} : Finset ℕ)) ?_)
  · exact le_trans (Finset.card_insert_le _ _) (by simp)
  · intro k hk
    rw [Finset.mem_filter] at hk
    have hj : ((k : ℤ) - r).natAbs = j := hk.2
    rw [Int.natAbs_eq_iff] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

/-- `∑_{k=1}^{n} g |k - r| ≤ 2 ∑_{j=0}^{n} g j` for `r ≤ n` and `g ≥ 0`. -/
theorem sum_translate_le (n r : ℕ) (hr : r ≤ n) (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) :
    ∑ k ∈ Finset.Icc 1 n, g ((k : ℤ) - (r : ℤ)).natAbs
      ≤ 2 * ∑ j ∈ Finset.range (n + 1), g j := by
  apply sum_reindex_le_card_smul (Finset.Icc 1 n)
    (fun k => ((k : ℤ) - (r : ℤ)).natAbs) g hg (Finset.range (n + 1)) ?_ 2 ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    have : ((k : ℤ) - (r : ℤ)).natAbs ≤ n := by omega
    omega
  · intro j _; exact translate_fibre_card_le n r j

/-- `∑_{k=1}^{n} g |k - r| ≤ 2 ∑_{j=0}^{n-1} g j` for `1 ≤ r ≤ n` and `g ≥ 0`. -/
theorem sum_translate_le_range (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) (g : ℕ → ℝ)
    (hg : ∀ j, 0 ≤ g j) :
    ∑ k ∈ Finset.Icc 1 n, g ((k : ℤ) - (r : ℤ)).natAbs
      ≤ 2 * ∑ j ∈ Finset.range n, g j := by
  apply sum_reindex_le_card_smul (Finset.Icc 1 n)
    (fun k => ((k : ℤ) - (r : ℤ)).natAbs) g hg (Finset.range n) ?_ 2 ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    have : ((k : ℤ) - (r : ℤ)).natAbs ≤ n - 1 := by omega
    omega
  · intro j _; exact translate_fibre_card_le n r j

/-- `2 S u ≤ 2 sup_{x ∈ Λ} S x` for `u ∈ Λ`. -/
theorem sum_le_two_mul_sup' {α : Type*} (Λ : Finset α) (hne : Λ.Nonempty)
    (S : α → ℝ) (u : α) (hu : u ∈ Λ) :
    2 * S u ≤ 2 * Λ.sup' hne S :=
  mul_le_mul_of_nonneg_left (Finset.le_sup' S hu) (by norm_num)

/-- If `q k ≤ μ u |k - r|`, then `∑_{k=1}^{n} q k ≤ 2 sup_{x ∈ Λ} ∑_{j ≤ n} μ x j`. -/
theorem revealment_sum_bound {α : Type*} (Λ : Finset α) (hne : Λ.Nonempty)
    (μ : α → ℕ → ℝ) (hμ : ∀ x j, 0 ≤ μ x j) (n r : ℕ) (hr : r ≤ n)
    (u : α) (hu : u ∈ Λ) (q : ℕ → ℝ)
    (hcomp : ∀ k, q k ≤ μ u ((k : ℤ) - (r : ℤ)).natAbs) :
    ∑ k ∈ Finset.Icc 1 n, q k
      ≤ 2 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), μ x j) := by
  have hA : ∑ k ∈ Finset.Icc 1 n, q k
      ≤ ∑ k ∈ Finset.Icc 1 n, μ u ((k : ℤ) - (r : ℤ)).natAbs :=
    Finset.sum_le_sum (fun k _ => hcomp k)
  have hB : ∑ k ∈ Finset.Icc 1 n, μ u ((k : ℤ) - (r : ℤ)).natAbs
      ≤ 2 * ∑ j ∈ Finset.range (n + 1), μ u j :=
    sum_translate_le n r hr (μ u) (hμ u)
  have hC : 2 * ∑ j ∈ Finset.range (n + 1), μ u j
      ≤ 2 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), μ x j) :=
    sum_le_two_mul_sup' Λ hne (fun x => ∑ j ∈ Finset.range (n + 1), μ x j) u hu
  exact hA.trans (hB.trans hC)

/-- Variant of `revealment_sum_bound` with `1 ≤ r` and the sum over `j < n`. -/
theorem revealment_sum_bound_range {α : Type*} (Λ : Finset α) (hne : Λ.Nonempty)
    (μ : α → ℕ → ℝ) (hμ : ∀ x j, 0 ≤ μ x j) (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n)
    (u : α) (hu : u ∈ Λ) (q : ℕ → ℝ)
    (hcomp : ∀ k, q k ≤ μ u ((k : ℤ) - (r : ℤ)).natAbs) :
    ∑ k ∈ Finset.Icc 1 n, q k
      ≤ 2 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n, μ x j) := by
  have hA : ∑ k ∈ Finset.Icc 1 n, q k
      ≤ ∑ k ∈ Finset.Icc 1 n, μ u ((k : ℤ) - (r : ℤ)).natAbs :=
    Finset.sum_le_sum (fun k _ => hcomp k)
  have hB : ∑ k ∈ Finset.Icc 1 n, μ u ((k : ℤ) - (r : ℤ)).natAbs
      ≤ 2 * ∑ j ∈ Finset.range n, μ u j :=
    sum_translate_le_range n r hr1 hrn (μ u) (hμ u)
  have hC : 2 * ∑ j ∈ Finset.range n, μ u j
      ≤ 2 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n, μ x j) :=
    sum_le_two_mul_sup' Λ hne (fun x => ∑ j ∈ Finset.range n, μ x j) u hu
  exact hA.trans (hB.trans hC)

/-- Two-endpoint version: for an edge with endpoints `u`, `v`, the summed revealment is at most `4
sup_{x ∈ Λ} ∑_{j ≤ n} μ x j`. -/
theorem revealment_family_sum_le {α : Type*} (Λ : Finset α) (hne : Λ.Nonempty)
    (μ : α → ℕ → ℝ) (hμ : ∀ x j, 0 ≤ μ x j) (n ru rv : ℕ) (hru : ru ≤ n) (hrv : rv ≤ n)
    (u v : α) (hu : u ∈ Λ) (hv : v ∈ Λ) (qu qv : ℕ → ℝ)
    (hcompu : ∀ k, qu k ≤ μ u ((k : ℤ) - (ru : ℤ)).natAbs)
    (hcompv : ∀ k, qv k ≤ μ v ((k : ℤ) - (rv : ℤ)).natAbs) :
    ∑ k ∈ Finset.Icc 1 n, (qu k + qv k)
      ≤ 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), μ x j) := by
  rw [Finset.sum_add_distrib]
  have hu' := revealment_sum_bound Λ hne μ hμ n ru hru u hu qu hcompu
  have hv' := revealment_sum_bound Λ hne μ hμ n rv hrv v hv qv hcompv
  have : ∑ k ∈ Finset.Icc 1 n, qu k + ∑ k ∈ Finset.Icc 1 n, qv k
      ≤ 2 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), μ x j)
        + 2 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), μ x j) :=
    add_le_add hu' hv'
  linarith

end OSSS
end StatMech
