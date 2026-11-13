/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Mathlib
import Code.OSSS.RevealmentSum

open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace StatMech
namespace Walls
















theorem oc_sum_reindex_le_card_smul {α β : Type*} [DecidableEq β] (S : Finset α)
    (φ : α → β) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) (T : Finset β)
    (himg : ∀ a ∈ S, φ a ∈ T) (C : ℕ)
    (hfib : ∀ b ∈ T, (S.filter (fun a => φ a = b)).card ≤ C) :
    ∑ a ∈ S, g (φ a) ≤ (C : ℝ) * ∑ b ∈ T, g b := by
  rw [← Finset.sum_fiberwise_of_maps_to himg (fun a => g (φ a)), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have heq : ∀ a ∈ S.filter (fun a => φ a = b), g (φ a) = g b := by
    intro a ha; rw [Finset.mem_filter] at ha; rw [ha.2]
  rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfib b hb) (hg b)










private theorem oc_translate_fibre_card_le (n r j : ℕ) :
    ((Finset.Icc 1 n).filter (fun k : ℕ => ((k : ℤ) - (r : ℤ)).natAbs = j)).card ≤ 2 := by
  apply le_trans (Finset.card_le_card (t := ({r + j, r - j} : Finset ℕ)) ?_)
  · exact le_trans (Finset.card_insert_le _ _) (by simp)
  · intro k hk
    rw [Finset.mem_filter] at hk
    have hj : ((k : ℤ) - r).natAbs = j := hk.2
    rw [Int.natAbs_eq_iff] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega









theorem oc_sum_translate_le (n r : ℕ) (hr : r ≤ n) (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) :
    ∑ k ∈ Finset.Icc 1 n, g ((k : ℤ) - (r : ℤ)).natAbs
      ≤ 2 * ∑ j ∈ Finset.range (n + 1), g j := by
  apply oc_sum_reindex_le_card_smul (Finset.Icc 1 n)
    (fun k => ((k : ℤ) - (r : ℤ)).natAbs) g hg (Finset.range (n + 1)) ?_ 2 ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    have : ((k : ℤ) - (r : ℤ)).natAbs ≤ n := by omega
    omega
  · intro j _; exact oc_translate_fibre_card_le n r j











theorem oc_two_mul_le_two_mul_sup' {α : Type*} (Λ : Finset α) (hne : Λ.Nonempty)
    (S : α → ℝ) (u : α) (hu : u ∈ Λ) :
    2 * S u ≤ 2 * Λ.sup' hne S :=
  mul_le_mul_of_nonneg_left (Finset.le_sup' S hu) (by norm_num)
























theorem oc_revealment_sum_bound {α : Type*} (Λ : Finset α) (hne : Λ.Nonempty)
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
    oc_sum_translate_le n r hr (μ u) (hμ u)
  
  have hC : 2 * ∑ j ∈ Finset.range (n + 1), μ u j
      ≤ 2 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), μ x j) :=
    oc_two_mul_le_two_mul_sup' Λ hne (fun x => ∑ j ∈ Finset.range (n + 1), μ x j) u hu
  exact hA.trans (hB.trans hC)




















theorem oc_box_crossing_scale_sum {α : Type*} (Λ : Finset α) (hne : Λ.Nonempty)
    (μ : α → ℕ → ℝ) (hμ : ∀ x j, 0 ≤ μ x j) (n ru rv : ℕ) (hru : ru ≤ n) (hrv : rv ≤ n)
    (u v : α) (hu : u ∈ Λ) (hv : v ∈ Λ) (qu qv : ℕ → ℝ)
    (hcompu : ∀ k, qu k ≤ μ u ((k : ℤ) - (ru : ℤ)).natAbs)
    (hcompv : ∀ k, qv k ≤ μ v ((k : ℤ) - (rv : ℤ)).natAbs) :
    ∑ k ∈ Finset.Icc 1 n, (qu k + qv k)
      ≤ 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), μ x j) := by
  rw [Finset.sum_add_distrib]
  have hu' := oc_revealment_sum_bound Λ hne μ hμ n ru hru u hu qu hcompu
  have hv' := oc_revealment_sum_bound Λ hne μ hμ n rv hrv v hv qv hcompv
  have hsum : ∑ k ∈ Finset.Icc 1 n, qu k + ∑ k ∈ Finset.Icc 1 n, qv k
      ≤ 2 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), μ x j)
        + 2 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), μ x j) :=
    add_le_add hu' hv'
  linarith












theorem oc_eq_revealment_family_sum_le {α : Type*} (Λ : Finset α) (hne : Λ.Nonempty)
    (μ : α → ℕ → ℝ) (hμ : ∀ x j, 0 ≤ μ x j) (n ru rv : ℕ) (hru : ru ≤ n) (hrv : rv ≤ n)
    (u v : α) (hu : u ∈ Λ) (hv : v ∈ Λ) (qu qv : ℕ → ℝ)
    (hcompu : ∀ k, qu k ≤ μ u ((k : ℤ) - (ru : ℤ)).natAbs)
    (hcompv : ∀ k, qv k ≤ μ v ((k : ℤ) - (rv : ℤ)).natAbs) :
    oc_box_crossing_scale_sum Λ hne μ hμ n ru rv hru hrv u v hu hv qu qv hcompu hcompv
      = StatMech.OSSS.revealment_family_sum_le Λ hne μ hμ n ru rv hru hrv u v hu hv qu qv
          hcompu hcompv := by
  rfl

end Walls
end StatMech
