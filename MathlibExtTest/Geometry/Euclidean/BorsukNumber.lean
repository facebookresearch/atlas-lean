/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Borsuk cover and optimizer tests
-/
module

import MathlibExt.Geometry.Euclidean.BorsukNumber
import Mathlib.Tactic

open Bornology Metric

private def point : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => 1)

private def pair : Set (EuclideanSpace ℝ (Fin 1)) := {0, point}

private theorem point_ne_zero : point ≠ 0 := by
  intro h
  have hv := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h
  norm_num [point] at hv

private theorem pair_nonempty : pair.Nonempty := by
  exact ⟨0, by simp [pair]⟩

private theorem pair_nontrivial : pair.Nontrivial := by
  exact ⟨0, by simp [pair], point, by simp [pair], point_ne_zero.symm⟩

private theorem pair_diameter_pos : 0 < ediam pair := by
  simpa only [pair, ediam_pair] using edist_pos.mpr point_ne_zero.symm

private theorem pair_cover : HasBorsukCover 2 pair := by
  refine ⟨fun i => if i.val = 0 then {0} else {point}, ?_, ?_⟩
  · intro x hx
    rcases (show x = 0 ∨ x = point by simpa [pair] using hx) with rfl | rfl
    · exact Set.mem_iUnion.mpr ⟨0, by simp⟩
    · exact Set.mem_iUnion.mpr ⟨1, by simp⟩
  · intro i
    dsimp only
    split <;> simpa only [ediam_singleton] using pair_diameter_pos

private theorem pair_no_one_cover : ¬HasBorsukCover 1 pair := by
  rintro ⟨c, hc, hd⟩
  have hsub : pair ⊆ c 0 := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc hx)
    have hi0 : i = 0 := Subsingleton.elim _ _
    simpa only [hi0] using hi
  exact (not_lt_of_ge (ediam_mono hsub)) (hd 0)

private theorem pair_number : setBorsukNumber pair = 2 := by
  apply le_antisymm (setBorsukNumber_le_of_cover pair_cover)
  apply le_iInf
  intro k
  have hk : 2 ≤ k.val := by
    by_contra h
    have hk1 : k.val ≤ 1 := by omega
    exact pair_no_one_cover (hasBorsukCover_mono pair_nonempty k.prop hk1)
  exact_mod_cast hk

example : HasBorsukCover 0 (∅ : Set (EuclideanSpace ℝ (Fin 1))) :=
  ⟨fun i => Fin.elim0 i, by simp, fun i => Fin.elim0 i⟩

example : setBorsukNumber (∅ : Set (EuclideanSpace ℝ (Fin 1))) = 0 := by
  apply le_antisymm _ bot_le
  exact setBorsukNumber_le_of_cover
    ⟨fun i => Fin.elim0 i, by simp, fun i => Fin.elim0 i⟩

example : ¬HasBorsukCover 1 ({0} : Set (EuclideanSpace ℝ (Fin 1))) := by
  rintro ⟨c, _, hd⟩
  have h := hd (0 : Fin 1)
  simp at h

example : setBorsukNumber ({0} : Set (EuclideanSpace ℝ (Fin 1))) = ⊤ := by
  apply ENat.iInf_natCast_eq_top.mpr
  refine ⟨fun k => ?_⟩
  have hk := hasBorsukCover_pos (by simp : ({0} : Set (EuclideanSpace ℝ (Fin 1))).Nonempty)
    k.prop
  obtain ⟨_, _, hd⟩ := k.prop
  have h := hd ⟨0, hk⟩
  simp at h

example : point ≠ 0 := point_ne_zero

example : pair.Nontrivial := pair_nontrivial

example : HasBorsukCover 2 pair := pair_cover

example : ¬HasBorsukCover 1 pair := pair_no_one_cover

example : setBorsukNumber pair = 2 := pair_number

example : setBorsukNumber pair ≤ dimensionBorsukNumber 1 := by
  exact le_iSup_of_le ⟨pair, (by simp [pair] : pair.Finite).isBounded, pair_nontrivial⟩ le_rfl

example : (2 : ℕ∞) ≤ dimensionBorsukNumber 1 := by
  rw [← pair_number]
  exact le_iSup_of_le ⟨pair, (by simp [pair] : pair.Finite).isBounded, pair_nontrivial⟩ le_rfl

example : ∃ c : Fin 2 → Set (EuclideanSpace ℝ (Fin 1)),
    (∀ i, c i ⊆ pair) ∧ pair = ⋃ i, c i ∧ ∀ i, ediam (c i) < ediam pair :=
  hasBorsukCover_iff_exactUnion.mp pair_cover

example : ∃ c : Fin 2 → Set (EuclideanSpace ℝ (Fin 1)),
    pair ⊆ ⋃ i, c i ∧ ∀ i, IsClosed (c i) ∧ ediam (c i) < ediam pair :=
  hasBorsukCover_iff_closedCover.mp pair_cover

example : HasBorsukCover 3 pair :=
  hasBorsukCover_mono pair_nonempty pair_cover (by decide)

example : dimensionBorsukNumber 0 = 0 := by
  apply le_antisymm _ bot_le
  apply dimensionBorsukNumber_le_iff.mpr
  intro s _ hs
  obtain ⟨x, _, y, _, hxy⟩ := hs
  exact False.elim (hxy (Subsingleton.elim _ _))

example : (1 : ℕ∞) ≤ firstBorsukFailureDimension := by
  apply le_iInf
  intro n
  exact_mod_cast (Nat.succ_le_iff.mpr n.prop.1)

example : firstBorsukFailureDimension = ⊤ ↔
    ∀ n : ℕ, 0 < n → dimensionBorsukNumber n ≤ (n + 1 : ℕ∞) :=
  firstBorsukFailureDimension_eq_top_iff

example (n : ℕ) : twoDistanceBorsukNumber n ≤ dimensionBorsukNumber n := by
  apply iSup_le
  intro s
  exact le_iSup_of_le ⟨s.val, s.prop.1, s.prop.2.1⟩ le_rfl
