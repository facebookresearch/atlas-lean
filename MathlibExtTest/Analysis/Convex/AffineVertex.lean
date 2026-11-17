/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

import MathlibExt.Analysis.Convex.AffineVertex

/-!
# Affine vertex checks

Focused checks for `MathlibExt.Analysis.Convex.AffineVertex`: two
vertices `![0, 0]`, `![4, 0]` certify one precedence inequality over
the whole hull through the public schedule theorem, and a negative
duration is rejected at a vertex.

These are elaboration and non-vacuity checks, not new results.
-/

open AffineVertex

/-- Vertex checks certify the hull precedence inequality. -/
example : ∀ x ∈ convexHull ℝ
      (({![0, 0], ![4, 0]} : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)),
      ∀ e ∈ ({(0, 1)} : Finset (Fin 2 × Fin 2)),
        (fun j : Fin 2 => if j = 1 then (5 : ℝ) else 0) e.1
          + affineFun ((fun _ : Fin 2 => (1 : ℝ)) e.1)
            ((fun _ _ : Fin 2 => (1 : ℝ)) e.1) x
          ≤ (fun j : Fin 2 => if j = 1 then (5 : ℝ) else 0) e.2 := by
  rw [schedule_precedence_hull_iff _
    (fun j : Fin 2 => if j = 1 then (5 : ℝ) else 0) (fun _ => (1 : ℝ))
    (fun _ _ : Fin 2 => (1 : ℝ)) _]
  intro v hv e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv he
  obtain rfl := he
  rcases hv with rfl | rfl <;> norm_num [affineFun, Fin.sum_univ_two]

/-- A negative duration at a vertex is rejected. -/
example : ¬ ∀ v ∈ ({![0, 0]} : Finset (Fin 2 → ℝ)),
    ∀ j ∈ ({0} : Finset (Fin 2)),
      0 ≤ affineFun (-1 : ℝ) (fun _ : Fin 2 => (0 : ℝ)) v := by
  intro h
  have hv := h ![0, 0] (by simp) 0 (by simp)
  norm_num [affineFun] at hv

/-- Empty scenario set: both sides of the certificates are vacuous. -/
example : (∀ x ∈ convexHull ℝ ((∅ : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)),
      0 ≤ affineFun 1 (fun _ => (1 : ℝ)) x)
    ↔ ∀ v ∈ (∅ : Finset (Fin 2 → ℝ)), 0 ≤ affineFun 1 (fun _ => (1 : ℝ)) v :=
  affineFun_nonneg_hull_iff _ _ _

/-- The negative-duration rejection goes through the duration
certificate's vertex side. -/
example : ¬ ∀ x ∈ convexHull ℝ (({![0, 0]} : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)),
    ∀ j ∈ ({0} : Finset (Fin 2)),
      0 ≤ affineFun (-1 : ℝ) (fun _ : Fin 2 => (0 : ℝ)) x := by
  rw [durations_nonneg_hull_iff]
  intro h
  have hv := h ![0, 0] (by simp) 0 (by simp)
  norm_num [affineFun] at hv
