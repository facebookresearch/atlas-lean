/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.PathShortening

@[expose] public section

/-!
# Local-convexity path shortening

A variant of the local shortening lemma where the bend point only needs a
neighborhood whose intersection with the feasible set is convex, instead of
lying in the interior. This is the form needed at obstacle boundary points.
-/

open Metric

namespace Cslib.Planning.MotionPlanning.PathShortening

open Topology

/-- (L-loc) Local shortening at a non-between bend with a locally convex neighborhood.

Shortcutting the bend with nearby points on the two incident segments yields a
strictly shorter feasible polyline. Feasibility of the shortcut segment comes
from convexity of `U ∩ F` rather than from an interior ball. -/
theorem local_shortening_of_locally_convex (F : Set plane) (l₁ l₂ : List plane) (a b c : plane)
    (h : Feasible F (l₁ ++ [a, b, c] ++ l₂))
    (hconv : ∃ U ∈ 𝓝 b, Convex ℝ (U ∩ F))
    (hb : ¬ Wbtw ℝ a b c) :
    ∀ ε > 0, ∃ a' c', a' ∈ segment ℝ a b ∧ c' ∈ segment ℝ b c ∧
      dist a' b < ε ∧ dist c' b < ε ∧
      Feasible F (l₁ ++ [a, a', c', c] ++ l₂) ∧
      polyLen (l₁ ++ [a, a', c', c] ++ l₂) < polyLen (l₁ ++ [a, b, c] ++ l₂) := by
  intro ε hε
  exact local_shortening_core F l₁ l₂ a b c h hconv hb ε hε

/-- (T0-loc) A length-minimal feasible polyline is weakly between at every bend
with a locally convex feasible neighborhood. -/
theorem wbtw_of_minimal_of_locally_convex (F : Set plane) (l₁ l₂ : List plane) (a b c : plane)
    (hfeas : Feasible F (l₁ ++ [a, b, c] ++ l₂))
    (hconv : ∃ U ∈ 𝓝 b, Convex ℝ (U ∩ F))
    (hmin : ∀ l' : List plane, Feasible F l' →
      l'.head? = (l₁ ++ [a, b, c] ++ l₂).head? →
      l'.getLast? = (l₁ ++ [a, b, c] ++ l₂).getLast? →
      polyLen (l₁ ++ [a, b, c] ++ l₂) ≤ polyLen l') :
    Wbtw ℝ a b c := by
  by_contra hbc
  obtain ⟨a', c', _, _, _, _, hfeas', hlt⟩ :=
    local_shortening_of_locally_convex F l₁ l₂ a b c hfeas hconv hbc 1 one_pos
  have hhead : (l₁ ++ [a, a', c', c] ++ l₂).head? = (l₁ ++ [a, b, c] ++ l₂).head? := by simp
  have hlast : (l₁ ++ [a, a', c', c] ++ l₂).getLast? = (l₁ ++ [a, b, c] ++ l₂).getLast? := by simp
  have hle := hmin _ hfeas' hhead hlast
  linarith

end Cslib.Planning.MotionPlanning.PathShortening
