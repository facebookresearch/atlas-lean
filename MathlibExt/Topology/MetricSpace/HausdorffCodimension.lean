/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Hausdorff codimension at least `c` in dimension `n`

`Set.HasHausdorffCodimAtLeast S n c` means `S = ∅ ∨ dimH S + c ≤ n` in `ℝ≥0∞`.
The `S = ∅` disjunct implements `dimH ∅ = -∞` (Mathlib has `dimH ∅ = 0`).
Truncated `↑(n - c)` is avoided in the definition: it would accept e.g. a point
as codimension 3 in dimension 2; see `hasHausdorffCodimAtLeast_iff`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Set

variable {X : Type*} [EMetricSpace X]

/-- **Lower bound on Hausdorff codimension.** Let $S$ be a subset of an extended metric space
and let $n, c$ be natural numbers. The set $S$ has Hausdorff codimension at least $c$ in
dimension $n$ if $S$ is empty or its Hausdorff dimension satisfies $\dim_H S + c \le n$, the
inequality being taken in $[0, \infty]$.

The empty-set case plays the role of the convention $\dim_H \emptyset = -\infty$. -/
def HasHausdorffCodimAtLeast (S : Set X) (n c : ℕ) : Prop :=
  S = ∅ ∨ dimH S + (c : ℝ≥0∞) ≤ (n : ℝ≥0∞)

/-- **The empty set has every codimension.** In an extended metric space, the empty set has
Hausdorff codimension at least $c$ in dimension $n$ for all natural numbers $n$ and $c$. -/
theorem hasHausdorffCodimAtLeast_empty (n c : ℕ) :
    (∅ : Set X).HasHausdorffCodimAtLeast n c :=
  Or.inl rfl

/-- **Subsets inherit a codimension bound.** Let $T \subseteq S$ be subsets of an extended
metric space and let $n, c$ be natural numbers. If $S$ has Hausdorff codimension at least $c$
in dimension $n$, then so does $T$. -/
theorem HasHausdorffCodimAtLeast.mono {S T : Set X} {n c : ℕ}
    (hS : S.HasHausdorffCodimAtLeast n c) (hTS : T ⊆ S) :
    T.HasHausdorffCodimAtLeast n c := by
  rcases hS with rfl | h
  · exact Or.inl (Set.subset_empty_iff.mp hTS)
  · exact Or.inr (le_trans (add_le_add_left (dimH_mono hTS) _) h)

/-- **Sets of codimension larger than the dimension are empty.** Let $S$ be a subset of an
extended metric space and let $n < c$ be natural numbers. If $S$ has Hausdorff codimension at
least $c$ in dimension $n$, then $S$ is empty. -/
theorem HasHausdorffCodimAtLeast.eq_empty_of_lt {S : Set X} {n c : ℕ}
    (hS : S.HasHausdorffCodimAtLeast n c) (hlt : n < c) : S = ∅ := by
  rcases hS with rfl | h
  · rfl
  · have hc : (c : ℝ≥0∞) ≤ dimH S + (c : ℝ≥0∞) := le_add_self
    have hle : (c : ℝ≥0∞) ≤ (n : ℝ≥0∞) := le_trans hc h
    have hcn : c ≤ n := by exact_mod_cast hle
    exact absurd hcn (by omega)

/-- **A dimension bound gives a codimension bound.** Let $S$ be a subset of an extended metric
space and let $c \le n$ be natural numbers. If the Hausdorff dimension of $S$ satisfies
$\dim_H S \le n - c$, then $S$ has Hausdorff codimension at least $c$ in dimension $n$. -/
theorem hasHausdorffCodimAtLeast_of_dimH_le {S : Set X} {n c : ℕ}
    (hcn : c ≤ n) (hdim : dimH S ≤ ((n - c : ℕ) : ℝ≥0∞)) :
    S.HasHausdorffCodimAtLeast n c := by
  refine Or.inr ?_
  have hnc : (n : ℝ≥0∞) = ((n - c : ℕ) : ℝ≥0∞) + (c : ℝ≥0∞) := by
    rw [← Nat.cast_add, Nat.sub_add_cancel hcn]
  rw [hnc]
  exact add_le_add_left hdim _

/-- **Characterization of Hausdorff codimension.** Let $S$ be a subset of an extended metric
space and let $n, c$ be natural numbers. Then $S$ has Hausdorff codimension at least $c$ in
dimension $n$ if and only if either $S$ is empty, or both $c \le n$ and the Hausdorff
dimension of $S$ satisfies $\dim_H S \le n - c$. -/
theorem hasHausdorffCodimAtLeast_iff {S : Set X} {n c : ℕ} :
    S.HasHausdorffCodimAtLeast n c ↔
      S = ∅ ∨ (c ≤ n ∧ dimH S ≤ ((n - c : ℕ) : ℝ≥0∞)) := by
  constructor
  · rintro (rfl | h)
    · exact Or.inl rfl
    · have hc : (c : ℝ≥0∞) ≤ dimH S + (c : ℝ≥0∞) := le_add_self
      have hle : (c : ℝ≥0∞) ≤ (n : ℝ≥0∞) := le_trans hc h
      have hcn : c ≤ n := by exact_mod_cast hle
      have hnc : (n : ℝ≥0∞) = ((n - c : ℕ) : ℝ≥0∞) + (c : ℝ≥0∞) := by
        rw [← Nat.cast_add, Nat.sub_add_cancel hcn]
      have hle2 : dimH S + (c : ℝ≥0∞) ≤
          ((n - c : ℕ) : ℝ≥0∞) + (c : ℝ≥0∞) := by
        rw [← hnc]; exact h
      have hdim : dimH S ≤ ((n - c : ℕ) : ℝ≥0∞) :=
        (ENNReal.add_le_add_iff_right (ENNReal.natCast_ne_top c)).mp hle2
      exact Or.inr ⟨hcn, hdim⟩
  · rintro (rfl | ⟨hcn, hdim⟩)
    · exact Or.inl rfl
    · exact hasHausdorffCodimAtLeast_of_dimH_le hcn hdim

end Set
