/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.PathShortening
public meta import CSLibExt.Planning.MotionPlanning.PathShortening

/-!
# Path shortening tests

Concrete length/feasibility computations, an instantiated shortening example,
and axiom probes for `CSLibExt.Planning.MotionPlanning.PathShortening`.
-/

/-!
# Tests for path shortening

The main file above is the repaired `PathShortening.lean` verbatim.
The checks below restore concrete computations for `polyLen` and `Feasible`,
pin the strengthened conclusion shape of `local_shortening`
(on-segment, ε-close replacement points) and the unchanged statement of
`wbtw_of_minimal`, and print the axioms both theorems depend on.
-/

open Metric Cslib.Planning.MotionPlanning Cslib.Planning.MotionPlanning.PathShortening

example : polyLen [(!₂[0, 0] : plane), (!₂[1, 0] : plane), (!₂[1, 1] : plane)] = 2 := by
  have h1 : dist (!₂[0, 0] : plane) (!₂[1, 0] : plane) = 1 := by
    rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two]
  have h2 : dist (!₂[1, 0] : plane) (!₂[1, 1] : plane) = 1 := by
    rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two]
  simp only [polyLen_cons_cons, polyLen_singleton, h1, h2]
  norm_num

example : polyLen [(!₂[0, 0] : plane), (!₂[3, 4] : plane)] = 5 := by
  have h : dist (!₂[0, 0] : plane) (!₂[3, 4] : plane) = 5 := by
    rw [EuclideanSpace.dist_eq]
    simp only [Fin.sum_univ_two]
    norm_num
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  simp only [polyLen_cons_cons, polyLen_singleton, h]
  norm_num

example : polyLen ([] : List plane) = 0 :=
  polyLen_nil

example (p : plane) : polyLen [p] = 0 :=
  polyLen_singleton p

example : Feasible Set.univ [(!₂[0, 0] : plane), (!₂[1, 0] : plane), (!₂[1, 1] : plane)] := by
  simp [feasible_cons_cons]

example : ¬ Feasible ∅ [(!₂[0, 0] : plane), (!₂[1, 0] : plane), (!₂[1, 1] : plane)] := by
  intro h
  simp only [feasible_cons_cons] at h
  obtain ⟨hsub, -⟩ := h
  have hmem := hsub (left_mem_segment ℝ _ _)
  simp at hmem

example : Wbtw ℝ (!₂[0, 0] : plane) (!₂[1, 0] : plane) (!₂[2, 0] : plane)
    ∧ dist (!₂[0, 0] : plane) (!₂[1, 0] : plane)
      + dist (!₂[1, 0] : plane) (!₂[2, 0] : plane)
      = dist (!₂[0, 0] : plane) (!₂[2, 0] : plane) := by
  have h1 : dist (!₂[0, 0] : plane) (!₂[1, 0] : plane) = 1 := by
    rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two]
  have h2 : dist (!₂[1, 0] : plane) (!₂[2, 0] : plane) = 1 := by
    rw [EuclideanSpace.dist_eq]
    simp only [Fin.sum_univ_two]
    norm_num [Real.dist_eq]
  have h3 : dist (!₂[0, 0] : plane) (!₂[2, 0] : plane) = 2 := by
    rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two]
  have heq : dist (!₂[0, 0] : plane) (!₂[1, 0] : plane)
      + dist (!₂[1, 0] : plane) (!₂[2, 0] : plane)
      = dist (!₂[0, 0] : plane) (!₂[2, 0] : plane) := by
    rw [h1, h2, h3]
    norm_num
  exact ⟨dist_add_dist_eq_iff.mp heq, heq⟩

-- `Feasible` on three points is the two segment inclusions plus last-point membership.
example (F : Set plane) (x y z : plane) :
    Feasible F [x, y, z] ↔ segment ℝ x y ⊆ F ∧ segment ℝ y z ⊆ F ∧ z ∈ F :=
  Iff.rfl

-- The endpoints of a feasible edge lie in `F`.
example (F : Set plane) (x y : plane) (h : Feasible F [x, y]) : x ∈ F ∧ y ∈ F := by
  simp only [feasible_cons_cons] at h
  exact ⟨h.1 (left_mem_segment ℝ x y), h.2⟩

-- A one-vertex polyline at an interior point of a concrete box is feasible.
example : Feasible {p : plane | p 0 ∈ Set.Ioo (0:ℝ) 2 ∧ p 1 ∈ Set.Ioo (0:ℝ) 2}
    [(!₂[1, 1] : plane)] := by
  show (!₂[1, 1] : plane) ∈ {p : plane | p 0 ∈ Set.Ioo (0:ℝ) 2 ∧ p 1 ∈ Set.Ioo (0:ℝ) 2}
  simp only [Set.mem_Ioo]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_succ]

-- A one-vertex polyline at an exterior point of the box is not feasible.
example : ¬ Feasible {p : plane | p 0 ∈ Set.Ioo (0:ℝ) 2 ∧ p 1 ∈ Set.Ioo (0:ℝ) 2}
    [(!₂[5, 1] : plane)] := by
  intro h
  have h' : (!₂[5, 1] : plane) ∈ {p : plane | p 0 ∈ Set.Ioo (0:ℝ) 2 ∧ p 1 ∈ Set.Ioo (0:ℝ) 2} := h
  simp only [Set.mem_Ioo] at h'
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_succ] at h'

-- A one-vertex polyline is never feasible for the empty set.
example : ¬ Feasible (∅ : Set plane) [(!₂[0, 0] : plane)] := by
  intro h
  exact Set.notMem_empty _ h

-- A two-point polyline needs its single-vertex tail in `F`.
example (F : Set plane) (x y : plane) (hseg : segment ℝ x y ⊆ F) (hy : y ∈ F) :
    Feasible F [x, y] := by
  simp only [feasible_cons_cons]
  exact ⟨hseg, hy⟩

-- Length splits over a junction written with appends.
example : polyLen ([(!₂[0, 0] : plane)] ++ [(!₂[1, 0] : plane), (!₂[1, 1] : plane)]
      ++ [(!₂[2, 1] : plane)])
    = dist (!₂[0, 0] : plane) (!₂[1, 0] : plane)
      + dist (!₂[1, 0] : plane) (!₂[1, 1] : plane)
      + dist (!₂[1, 1] : plane) (!₂[2, 1] : plane) := by
  simp only [List.cons_append, List.nil_append, polyLen_cons_cons,
    polyLen_singleton, add_zero]
  ring

-- An out-and-back spike has twice the one-way length.
example : polyLen [(!₂[0, 0] : plane), (!₂[1, 0] : plane), (!₂[0, 0] : plane)]
    = 2 * dist (!₂[0, 0] : plane) (!₂[1, 0] : plane) := by
  rw [polyLen_cons_cons, polyLen_cons_cons, polyLen_singleton, add_zero,
    dist_comm (!₂[1, 0] : plane) (!₂[0, 0] : plane)]
  ring

-- Instantiating `local_shortening` at the right-angle bend gives on-segment
-- witnesses strictly below the computed original length 2.
example : ∃ a' c' : plane,
    a' ∈ segment ℝ (!₂[0, 0] : plane) (!₂[1, 0] : plane) ∧
    c' ∈ segment ℝ (!₂[1, 0] : plane) (!₂[1, 1] : plane) ∧
    dist a' (!₂[1, 0] : plane) < 1 ∧ dist c' (!₂[1, 0] : plane) < 1 ∧
    Feasible Set.univ
      ([] ++ [(!₂[0, 0] : plane), a', c', (!₂[1, 1] : plane)] ++ []) ∧
    polyLen ([] ++ [(!₂[0, 0] : plane), a', c', (!₂[1, 1] : plane)] ++ []) < 2 := by
  have h1 : dist (!₂[0, 0] : plane) (!₂[1, 0] : plane) = 1 := by
    rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two]
  have h2 : dist (!₂[1, 0] : plane) (!₂[1, 1] : plane) = 1 := by
    rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two]
  have hdiag : dist (!₂[0, 0] : plane) (!₂[1, 1] : plane) = Real.sqrt 2 := by
    rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two]
    norm_num
  have hlen : polyLen
      ([] ++ [(!₂[0, 0] : plane), (!₂[1, 0] : plane), (!₂[1, 1] : plane)] ++ []) = 2 := by
    simp only [List.nil_append, List.append_nil, polyLen_cons_cons, polyLen_singleton,
      h1, h2]
    norm_num
  have hfeas : Feasible Set.univ
      ([] ++ [(!₂[0, 0] : plane), (!₂[1, 0] : plane), (!₂[1, 1] : plane)] ++ []) := by
    simp [feasible_cons_cons]
  have hb : (!₂[1, 0] : plane) ∈ interior Set.univ := by simp
  have hbc : ¬ Wbtw ℝ (!₂[0, 0] : plane) (!₂[1, 0] : plane) (!₂[1, 1] : plane) := by
    have hlt : Real.sqrt 2 < 1 + 1 := by
      have hsqrt : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
      linarith
    apply dist_lt_dist_add_dist_iff.mp
    rw [hdiag, h1, h2]
    exact hlt
  obtain ⟨a', c', ha', hc', hda', hdc', hfeas', hlt⟩ :=
    local_shortening Set.univ [] [] _ _ _ hfeas hb hbc 1 one_pos
  rw [hlen] at hlt
  exact ⟨a', c', ha', hc', hda', hdc', hfeas', hlt⟩

-- The strengthened conclusion exposes on-segment ε-close replacement points.
example (F : Set plane) (l₁ l₂ : List plane) (a b c : plane)
    (hfeas : Feasible F (l₁ ++ [a, b, c] ++ l₂))
    (hb : b ∈ interior F) (hbc : ¬ Wbtw ℝ a b c) (ε : ℝ) (hε : 0 < ε) :
    ∃ a' c' : plane, a' ∈ segment ℝ a b ∧ c' ∈ segment ℝ b c ∧
      dist a' b < ε ∧ dist c' b < ε ∧
      Feasible F (l₁ ++ [a, a', c', c] ++ l₂) ∧
      polyLen (l₁ ++ [a, a', c', c] ++ l₂) < polyLen (l₁ ++ [a, b, c] ++ l₂) :=
  local_shortening F l₁ l₂ a b c hfeas hb hbc ε hε

-- Destructuring the new shape yields the replacement points and their facts.
example (F : Set plane) (l₁ l₂ : List plane) (a b c : plane)
    (hfeas : Feasible F (l₁ ++ [a, b, c] ++ l₂))
    (hb : b ∈ interior F) (hbc : ¬ Wbtw ℝ a b c) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : plane, p ∈ segment ℝ a b ∧ dist p b < ε := by
  obtain ⟨a', _, ha', _, hda', _, _, _⟩ :=
    local_shortening F l₁ l₂ a b c hfeas hb hbc ε hε
  exact ⟨a', ha', hda'⟩

-- The minimality corollary keeps its statement.
example (F : Set plane) (l₁ l₂ : List plane) (a b c : plane)
    (hfeas : Feasible F (l₁ ++ [a, b, c] ++ l₂)) (hb : b ∈ interior F)
    (hmin : ∀ l' : List plane, Feasible F l' →
      l'.head? = (l₁ ++ [a, b, c] ++ l₂).head? →
      l'.getLast? = (l₁ ++ [a, b, c] ++ l₂).getLast? →
      polyLen (l₁ ++ [a, b, c] ++ l₂) ≤ polyLen l') :
    Wbtw ℝ a b c :=
  wbtw_of_minimal F l₁ l₂ a b c hfeas hb hmin

#print axioms Cslib.Planning.MotionPlanning.PathShortening.local_shortening
#print axioms Cslib.Planning.MotionPlanning.PathShortening.wbtw_of_minimal
