/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.TDA.PersistenceModule

@[expose] public section

open CategoryTheory MathlibExt.Topology.TDA Metric

/-- The interval module of `[0, 1]` has fibre `k` (functions on a point) at `1/2`. -/
example : (intervalModule ℚ (Set.Icc (0 : ℝ) 1) Set.ordConnected_Icc).obj (1 / 2) =
    ModuleCat.of ℚ (PLift ((1 / 2 : ℝ) ∈ Set.Icc 0 1) → ℚ) :=
  rfl

/-- Composing interleavings adds their scales. -/
noncomputable example (U : ℝ ⥤ ModuleCat.{0} ℚ) : Interleaving U U (1 + 2) :=
  (Interleaving.refl U zero_le_one).trans (Interleaving.refl U zero_le_two)

example (U V : ℝ ⥤ ModuleCat.{0} ℚ) (e : Interleaving U V 1) : Interleaving V U 1 := e.symm

/-- No interleaving at a negative scale. -/
example (U V : ℝ ⥤ ModuleCat.{0} ℚ) {δ : ℝ} (e : Interleaving U V δ) : 0 ≤ δ := e.nonneg

/-- No matching at a negative scale, even between empty barcodes. -/
example {ι κ : Type} (I : ι → Set ℝ) (J : κ → Set ℝ) : ¬ IsMatching I J (-1) :=
  fun h => by linarith [h.1]

/-- Empty barcodes are `0`-matched: the hypotheses of the converse stability statement can hold. -/
example : IsMatching (fun e : PEmpty => e.elim) (fun e : PEmpty => e.elim) 0 :=
  ⟨le_rfl, fun _ _ => False, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    fun e => e.elim, fun e => e.elim⟩

/-- A bar is `0`-matched with itself. -/
example : IsMatching (fun _ : Unit => Set.Icc (0 : ℝ) 1) (fun _ : Unit => Set.Icc (0 : ℝ) 1) 0 :=
  ⟨le_rfl, fun _ _ => True, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ => by simp [hausdorffEDist_self], fun _ h => (h () trivial).elim,
    fun _ h => (h () trivial).elim⟩

/-- Two distinct bars `[0, 1]` and `[1/2, 3/2]` are `1/2`-matched: their endpoints differ by
`1/2` (`hausdorffEDist_Icc_Icc`). -/
example : IsMatching (fun _ : Unit => Set.Icc (0 : ℝ) 1)
    (fun _ : Unit => Set.Icc (1 / 2 : ℝ) (3 / 2)) (1 / 2) := by
  refine ⟨by norm_num, fun _ _ => True, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ => ?_, fun _ h => (h () trivial).elim, fun _ h => (h () trivial).elim⟩
  rw [hausdorffEDist_Icc_Icc (by norm_num) (by norm_num)]
  norm_num [abs_of_neg, abs_of_nonneg]

/-- The Hausdorff distance between closed intervals is the endpoint distance. -/
example : hausdorffEDist (Set.Icc (0 : ℝ) 1) (Set.Icc 3 7) = ENNReal.ofReal 6 := by
  rw [hausdorffEDist_Icc_Icc (by norm_num) (by norm_num)]
  norm_num [abs_of_neg]

/-- Open and closed ends are not distinguished: `[0, 1)` and `[0, 1]` are at distance `0`, as
the undecorated persistence diagram forgets decorations. -/
example : hausdorffEDist (Set.Ico (0 : ℝ) 1) (Set.Icc 0 1) = 0 := by
  rw [← hausdorffEDist_closure, closure_Ico (by norm_num : (0 : ℝ) ≠ 1), closure_Icc,
    hausdorffEDist_self]

/-- Two infinite bars `[0, ∞)` and `[1, ∞)` are `1`-matched. -/
example : IsMatching (fun _ : Unit => Set.Ici (0 : ℝ)) (fun _ : Unit => Set.Ici (1 : ℝ)) 1 := by
  refine ⟨zero_le_one, fun _ _ => True, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ => ?_, fun _ h => (h () trivial).elim, fun _ h => (h () trivial).elim⟩
  refine hausdorffEDist_le_of_mem_edist (fun x hx => ⟨x + 1, ?_, ?_⟩) (fun y hy => ⟨y, ?_, ?_⟩)
  · simpa using (show (0 : ℝ) ≤ x from hx)
  · simp [edist_dist, Real.dist_eq]
  · exact le_trans zero_le_one hy
  · simp

/-- An infinite bar is never within `δ` of the diagonal, so it can never stay unmatched. -/
example (δ : ℝ) : ¬ ∃ a, Set.Ici (0 : ℝ) ⊆ Set.Icc a (a + 2 * δ) := by
  rintro ⟨a, h⟩
  have := (h (show max 0 (a + 2 * δ + 1) ∈ Set.Ici (0 : ℝ) from le_max_left _ _)).2
  linarith [le_max_right 0 (a + 2 * δ + 1)]

/-- A short bar may stay unmatched: `[0, 1]` against the empty barcode at `δ = 1/2`. -/
example : IsMatching (fun _ : Unit => Set.Icc (0 : ℝ) 1) (fun e : Empty => e.elim) (1 / 2) :=
  ⟨by norm_num, fun _ _ => False, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim,
    fun _ _ h => h.elim, fun _ _ => ⟨0, by norm_num⟩, fun e => e.elim⟩
