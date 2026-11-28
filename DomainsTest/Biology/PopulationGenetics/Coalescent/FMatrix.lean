/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.FMatrix

/-!
# Tests for the F-matrix encoding of ranked tree shapes

The F matrix of the example of Fig. 2 of Kim, Rosenberg and Palacios (2020); the two ranked tree
shapes with four leaves, their F matrices and their distances `d₁ = d₂ = 1`; two labelings of one
shape, which the F matrix identifies; the metric space structures of `d₁` and `d₂`; the fixed
diagonal of isochronous F matrices; the weight matrices of two genealogies of one shape and their
weighted distance, also in the metric space structure of `d₁ʷ`; a heterochronous history
with two leaves sampled at two times; the boundary case of one leaf; and an `L²`-medoid of a
sample of reals.
-/

@[expose] public section

open Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.FMatrix

open MathlibExt.Biology.PopulationGenetics.Coalescent

/-- The ranked labeled history of `n` genes whose step `i` merges the lineages with labels in
`ps i`. -/
def ofPairs {n : ℕ} (ps : Fin (n - 1) → Finset ℕ)
    (h : ∀ i : Fin (n - 1), (univ.filter fun x : Fin (n - i) => (x : ℕ) ∈ ps i).card = 2) :
    RankedHistory n :=
  fun i => ⟨univ.filter fun x => (x : ℕ) ∈ ps i, h i⟩

/-- The tree of Fig. 2A of the source: the root's children are a leaf and a lineage that
branches at the second change point; then its two children branch in turn. -/
def fig2 : RankedHistory 5 := ofPairs ![{3, 4}, {1, 2}, {1, 2}, {0, 1}] (by decide)

/-- The F matrix of Fig. 2B of the source (rows and columns from the root). -/
example : fig2.fMatrix = !![2, 0, 0, 0; 1, 3, 0, 0; 1, 2, 4, 0; 1, 1, 3, 5] := by
  decide

/-- The caterpillar with four leaves. -/
def caterpillar : RankedHistory 4 := ofPairs ![{2, 3}, {1, 2}, {0, 1}] (by decide)

/-- The caterpillar again, with other leaf labels. -/
def caterpillar' : RankedHistory 4 := ofPairs ![{0, 1}, {0, 1}, {0, 1}] (by decide)

/-- The balanced tree with four leaves. -/
def balanced : RankedHistory 4 := ofPairs ![{2, 3}, {0, 1}, {0, 1}] (by decide)

theorem fMatrix_caterpillar : caterpillar.fMatrix = !![2, 0, 0; 1, 3, 0; 1, 2, 4] := by
  decide

theorem fMatrix_balanced : balanced.fMatrix = !![2, 0, 0; 1, 3, 0; 0, 2, 4] := by
  decide

/-- The two labelings of the caterpillar have the same F matrix, so a relabelling of the genes
carries one history's ancestral partitions to the other's. -/
example : ∃ σ : Equiv.Perm (Fin 4),
    (partitionsOf caterpillar).map (relabelLineages σ) = partitionsOf caterpillar' :=
  (RankedHistory.fMatrix_eq_fMatrix_iff _ _).1 (by decide)

/-- The caterpillar and the balanced tree have different F matrices, so no relabelling of the
genes relates them. -/
example : ¬ ∃ σ : Equiv.Perm (Fin 4),
    (partitionsOf caterpillar).map (relabelLineages σ) = partitionsOf balanced := by
  rw [← RankedHistory.fMatrix_eq_fMatrix_iff, fMatrix_caterpillar, fMatrix_balanced]
  decide

/-- The diagonal of an isochronous F matrix: `2, 3, 4` for four leaves. -/
example (T : RankedTreeShape 4 1) : T.fMatrix 0 0 = 2 ∧ T.fMatrix 1 1 = 3 ∧ T.fMatrix 2 2 = 4 :=
  ⟨T.fMatrix_diag_of_isochronous 0, T.fMatrix_diag_of_isochronous 1,
    T.fMatrix_diag_of_isochronous 2⟩

/-- The two ranked tree shapes with four leaves are at `L¹` distance `1`. -/
theorem d₁_caterpillar_balanced :
    RankedTreeShape.d₁ caterpillar.rankedTreeShape balanced.rankedTreeShape = 1 := by
  simp only [RankedTreeShape.d₁, RankedHistory.fMatrix_rankedTreeShape, fMatrix_caterpillar,
    fMatrix_balanced]
  have h0 : Finset.Iic (0 : Fin 3) = {0} := by decide
  have h1 : Finset.Iic (1 : Fin 3) = {0, 1} := by decide
  have h2 : Finset.Iic (2 : Fin 3) = {0, 1, 2} := by decide
  simp [Fin.sum_univ_three, h0, h1, h2]

/-- The two ranked tree shapes with four leaves are at `L²` distance `1`. -/
theorem d₂_caterpillar_balanced :
    RankedTreeShape.d₂ caterpillar.rankedTreeShape balanced.rankedTreeShape = 1 := by
  simp only [RankedTreeShape.d₂, RankedHistory.fMatrix_rankedTreeShape, fMatrix_caterpillar,
    fMatrix_balanced]
  have h0 : Finset.Iic (0 : Fin 3) = {0} := by decide
  have h1 : Finset.Iic (1 : Fin 3) = {0, 1} := by decide
  have h2 : Finset.Iic (2 : Fin 3) = {0, 1, 2} := by decide
  simp [Fin.sum_univ_three, h0, h1, h2]

/-- The same distances in the metric space structures. -/
example : RankedTreeShape.metricSpaceD₁.dist caterpillar.rankedTreeShape
      balanced.rankedTreeShape = 1 ∧
    RankedTreeShape.metricSpaceD₂.dist caterpillar.rankedTreeShape
      balanced.rankedTreeShape = 1 := by
  rw [RankedTreeShape.dist_metricSpaceD₁, RankedTreeShape.dist_metricSpaceD₂]
  exact ⟨d₁_caterpillar_balanced, d₂_caterpillar_balanced⟩

/-- Distinct ranked tree shapes are at positive distance. -/
example : 0 < RankedTreeShape.d₁ caterpillar.rankedTreeShape balanced.rankedTreeShape := by
  let _ := RankedTreeShape.metricSpaceD₁ (n := 4) (m := 1)
  rw [← RankedTreeShape.dist_metricSpaceD₁]
  refine dist_pos.2 fun h => ?_
  have := congrArg RankedTreeShape.fMatrix h
  rw [RankedHistory.fMatrix_rankedTreeShape, RankedHistory.fMatrix_rankedTreeShape,
    fMatrix_caterpillar, fMatrix_balanced] at this
  revert this
  decide

/-- The ranked labeled history of three genes. -/
def three : RankedHistory 3 := ofPairs ![{1, 2}, {0, 1}] (by decide)

theorem fMatrix_three : three.fMatrix = !![2, 0; 1, 3] := by
  decide

/-- The genealogy of the ranked tree shape with three leaves with change points at times
`0, 1, 3`. -/
noncomputable def genealogy₁ : RankedGenealogy 3 1 where
  shape := three.rankedTreeShape
  time := ![0, 1, 3]
  strictMono_time := Fin.strictMono_iff_lt_succ.2 fun i => by fin_cases i <;> norm_num
  time_zero _ := rfl

/-- The same shape with change points at times `0, 2, 3`. -/
noncomputable def genealogy₂ : RankedGenealogy 3 1 where
  shape := three.rankedTreeShape
  time := ![0, 2, 3]
  strictMono_time := Fin.strictMono_iff_lt_succ.2 fun i => by fin_cases i <;> norm_num
  time_zero _ := rfl

/-- The weight matrix of `genealogy₁`: interval lengths `2` (below the root) and `1`, and the
span `3` from the most recent interval to the top of the one below the root. -/
theorem weightMatrix_genealogy₁ : genealogy₁.weightMatrix = !![2, 0; 3, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [RankedGenealogy.weightMatrix, genealogy₁]

theorem weightMatrix_genealogy₂ : genealogy₂.weightMatrix = !![1, 0; 3, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [RankedGenealogy.weightMatrix, genealogy₂]

/-- The weighted matrices `F ∘ W` are `[[4, 0], [3, 3]]` and `[[2, 0], [3, 6]]`, at weighted
`L¹` distance `2 + 0 + 3 = 5`. -/
theorem dw₁_genealogy₁_genealogy₂ : RankedGenealogy.dw₁ genealogy₁ genealogy₂ = 5 := by
  have hs₁ : genealogy₁.shape.fMatrix = !![2, 0; 1, 3] := fMatrix_three
  have hs₂ : genealogy₂.shape.fMatrix = !![2, 0; 1, 3] := fMatrix_three
  have h0 : Finset.Iic (0 : Fin 2) = {0} := by decide
  have h1 : Finset.Iic (1 : Fin 2) = {0, 1} := by decide
  change ∑ i : Fin 2, ∑ j ∈ Iic i, |(genealogy₁.shape.fMatrix i j : ℝ) *
    genealogy₁.weightMatrix i j - genealogy₂.shape.fMatrix i j * genealogy₂.weightMatrix i j| = 5
  rw [hs₁, hs₂, weightMatrix_genealogy₁, weightMatrix_genealogy₂, Fin.sum_univ_two, h0, h1]
  norm_num

/-- The same distance in the metric space structure on isochronous genealogies. -/
example : RankedGenealogy.metricSpaceDw₁OfIsochronous.dist genealogy₁ genealogy₂ = 5 := by
  rw [RankedGenealogy.dist_metricSpaceDw₁OfIsochronous, dw₁_genealogy₁_genealogy₂]

/-- The heterochronous history with leaf `0` sampled at the present, leaf `1` sampled earlier,
and the root above both. -/
def hetero : LabeledRankedHistory 2 2 where
  lineages := [{{0}}, {{0}, {1}}, {univ}]
  length_lineages := rfl
  initial := ⟨{0}, by decide, by decide⟩
  step t ht := by
    have ht' : t < 2 := by omega
    interval_cases t
    · exact Or.inr ⟨{1}, by decide, by decide, by decide⟩
    · exact Or.inl ⟨{0}, by decide, {1}, by decide, by decide, by decide⟩
  root := by decide

/-- Its F matrix: two lineages below the root, of which one persists to the most recent
interval, which has one lineage. -/
example : hetero.fMatrix = !![2, 0; 1, 1] := by
  decide

/-- With one leaf there is one ranked tree shape. -/
example (T₁ T₂ : RankedTreeShape 1 1) : T₁ = T₂ :=
  RankedTreeShape.fMatrix_injective (Matrix.ext fun i _ => absurd i.isLt (by norm_num))

/-- An `L²`-medoid of the sample `0, 1, 5` of reals for the distance `|x - y|`. -/
example : (1 : ℝ) ∈ l2MedoidSet (fun x y : ℝ => |x - y|) ![0, 1, 5] := by
  refine ⟨⟨1, rfl⟩, fun k => ?_⟩
  fin_cases k <;> norm_num [Fin.sum_univ_three]

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.FMatrix
