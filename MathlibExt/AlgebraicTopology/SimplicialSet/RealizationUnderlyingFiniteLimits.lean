/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Sort

/-!
# Finite limits of the underlying geometric realization

The points of the topological standard simplices form a flat cosimplicial
type: their category of elements is cofiltered.  Common refinements are
constructed from the sorted union of cumulative barycentric coordinates, and
parallel maps are equalized by restricting to positive support.  The density
presentation then identifies underlying geometric realization with a
filtered colimit of evaluation functors, hence it preserves finite limits.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Convexity
open CategoryTheory.Functor
open scoped BigOperators Simplicial

namespace SimplexCategory

private def cumulative {n : ℕ} (x : StdSimplex ℝ (Fin (n + 1)))
    (r : Fin (n + 2)) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) ↦ i.val < r.val), x.weights i

@[simp]
private lemma cumulative_zero {n : ℕ} (x : StdSimplex ℝ (Fin (n + 1))) :
    cumulative x 0 = 0 := by
  simp [cumulative]

@[simp]
private lemma cumulative_last {n : ℕ} (x : StdSimplex ℝ (Fin (n + 1))) :
    cumulative x (Fin.last (n + 1)) = 1 := by
  rw [cumulative, Finset.filter_eq_self.mpr]
  · exact x.total_of_fintype
  · intro i _
    simpa using i.isLt

private lemma cumulative_mono {n : ℕ} (x : StdSimplex ℝ (Fin (n + 1))) :
    Monotone (cumulative x) := by
  intro r s hrs
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact lt_of_lt_of_le hi (Fin.le_iff_val_le_val.mp hrs)
  · intro i _ _
    exact x.weights_nonneg i

private lemma cumulative_succ {n : ℕ} (x : StdSimplex ℝ (Fin (n + 1)))
    (r : Fin (n + 1)) :
    cumulative x r.succ = cumulative x r.castSucc + x.weights r := by
  rw [cumulative, cumulative]
  have hfilter :
      Finset.univ.filter (fun i : Fin (n + 1) ↦ i.val < r.succ.val) =
        insert r (Finset.univ.filter (fun i : Fin (n + 1) ↦ i.val < r.castSucc.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.val_succ, Fin.val_castSucc]
    omega
  rw [hfilter, Finset.sum_insert]
  · ac_rfl
  · simp

private lemma cumulative_nonneg {n : ℕ} (x : StdSimplex ℝ (Fin (n + 1)))
    (r : Fin (n + 2)) : 0 ≤ cumulative x r := by
  simpa using cumulative_mono x (Fin.zero_le r)

private lemma cumulative_le_one {n : ℕ} (x : StdSimplex ℝ (Fin (n + 1)))
    (r : Fin (n + 2)) : cumulative x r ≤ 1 := by
  simpa using cumulative_mono x (Fin.le_last r)

private noncomputable def breakpoints {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) : Finset ℝ :=
  Finset.univ.image (cumulative x) ∪ Finset.univ.image (cumulative y)

private lemma zero_mem_breakpoints {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    0 ∈ breakpoints x y := by
  classical
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, cumulative_zero x⟩

private lemma one_mem_breakpoints {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    1 ∈ breakpoints x y := by
  classical
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr
    ⟨Fin.last (n + 1), Finset.mem_univ _, cumulative_last x⟩

private lemma breakpoints_mem_Icc {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    {t : ℝ} (ht : t ∈ breakpoints x y) : t ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  simp only [breakpoints, Finset.mem_union, Finset.mem_image] at ht
  rcases ht with ⟨r, _, rfl⟩ | ⟨r, _, rfl⟩
  · exact ⟨cumulative_nonneg x r, cumulative_le_one x r⟩
  · exact ⟨cumulative_nonneg y r, cumulative_le_one y r⟩

private lemma two_le_card_breakpoints {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    2 ≤ (breakpoints x y).card := by
  classical
  have hsub : ({0, 1} : Finset ℝ) ⊆ breakpoints x y := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact zero_mem_breakpoints x y
    · exact one_mem_breakpoints x y
  simpa using Finset.card_le_card hsub

private noncomputable def breakpointOrderEmb {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    Fin (breakpoints x y).card ↪o ℝ :=
  (breakpoints x y).orderEmbOfFin rfl

private lemma breakpointOrderEmb_zero {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    breakpointOrderEmb x y
      ⟨0, lt_of_lt_of_le Nat.zero_lt_two (two_le_card_breakpoints x y)⟩ = 0 := by
  classical
  rw [breakpointOrderEmb, Finset.orderEmbOfFin_zero]
  apply le_antisymm
  · exact Finset.min'_le _ _ (zero_mem_breakpoints x y)
  · apply Finset.le_min'
    intro t ht
    exact (breakpoints_mem_Icc x y ht).1

private lemma breakpointOrderEmb_last {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    breakpointOrderEmb x y
      ⟨(breakpoints x y).card - 1, by
        have h := two_le_card_breakpoints x y
        omega⟩ = 1 := by
  classical
  rw [breakpointOrderEmb, Finset.orderEmbOfFin_last rfl (by
    have h := two_le_card_breakpoints x y
    omega)]
  apply le_antisymm
  · apply Finset.max'_le
    intro t ht
    exact (breakpoints_mem_Icc x y ht).2
  · exact Finset.le_max' _ _ (one_mem_breakpoints x y)

private lemma card_sub_one_pos {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    0 < (breakpoints x y).card - 1 := by
  have h := two_le_card_breakpoints x y
  omega

private lemma card_sub_one_add_one {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    (breakpoints x y).card - 1 + 1 = (breakpoints x y).card := by
  have h := two_le_card_breakpoints x y
  omega

private noncomputable def gapLower {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (r : Fin ((breakpoints x y).card - 1)) : ℝ :=
  breakpointOrderEmb x y (Fin.cast (card_sub_one_add_one x y) r.castSucc)

private noncomputable def gapUpper {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (r : Fin ((breakpoints x y).card - 1)) : ℝ :=
  breakpointOrderEmb x y (Fin.cast (card_sub_one_add_one x y) r.succ)

private lemma gapLower_lt_gapUpper {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (r : Fin ((breakpoints x y).card - 1)) :
    gapLower x y r < gapUpper x y r := by
  apply (breakpointOrderEmb x y).strictMono
  simp

private noncomputable def breakpointAt {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (j : ℕ) : ℝ :=
  if h : j < (breakpoints x y).card then
    breakpointOrderEmb x y ⟨j, h⟩
  else 0

@[simp]
private lemma breakpointAt_zero {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    breakpointAt x y 0 = 0 := by
  rw [breakpointAt, dite_eq_left (by
    have h := two_le_card_breakpoints x y
    omega)]
  exact breakpointOrderEmb_zero x y

@[simp]
private lemma breakpointAt_card_sub_one {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    breakpointAt x y ((breakpoints x y).card - 1) = 1 := by
  rw [breakpointAt, dite_eq_left (by
    have h := two_le_card_breakpoints x y
    omega)]
  exact breakpointOrderEmb_last x y

private lemma gapLower_eq_breakpointAt {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (r : Fin ((breakpoints x y).card - 1)) :
    gapLower x y r = breakpointAt x y r.val := by
  rw [gapLower, breakpointAt, dite_eq_left (by
    have h := two_le_card_breakpoints x y
    omega)]
  apply congrArg (breakpointOrderEmb x y)
  ext
  rfl

private lemma gapUpper_eq_breakpointAt {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (r : Fin ((breakpoints x y).card - 1)) :
    gapUpper x y r = breakpointAt x y (r.val + 1) := by
  rw [gapUpper, breakpointAt, dite_eq_left (by
    have h := two_le_card_breakpoints x y
    omega)]
  apply congrArg (breakpointOrderEmb x y)
  ext
  rfl

private lemma breakpointAt_fin {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (j : Fin (breakpoints x y).card) :
    breakpointAt x y j.val = breakpointOrderEmb x y j := by
  rw [breakpointAt, dite_eq_left j.isLt]

private lemma sum_gap_eq_one {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    ∑ r : Fin ((breakpoints x y).card - 1),
      (gapUpper x y r - gapLower x y r) = 1 := by
  calc
    _ = ∑ j ∈ Finset.range ((breakpoints x y).card - 1),
        (breakpointAt x y (j + 1) - breakpointAt x y j) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Fintype.sum_congr
      intro r
      rw [gapUpper_eq_breakpointAt, gapLower_eq_breakpointAt]
    _ = breakpointAt x y ((breakpoints x y).card - 1) - breakpointAt x y 0 :=
      Finset.sum_range_sub _ _
    _ = 1 := by simp

private lemma exists_breakpointIndex {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    {t : ℝ} (ht : t ∈ breakpoints x y) :
    ∃ j : Fin (breakpoints x y).card, breakpointOrderEmb x y j = t := by
  have ht' : t ∈ (breakpoints x y : Set ℝ) := ht
  rw [← (breakpoints x y).range_orderEmbOfFin rfl] at ht'
  exact ht'

private lemma sum_gaps_le_breakpoint {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    {t : ℝ} (ht : t ∈ breakpoints x y) :
    (∑ r : Fin ((breakpoints x y).card - 1),
        if gapUpper x y r ≤ t then gapUpper x y r - gapLower x y r else 0) = t := by
  classical
  obtain ⟨j, rfl⟩ := exists_breakpointIndex x y ht
  calc
    _ = ∑ q ∈ Finset.range j.val,
        (breakpointAt x y (q + 1) - breakpointAt x y q) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_bij (fun r _ ↦ r.val)
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
        simp only [Finset.mem_range]
        change breakpointOrderEmb x y
          (Fin.cast (card_sub_one_add_one x y) r.succ) ≤
            breakpointOrderEmb x y j at hr
        have hle := (breakpointOrderEmb x y).le_iff_le.mp hr
        change r.val + 1 ≤ j.val at hle
        omega
      · intro r₁ _ r₂ _ h
        exact Fin.ext h
      · intro q hq
        simp only [Finset.mem_range] at hq
        have hjk : j.val ≤ (breakpoints x y).card - 1 := by omega
        let r : Fin ((breakpoints x y).card - 1) := ⟨q, hq.trans_le hjk⟩
        refine ⟨r, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change breakpointOrderEmb x y
          (Fin.cast (card_sub_one_add_one x y) r.succ) ≤
            breakpointOrderEmb x y j
        apply (breakpointOrderEmb x y).monotone
        change r.val + 1 ≤ j.val
        change q + 1 ≤ j.val
        omega
      · intro r _
        rw [gapUpper_eq_breakpointAt, gapLower_eq_breakpointAt]
    _ = breakpointAt x y j.val - breakpointAt x y 0 := Finset.sum_range_sub _ _
    _ = breakpointOrderEmb x y j := by rw [breakpointAt_fin]; simp

private noncomputable def couplingSimplex {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    StdSimplex ℝ (Fin ((breakpoints x y).card - 1)) where
  weights := Finsupp.equivFunOnFinite.symm
    (fun r ↦ gapUpper x y r - gapLower x y r)
  nonneg r := by
    change 0 ≤ gapUpper x y r - gapLower x y r
    exact sub_nonneg.mpr (gapLower_lt_gapUpper x y r).le
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    exact sum_gap_eq_one x y

@[simp]
private lemma couplingSimplex_weights {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (r : Fin ((breakpoints x y).card - 1)) :
    (couplingSimplex x y).weights r = gapUpper x y r - gapLower x y r := by
  simp [couplingSimplex]

private lemma cumulative_left_mem_breakpoints {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (i : Fin (n + 2)) : cumulative x i ∈ breakpoints x y := by
  classical
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

private lemma cumulative_right_mem_breakpoints {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (i : Fin (m + 2)) : cumulative y i ∈ breakpoints x y := by
  classical
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

private lemma gapUpper_mem_breakpoints {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (r : Fin ((breakpoints x y).card - 1)) :
    gapUpper x y r ∈ breakpoints x y := by
  change breakpointOrderEmb x y
    (Fin.cast (card_sub_one_add_one x y) r.succ) ∈ breakpoints x y
  exact (breakpoints x y).orderEmbOfFin_mem rfl _

private lemma gapUpper_le_one {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (r : Fin ((breakpoints x y).card - 1)) :
    gapUpper x y r ≤ 1 :=
  (breakpoints_mem_Icc x y (gapUpper_mem_breakpoints x y r)).2

private lemma gapUpper_mono {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    Monotone (gapUpper x y) := by
  intro r s hrs
  apply (breakpointOrderEmb x y).monotone
  change r.val + 1 ≤ s.val + 1
  exact Nat.succ_le_succ (Fin.le_iff_val_le_val.mp hrs)

private lemma exists_leftThreshold {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (r : Fin ((breakpoints x y).card - 1)) :
    ∃ i : Fin (n + 1), gapUpper x y r ≤ cumulative x i.succ := by
  refine ⟨Fin.last n, ?_⟩
  simpa using gapUpper_le_one x y r

private noncomputable def leftIndex {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (r : Fin ((breakpoints x y).card - 1)) : Fin (n + 1) :=
  Fin.find (fun i ↦ gapUpper x y r ≤ cumulative x i.succ)
    (exists_leftThreshold x y r)

private lemma leftIndex_mono {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    Monotone (leftIndex x y) := by
  intro r s hrs
  apply Fin.find_le_of_pos (exists_leftThreshold x y r)
  exact (gapUpper_mono x y hrs).trans
    (Fin.find_spec (exists_leftThreshold x y s))

private noncomputable def leftProjection {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    Fin ((breakpoints x y).card - 1) →o Fin (n + 1) :=
  ⟨leftIndex x y, leftIndex_mono x y⟩

private lemma leftIndex_le_iff {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (r : Fin ((breakpoints x y).card - 1)) (i : Fin (n + 1)) :
    leftIndex x y r ≤ i ↔ gapUpper x y r ≤ cumulative x i.succ := by
  constructor
  · intro h
    exact (Fin.find_spec (exists_leftThreshold x y r)).trans
      (cumulative_mono x (Fin.succ_le_succ_iff.mpr h))
  · exact Fin.find_le_of_pos (exists_leftThreshold x y r)

private lemma exists_rightThreshold {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (r : Fin ((breakpoints x y).card - 1)) :
    ∃ i : Fin (m + 1), gapUpper x y r ≤ cumulative y i.succ := by
  refine ⟨Fin.last m, ?_⟩
  simpa using gapUpper_le_one x y r

private noncomputable def rightIndex {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (r : Fin ((breakpoints x y).card - 1)) : Fin (m + 1) :=
  Fin.find (fun i ↦ gapUpper x y r ≤ cumulative y i.succ)
    (exists_rightThreshold x y r)

private lemma rightIndex_mono {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    Monotone (rightIndex x y) := by
  intro r s hrs
  apply Fin.find_le_of_pos (exists_rightThreshold x y r)
  exact (gapUpper_mono x y hrs).trans
    (Fin.find_spec (exists_rightThreshold x y s))

private noncomputable def rightProjection {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    Fin ((breakpoints x y).card - 1) →o Fin (m + 1) :=
  ⟨rightIndex x y, rightIndex_mono x y⟩

private lemma rightIndex_le_iff {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (r : Fin ((breakpoints x y).card - 1)) (i : Fin (m + 1)) :
    rightIndex x y r ≤ i ↔ gapUpper x y r ≤ cumulative y i.succ := by
  constructor
  · intro h
    exact (Fin.find_spec (exists_rightThreshold x y r)).trans
      (cumulative_mono y (Fin.succ_le_succ_iff.mpr h))
  · exact Fin.find_le_of_pos (exists_rightThreshold x y r)

private noncomputable def cutHom {m : ℕ} (t j : Fin (m + 1)) : ℝ →+ ℝ :=
  if j ≤ t then AddMonoidHom.id ℝ else 0

private noncomputable def massBelow {m : ℕ}
    (x : StdSimplex ℝ (Fin (m + 1))) (t : Fin (m + 1)) : ℝ :=
  x.weights.sum fun j a ↦ cutHom t j a

private lemma massBelow_map {n m : ℕ} (x : StdSimplex ℝ (Fin (n + 1)))
    (α : Fin (n + 1) →o Fin (m + 1)) (t : Fin (m + 1)) :
    massBelow (x.map α) t =
      x.weights.sum (fun i a ↦ cutHom t (α i) a) := by
  rw [massBelow, StdSimplex.weights_map,
    Finsupp.sum_mapDomain_index_addMonoidHom]

private lemma massBelow_eq_cumulative_succ {n : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    massBelow x i = cumulative x i.succ := by
  classical
  rw [massBelow, Finsupp.sum]
  have hcut (a : Fin (n + 1)) :
      cutHom i a (x.weights a) = if a ≤ i then x.weights a else 0 := by
    by_cases h : a ≤ i <;> simp [cutHom, h]
  simp_rw [hcut]
  rw [← Finset.sum_filter]
  rw [cumulative]
  apply Finset.sum_subset
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    have hai := Fin.le_iff_val_le_val.mp ha.2
    change a.val < i.val + 1
    exact Nat.lt_succ_iff.mpr hai
  · intro a ha ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have ha_support : a ∉ x.weights.support := by
      intro ha_support
      apply ha'
      simp only [Finset.mem_filter]
      refine ⟨ha_support, Fin.le_iff_val_le_val.mpr ?_⟩
      have hai : a.val < i.val + 1 := by simpa using ha
      exact Nat.lt_succ_iff.mp hai
    exact Finsupp.notMem_support_iff.mp ha_support

private lemma massBelow_map_lt_of_apply_lt {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1)))
    (α β : Fin (n + 1) →o Fin (m + 1)) {i : Fin (n + 1)}
    (hi : x.weights i ≠ 0) (hiαβ : α i < β i) :
    massBelow (x.map β) (α i) < massBelow (x.map α) (α i) := by
  rw [massBelow_map, massBelow_map, Finsupp.sum, Finsupp.sum]
  apply Finset.sum_lt_sum
  · intro k hk
    by_cases hβ : β k ≤ α i
    · have hki : k < i := by
        by_contra h
        have hik : i ≤ k := le_of_not_gt h
        exact (not_lt_of_ge ((β.monotone hik).trans hβ)) hiαβ
      have hα : α k ≤ α i := α.monotone hki.le
      simp [cutHom, hβ, hα]
    · by_cases hα : α k ≤ α i
      · simp [cutHom, hβ, hα]
      · simp [cutHom, hβ, hα]
  · refine ⟨i, ?_, ?_⟩
    · simpa [Finsupp.mem_support_iff] using hi
    · have hpos : 0 < x.weights i :=
        lt_of_le_of_ne (x.weights_nonneg i) (Ne.symm hi)
      have hβ : ¬ β i ≤ α i := not_le_of_gt hiαβ
      simpa [cutHom, hβ] using hpos

private lemma eq_on_support_of_map_eq {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1)))
    (α β : Fin (n + 1) →o Fin (m + 1))
    (h : x.map α = x.map β) {i : Fin (n + 1)}
    (hi : x.weights i ≠ 0) : α i = β i := by
  apply le_antisymm
  · by_contra hnot
    have hs := massBelow_map_lt_of_apply_lt x β α hi (lt_of_not_ge hnot)
    rw [h] at hs
    exact (lt_irrefl _ hs).elim
  · by_contra hnot
    have hs := massBelow_map_lt_of_apply_lt x α β hi (lt_of_not_ge hnot)
    rw [h] at hs
    exact (lt_irrefl _ hs).elim

private lemma massBelow_coupling_left {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (i : Fin (n + 1)) :
    massBelow ((couplingSimplex x y).map (leftProjection x y)) i =
      cumulative x i.succ := by
  calc
    _ = (couplingSimplex x y).weights.sum
        (fun r a ↦ cutHom i (leftProjection x y r) a) :=
      by
        rw [massBelow, StdSimplex.weights_map,
          Finsupp.sum_mapDomain_index_addMonoidHom]
    _ = _ := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      have hcut (r : Fin ((breakpoints x y).card - 1)) :
          cutHom i (leftProjection x y r) ((couplingSimplex x y).weights r) =
            if gapUpper x y r ≤ cumulative x i.succ then
              gapUpper x y r - gapLower x y r else 0 := by
        rw [couplingSimplex_weights]
        by_cases h : leftIndex x y r ≤ i
        · have hp := (leftIndex_le_iff x y r i).mp h
          simp only [hp, ↓reduceIte]
          simp [cutHom, leftProjection, h]
        · have hp : ¬gapUpper x y r ≤ cumulative x i.succ := by
            simpa [leftIndex_le_iff x y r i] using h
          simp only [hp, ↓reduceIte]
          simp [cutHom, leftProjection, h]
      simp_rw [hcut]
      exact sum_gaps_le_breakpoint x y (cumulative_left_mem_breakpoints x y i.succ)

private lemma massBelow_coupling_right {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1)))
    (i : Fin (m + 1)) :
    massBelow ((couplingSimplex x y).map (rightProjection x y)) i =
      cumulative y i.succ := by
  calc
    _ = (couplingSimplex x y).weights.sum
        (fun r a ↦ cutHom i (rightProjection x y r) a) :=
      by
        rw [massBelow, StdSimplex.weights_map,
          Finsupp.sum_mapDomain_index_addMonoidHom]
    _ = _ := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      have hcut (r : Fin ((breakpoints x y).card - 1)) :
          cutHom i (rightProjection x y r) ((couplingSimplex x y).weights r) =
            if gapUpper x y r ≤ cumulative y i.succ then
              gapUpper x y r - gapLower x y r else 0 := by
        rw [couplingSimplex_weights]
        by_cases h : rightIndex x y r ≤ i
        · have hp := (rightIndex_le_iff x y r i).mp h
          simp only [hp, ↓reduceIte]
          simp [cutHom, rightProjection, h]
        · have hp : ¬gapUpper x y r ≤ cumulative y i.succ := by
            simpa [rightIndex_le_iff x y r i] using h
          simp only [hp, ↓reduceIte]
          simp [cutHom, rightProjection, h]
      simp_rw [hcut]
      exact sum_gaps_le_breakpoint x y (cumulative_right_mem_breakpoints x y i.succ)

private lemma stdSimplex_eq_of_massBelow_eq {n : ℕ}
    {x y : StdSimplex ℝ (Fin (n + 1))}
    (h : ∀ i, massBelow x i = massBelow y i) : x = y := by
  apply StdSimplex.ext
  ext i
  have hsucc : cumulative x i.succ = cumulative y i.succ := by
    simpa only [massBelow_eq_cumulative_succ] using h i
  have hcast : cumulative x i.castSucc = cumulative y i.castSucc := by
    by_cases hi : i = 0
    · subst i
      simp
    · let j : Fin (n + 1) := (i.pred hi).castSucc
      have hj := h j
      rw [massBelow_eq_cumulative_succ, massBelow_eq_cumulative_succ] at hj
      have hj_eq : j.succ = i.castSucc := by
        have hi_val : i.val ≠ 0 := by
          intro hval
          apply hi
          apply Fin.ext
          simpa using hval
        ext
        simp only [j, Fin.val_succ, Fin.val_castSucc, Fin.val_pred]
        omega
      simpa only [hj_eq] using hj
  have hx := cumulative_succ x i
  have hy := cumulative_succ y i
  linarith

private lemma couplingSimplex_map_left {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    (couplingSimplex x y).map (leftProjection x y) = x := by
  apply stdSimplex_eq_of_massBelow_eq
  intro i
  rw [massBelow_coupling_left, ← massBelow_eq_cumulative_succ]

private lemma couplingSimplex_map_right {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    (couplingSimplex x y).map (rightProjection x y) = y := by
  apply stdSimplex_eq_of_massBelow_eq
  intro i
  rw [massBelow_coupling_right, ← massBelow_eq_cumulative_succ]

private theorem exists_monotoneCoupling {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    ∃ (k : ℕ) (_ : 0 < k) (z : StdSimplex ℝ (Fin k))
      (left : Fin k →o Fin (n + 1)) (right : Fin k →o Fin (m + 1)),
      z.map left = x ∧ z.map right = y := by
  exact ⟨(breakpoints x y).card - 1, card_sub_one_pos x y,
    couplingSimplex x y, leftProjection x y, rightProjection x y,
    couplingSimplex_map_left x y, couplingSimplex_map_right x y⟩

private theorem exists_monotoneCouplingDim {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (y : StdSimplex ℝ (Fin (m + 1))) :
    ∃ (d : ℕ) (z : StdSimplex ℝ (Fin (d + 1)))
      (left : Fin (d + 1) →o Fin (n + 1))
      (right : Fin (d + 1) →o Fin (m + 1)),
      z.map left = x ∧ z.map right = y := by
  obtain ⟨k, hk, z, left, right, hl, hr⟩ := exists_monotoneCoupling x y
  have hdk : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk.ne')
  let e : Fin (k - 1 + 1) ≃o Fin k := Fin.castOrderIso hdk
  let eh : Fin (k - 1 + 1) →o Fin k := e.toOrderEmbedding.toOrderHom
  let z' : StdSimplex ℝ (Fin (k - 1 + 1)) := z.map e.symm
  let left' : Fin (k - 1 + 1) →o Fin (n + 1) := left.comp eh
  let right' : Fin (k - 1 + 1) →o Fin (m + 1) := right.comp eh
  refine ⟨k - 1, z', left', right', ?_, ?_⟩
  · simpa [z', left', eh, e, StdSimplex.map_map] using hl
  · simpa [z', right', eh, e, StdSimplex.map_map] using hr

private theorem exists_supportEqualizer {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1)))
    (α β : Fin (n + 1) →o Fin (m + 1)) (h : x.map α = x.map β) :
    ∃ (k : ℕ) (_ : 0 < k) (z : StdSimplex ℝ (Fin k))
      (γ : Fin k →o Fin (n + 1)), z.map γ = x ∧ α.comp γ = β.comp γ := by
  classical
  let s := x.weights.support
  have hs : s.Nonempty := x.support_weights_nonempty
  let γ : Fin s.card →o Fin (n + 1) := (s.orderEmbOfFin rfl).toOrderHom
  have hx : x ∈ Set.range (StdSimplex.map γ) :=
    (StdSimplex.mem_range_map_iff γ x).2 (by
      intro i hi
      apply Finsupp.notMem_support_iff.mp
      intro his
      apply hi
      change i ∈ Set.range ⇑(s.orderEmbOfFin rfl)
      rw [s.range_orderEmbOfFin rfl]
      exact his)
  obtain ⟨z, hz⟩ := hx
  refine ⟨s.card, Finset.card_pos.mpr hs, z, γ, hz, ?_⟩
  ext i
  have hi : γ i ∈ x.weights.support := by
    change s.orderEmbOfFin rfl i ∈ x.weights.support
    exact s.orderEmbOfFin_mem rfl i
  exact congrArg Fin.val
    (eq_on_support_of_map_eq x α β h (Finsupp.mem_support_iff.mp hi))

private theorem exists_supportEqualizerDim {n m : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1)))
    (α β : Fin (n + 1) →o Fin (m + 1)) (h : x.map α = x.map β) :
    ∃ (d : ℕ) (z : StdSimplex ℝ (Fin (d + 1)))
      (γ : Fin (d + 1) →o Fin (n + 1)),
      z.map γ = x ∧ α.comp γ = β.comp γ := by
  obtain ⟨k, hk, z, γ, hz, hγ⟩ := exists_supportEqualizer x α β h
  have hdk : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk.ne')
  let e : Fin (k - 1 + 1) ≃o Fin k := Fin.castOrderIso hdk
  let eh : Fin (k - 1 + 1) →o Fin k := e.toOrderEmbedding.toOrderHom
  let z' : StdSimplex ℝ (Fin (k - 1 + 1)) := z.map e.symm
  let γ' : Fin (k - 1 + 1) →o Fin (n + 1) := γ.comp eh
  refine ⟨k - 1, z', γ', ?_, ?_⟩
  · simpa [z', γ', eh, e, StdSimplex.map_map] using hz
  · ext i
    exact congrArg Fin.val (DFunLike.congr_fun hγ (e i))

private noncomputable abbrev simplexPoints : SimplexCategory ⥤ Type u :=
  SimplexCategory.toTop.{u} ⋙ forget TopCat.{u}

noncomputable instance isCofiltered_elements_toTop_forget :
    IsCofiltered
      (SimplexCategory.toTop.{u} ⋙ forget TopCat.{u}).Elements where
  nonempty := ⟨simplexPoints.{u}.elementsMk ⦋0⦌
    (ULift.up (StdSimplex.single (R := ℝ) (0 : Fin 1)))⟩
  cone_objs p q := by
    obtain ⟨n⟩ := p.obj
    obtain ⟨m⟩ := q.obj
    obtain ⟨d, z, left, right, hleft, hright⟩ :=
      exists_monotoneCouplingDim p.val.down q.val.down
    let r : simplexPoints.{u}.Elements :=
      simplexPoints.{u}.elementsMk ⦋d⦌ (ULift.up z)
    let f : r ⟶ p := Functor.Elements.homMk (SimplexCategory.Hom.mk left) (by
      change ULift.up (z.map left) = p.val
      rw [hleft]
      exact ULift.up_down p.val)
    let g : r ⟶ q := Functor.Elements.homMk (SimplexCategory.Hom.mk right) (by
      change ULift.up (z.map right) = q.val
      rw [hright]
      exact ULift.up_down q.val)
    exact ⟨r, f, g, trivial⟩
  cone_maps {p q} f g := by
    obtain ⟨n⟩ := p.obj
    obtain ⟨m⟩ := q.obj
    have hmap : p.val.down.map f.hom.toOrderHom =
        p.val.down.map g.hom.toOrderHom := by
      have h := congrArg ULift.down (f.map_val.trans g.map_val.symm)
      change StdSimplex.map f.hom.toOrderHom p.val.down =
        StdSimplex.map g.hom.toOrderHom p.val.down at h
      exact h
    obtain ⟨d, z, γ, hz, hγ⟩ :=
      exists_supportEqualizerDim p.val.down f.hom.toOrderHom g.hom.toOrderHom hmap
    let r : simplexPoints.{u}.Elements :=
      simplexPoints.{u}.elementsMk ⦋d⦌ (ULift.up z)
    let h : r ⟶ p := Functor.Elements.homMk (SimplexCategory.Hom.mk γ) (by
      change ULift.up (z.map γ) = p.val
      rw [hz]
      exact ULift.up_down p.val)
    refine ⟨r, h, ?_⟩
    apply Functor.Elements.hom_ext
    apply SimplexCategory.Hom.ext'
    exact hγ

end SimplexCategory

namespace SSet

private noncomputable abbrev standardSimplexPoints : SimplexCategory ⥤ Type u :=
  SimplexCategory.toTop.{u} ⋙ forget TopCat.{u}

private noncomputable abbrev realizationExplicitLan : SSet.{u} ⥤ Type u :=
  (Functor.whiskeringLeft standardSimplexPoints.{u}.Elementsᵒᵖ
      SimplexCategoryᵒᵖ (Type u)).obj
      (Functor.Elements.π standardSimplexPoints.{u}).op ⋙ colim

private noncomputable def realizationExplicitLanExtensionIso :
    standardSimplexPoints.{u} ≅ stdSimplex.{u} ⋙ realizationExplicitLan.{u} :=
  (Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso
    standardSimplexPoints.{u}).symm ≪≫
      (Functor.isoWhiskerRight
        (uliftYonedaIsoShrinkYoneda (C := SimplexCategory))
        realizationExplicitLan.{u}).symm

private noncomputable instance :
    realizationExplicitLan.{u}.IsLeftKanExtension
      realizationExplicitLanExtensionIso.{u}.hom :=
  Presheaf.isLeftKanExtension_along_uliftYoneda_of_preservesColimits
    realizationExplicitLanExtensionIso.{u}.symm

private noncomputable def toTopForgetExtension :
    standardSimplexPoints.{u} ⟶
      stdSimplex.{u} ⋙ (toTop.{u} ⋙ forget TopCat.{u}) :=
  whiskerRight toTopSimplex.inv (forget TopCat.{u}) ≫
    (Functor.associator _ _ _).hom

private noncomputable instance :
    (toTop.{u} ⋙ forget TopCat.{u}).IsLeftKanExtension
      toTopForgetExtension.{u} := by
  unfold toTopForgetExtension
  infer_instance

private noncomputable def underlyingRealizationComparison :
    (toTop.{u} ⋙ forget TopCat.{u}) ≅ realizationExplicitLan.{u} :=
  leftKanExtensionUnique _ toTopForgetExtension.{u} _
    realizationExplicitLanExtensionIso.{u}.hom

/-- Geometric realization, after forgetting the topology, preserves finite
limits. -/
noncomputable instance preservesFiniteLimits_toTop_forget :
    PreservesFiniteLimits (toTop.{u} ⋙ forget TopCat.{u}) :=
  preservesFiniteLimits_of_natIso underlyingRealizationComparison.{u}.symm

end SSet
