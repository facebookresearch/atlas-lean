/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Convenient.StdSimplexProductCellGluing

@[expose] public section

/-!
# ProductCell overlap regression for `n = m = 1`

Concrete overlap checks of the forward range implications
`shuffleCell_mem_range_imp_cumAB` and `shuffleCell_mem_range_imp_cumBA` and the
reverse range equivalence `shuffleCell_mem_range_iff` on the
`[0, 1, 1]` / `[0, 0, 1]` shuffle applied to the uniform `1 / 3` point of `Δ^2`.
Each check pins its chain-level projections by `decide` and verifies both
cumulative sides against independently computed fiber sums, so a swapped
orientation or fiber would break the numeric equalities.

Nonclaims: no gluing or coverage.
-/

set_option autoImplicit false

noncomputable section

namespace MathlibExtTest.Topology.Convenient.StdSimplexProductCellOverlapTests

/-- First projection `[0, 1, 1] : Fin 3 → Fin 2`. -/
private def projA11 : Fin 3 → Fin 2 := fun i => if i = 0 then 0 else 1

/-- Second projection `[0, 0, 1] : Fin 3 → Fin 2`. -/
private def projB11 : Fin 3 → Fin 2 := fun i => if i = 2 then 1 else 0

/-- Concrete `n = m = 1` shuffle with projections `[0, 1, 1]` / `[0, 0, 1]`. -/
private def S11 : ProdSimplexShuffle 1 1 :=
  { projA := projA11
    projB := projB11
    monoA := by decide
    monoB := by decide
    firstA := by decide
    lastA := by decide
    firstB := by decide
    lastB := by decide
    step := by decide }

/-- Uniform `1 / 3` point of `Δ^2`. -/
private noncomputable def sThird : Convexity.StdSimplex ℝ (Fin 3) where
  weights := Finsupp.equivFunOnFinite.symm (fun _ => (1 / 3 : ℝ))
  nonneg m := by
    have h : (0 : ℝ) ≤ 1 / 3 := by norm_num
    exact h
  total := by
    have h : (∑ _ : Fin 3, (1 / 3 : ℝ)) = 1 := by
      rw [Fin.sum_univ_three]
      norm_num
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)]

/-- Unfolding equation for the uniform-point coordinates. -/
private theorem sThird_val (i : Fin 3) : sThird.weights i = (1 / 3 : ℝ) :=
  rfl

/-- First-factor coordinate at `0`: fiber `{0}`, so the value is `1 / 3`. -/
private theorem fst_zero :
    (shuffleCell S11 sThird).1.weights 0 = 1 / 3 := by
  have h := shuffleCell_fst_fiber S11 sThird 0
  have hfilter : Finset.univ.filter (fun k : Fin 3 => S11.projA k = 0) = {0} := by
    decide
  rw [h, hfilter, Finset.sum_singleton]
  exact sThird_val _

/-- First-factor coordinate at `1`: fiber `{1, 2}`, so the value is `2 / 3`. -/
private theorem fst_one :
    (shuffleCell S11 sThird).1.weights 1 = 2 / 3 := by
  have h := shuffleCell_fst_fiber S11 sThird 1
  have hfilter : Finset.univ.filter (fun k : Fin 3 => S11.projA k = 1) = {1, 2} := by
    decide
  rw [h, hfilter, Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)]
  show (1 / 3 : ℝ) + 1 / 3 = 2 / 3
  norm_num

/-- Second-factor coordinate at `0`: fiber `{0, 1}`, so the value is `2 / 3`. -/
private theorem snd_zero :
    (shuffleCell S11 sThird).2.weights 0 = 2 / 3 := by
  have h := shuffleCell_snd_fiber S11 sThird 0
  have hfilter : Finset.univ.filter (fun k : Fin 3 => S11.projB k = 0) = {0, 1} := by
    decide
  rw [h, hfilter, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)]
  show (1 / 3 : ℝ) + 1 / 3 = 2 / 3
  norm_num

/-- Second-factor coordinate at `1`: fiber `{2}`, so the value is `1 / 3`. -/
private theorem snd_one :
    (shuffleCell S11 sThird).2.weights 1 = 1 / 3 := by
  have h := shuffleCell_snd_fiber S11 sThird 1
  have hfilter : Finset.univ.filter (fun k : Fin 3 => S11.projB k = 1) = {2} := by
    decide
  rw [h, hfilter, Finset.sum_singleton]
  exact sThird_val _

/-- Independent overlap witness: the concrete cell point satisfies both cumulative
families at every chain vertex, proved directly from coordinate values. -/
private theorem overlap_S11 :
    shuffleCumOverlap S11 (shuffleCell S11 sThird).1 (shuffleCell S11 sThird).2 := by
  intro k
  fin_cases k
  · -- `k = 0`: `projA = 0`, `projB = 0`.
    have eA : (S11.projA 0).val = 0 := by decide
    have eB : (S11.projB 0).val = 0 := by decide
    show shuffleCumBefore (shuffleCell S11 sThird).1 (S11.projA 0).val ≤
        shuffleCumThrough (shuffleCell S11 sThird).2 (S11.projB 0).val ∧
      shuffleCumBefore (shuffleCell S11 sThird).2 (S11.projB 0).val ≤
        shuffleCumThrough (shuffleCell S11 sThird).1 (S11.projA 0).val
    rw [eA, eB]
    have hx_before : shuffleCumBefore (shuffleCell S11 sThird).1 0 = 0 := by
      unfold shuffleCumBefore
      have hfilter : Finset.univ.filter (fun i : Fin 2 => i.val < 0) = ∅ := by
        decide
      rw [hfilter, Finset.sum_empty]
    have hy_through : shuffleCumThrough (shuffleCell S11 sThird).2 0 = 2 / 3 := by
      unfold shuffleCumThrough
      have hfilter : Finset.univ.filter (fun i : Fin 2 => i.val ≤ 0) = {0} := by
        decide
      rw [hfilter, Finset.sum_singleton, snd_zero]
    have hy_before : shuffleCumBefore (shuffleCell S11 sThird).2 0 = 0 := by
      unfold shuffleCumBefore
      have hfilter : Finset.univ.filter (fun i : Fin 2 => i.val < 0) = ∅ := by
        decide
      rw [hfilter, Finset.sum_empty]
    have hx_through : shuffleCumThrough (shuffleCell S11 sThird).1 0 = 1 / 3 := by
      unfold shuffleCumThrough
      have hfilter : Finset.univ.filter (fun i : Fin 2 => i.val ≤ 0) = {0} := by
        decide
      rw [hfilter, Finset.sum_singleton, fst_zero]
    rw [hx_before, hy_through, hy_before, hx_through]
    constructor <;> norm_num
  · -- `k = 1`: `projA = 1`, `projB = 0`.
    have eA : (S11.projA 1).val = 1 := by decide
    have eB : (S11.projB 1).val = 0 := by decide
    show shuffleCumBefore (shuffleCell S11 sThird).1 (S11.projA 1).val ≤
        shuffleCumThrough (shuffleCell S11 sThird).2 (S11.projB 1).val ∧
      shuffleCumBefore (shuffleCell S11 sThird).2 (S11.projB 1).val ≤
        shuffleCumThrough (shuffleCell S11 sThird).1 (S11.projA 1).val
    rw [eA, eB]
    have hx_before : shuffleCumBefore (shuffleCell S11 sThird).1 1 = 1 / 3 := by
      unfold shuffleCumBefore
      have hfilter : Finset.univ.filter (fun i : Fin 2 => i.val < 1) = {0} := by
        decide
      rw [hfilter, Finset.sum_singleton, fst_zero]
    have hy_through : shuffleCumThrough (shuffleCell S11 sThird).2 0 = 2 / 3 := by
      unfold shuffleCumThrough
      have hfilter : Finset.univ.filter (fun i : Fin 2 => i.val ≤ 0) = {0} := by
        decide
      rw [hfilter, Finset.sum_singleton, snd_zero]
    have hy_before : shuffleCumBefore (shuffleCell S11 sThird).2 0 = 0 := by
      unfold shuffleCumBefore
      have hfilter : Finset.univ.filter (fun i : Fin 2 => i.val < 0) = ∅ := by
        decide
      rw [hfilter, Finset.sum_empty]
    have hx_through : shuffleCumThrough (shuffleCell S11 sThird).1 1 = 1 := by
      unfold shuffleCumThrough
      have hfilter : Finset.univ.filter (fun i : Fin 2 => i.val ≤ 1) = {0, 1} := by
        decide
      rw [hfilter, Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1), fst_zero, fst_one]
      norm_num
    rw [hx_before, hy_through, hy_before, hx_through]
    constructor <;> norm_num
  · -- `k = 2`: `projA = 1`, `projB = 1`.
    have eA : (S11.projA 2).val = 1 := by decide
    have eB : (S11.projB 2).val = 1 := by decide
    show shuffleCumBefore (shuffleCell S11 sThird).1 (S11.projA 2).val ≤
        shuffleCumThrough (shuffleCell S11 sThird).2 (S11.projB 2).val ∧
      shuffleCumBefore (shuffleCell S11 sThird).2 (S11.projB 2).val ≤
        shuffleCumThrough (shuffleCell S11 sThird).1 (S11.projA 2).val
    rw [eA, eB]
    have hx_before : shuffleCumBefore (shuffleCell S11 sThird).1 1 = 1 / 3 := by
      unfold shuffleCumBefore
      have hfilter : Finset.univ.filter (fun i : Fin 2 => i.val < 1) = {0} := by
        decide
      rw [hfilter, Finset.sum_singleton, fst_zero]
    have hy_through : shuffleCumThrough (shuffleCell S11 sThird).2 1 = 1 := by
      unfold shuffleCumThrough
      have hfilter : Finset.univ.filter (fun i : Fin 2 => i.val ≤ 1) = {0, 1} := by
        decide
      rw [hfilter, Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1), snd_zero, snd_one]
      norm_num
    have hy_before : shuffleCumBefore (shuffleCell S11 sThird).2 1 = 2 / 3 := by
      unfold shuffleCumBefore
      have hfilter : Finset.univ.filter (fun i : Fin 2 => i.val < 1) = {0} := by
        decide
      rw [hfilter, Finset.sum_singleton, snd_zero]
    have hx_through : shuffleCumThrough (shuffleCell S11 sThird).1 1 = 1 := by
      unfold shuffleCumThrough
      have hfilter : Finset.univ.filter (fun i : Fin 2 => i.val ≤ 1) = {0, 1} := by
        decide
      rw [hfilter, Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1), fst_zero, fst_one]
      norm_num
    rw [hx_before, hy_through, hy_before, hx_through]
    constructor <;> norm_num

/-- Overlap `AB` direction at chain level `1`: strict mass `1 / 3` below level
`1` in the first factor against weak mass `2 / 3` through level `0` in the
second factor. -/
example : shuffleCumBefore (shuffleCell S11 sThird).1 1 ≤
    shuffleCumThrough (shuffleCell S11 sThird).2 0 := by
  have hmem : ((shuffleCell S11 sThird).1, (shuffleCell S11 sThird).2) ∈
      Set.range (shuffleCell S11) :=
    ⟨sThird, rfl⟩
  have hAB := shuffleCell_mem_range_imp_cumAB S11 hmem 1
  have eA : (S11.projA 1).val = 1 := by decide
  have eB : (S11.projB 1).val = 0 := by decide
  rw [eA, eB] at hAB
  have lhs : shuffleCumBefore (shuffleCell S11 sThird).1 1 = 1 / 3 := by
    unfold shuffleCumBefore
    have hfilter : Finset.univ.filter (fun i : Fin 2 => i.val < 1) = {0} := by
      decide
    rw [hfilter, Finset.sum_singleton, fst_zero]
  have rhs : shuffleCumThrough (shuffleCell S11 sThird).2 0 = 2 / 3 := by
    unfold shuffleCumThrough
    have hfilter : Finset.univ.filter (fun i : Fin 2 => i.val ≤ 0) = {0} := by
      decide
    rw [hfilter, Finset.sum_singleton, snd_zero]
  rw [lhs, rhs] at hAB ⊢
  exact hAB

/-- Overlap `BA` direction at chain level `2`: strict mass `2 / 3` below level
`1` in the second factor against weak mass `1` through level `1` in the first
factor. -/
example : shuffleCumBefore (shuffleCell S11 sThird).2 1 ≤
    shuffleCumThrough (shuffleCell S11 sThird).1 1 := by
  have hmem : ((shuffleCell S11 sThird).1, (shuffleCell S11 sThird).2) ∈
      Set.range (shuffleCell S11) :=
    ⟨sThird, rfl⟩
  have hBA := shuffleCell_mem_range_imp_cumBA S11 hmem 2
  have eB : (S11.projB 2).val = 1 := by decide
  have eA : (S11.projA 2).val = 1 := by decide
  rw [eB, eA] at hBA
  have lhs : shuffleCumBefore (shuffleCell S11 sThird).2 1 = 2 / 3 := by
    unfold shuffleCumBefore
    have hfilter : Finset.univ.filter (fun i : Fin 2 => i.val < 1) = {0} := by
      decide
    rw [hfilter, Finset.sum_singleton, snd_zero]
  have rhs : shuffleCumThrough (shuffleCell S11 sThird).1 1 = 1 := by
    unfold shuffleCumThrough
    have hfilter : Finset.univ.filter (fun i : Fin 2 => i.val ≤ 1) = {0, 1} := by
      decide
    rw [hfilter, Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1), fst_zero, fst_one]
    norm_num
  rw [lhs, rhs] at hBA ⊢
  exact hBA

/-- Reverse direction: the independently verified overlap places the concrete
cell point back in the range via `shuffleCell_mem_range_iff`. -/
example : ((shuffleCell S11 sThird).1, (shuffleCell S11 sThird).2) ∈
    Set.range (shuffleCell S11) :=
  (shuffleCell_mem_range_iff S11).mpr overlap_S11

end MathlibExtTest.Topology.Convenient.StdSimplexProductCellOverlapTests
