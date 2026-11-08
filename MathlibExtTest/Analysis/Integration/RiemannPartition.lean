/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Integration.RiemannCommonRefinement
import Mathlib.Tactic

namespace MetaMathlibExt

open MathlibExt.Analysis.Integration

/-- The endpoints of any partition satisfy `a ≤ b`. -/
example {a b : ℝ} (P : Partition a b) : a ≤ b :=
  P.a_le_b

/-- A partition of `[a, b]` with `a < b` has positive mesh. -/
example {a b : ℝ} (hab : a < b) (P : Partition a b) : 0 < P.mesh :=
  P.mesh_pos_of_lt hab

/-- The subinterval lengths of any partition telescope to `b - a`. -/
example {a b : ℝ} (P : Partition a b) :
    ∑ i : Fin P.n, (P.points i.succ - P.points i.castSucc) = b - a :=
  P.sum_sub_eq

/-- Every tag of a tagged partition lies in `[a, b]`. -/
example {a b : ℝ} (T : TaggedPartition a b) (i : Fin T.n) :
    T.tags i ∈ Set.Icc a b :=
  T.tag_mem_Icc i

/-- The Riemann sum of a constant function is the constant times `b - a`. -/
example {a b : ℝ} (c : ℝ) (T : TaggedPartition a b) :
    riemannSum (fun _ => c) T = c * (b - a) :=
  riemannSum_const c T

/-- The Riemann sum over a trivial tagged partition is `0`. -/
example {a b : ℝ} (f : ℝ → ℝ) (T : TaggedPartition a b) (h : T.n = 0) :
    riemannSum f T = 0 :=
  riemannSum_eq_zero_of_n_eq_zero f T h

/-- Every tagged partition is a tagged refinement of itself, with `assign`
the identity. -/
example {a b : ℝ} (T : TaggedPartition a b) : T.IsTaggedRefinement T where
  assign := id
  contained_left := fun _ => le_rfl
  contained_right := fun _ => le_rfl
  telescope := fun k => by
    -- Only `k` itself survives the filter `id j = k`.
    have : Finset.univ.filter (fun j : Fin T.n => id j = k) = {k} := by
      ext j
      simp [Finset.mem_filter, Finset.mem_singleton]
    rw [this]
    simp

/-- For a constant function, the refinement bound holds with oscillation
`0`: the two Riemann sums are equal. -/
example {a b : ℝ} (c : ℝ) (T T' : TaggedPartition a b)
    (href : T.IsTaggedRefinement T') :
    |riemannSum (fun _ => c) T - riemannSum (fun _ => c) T'| ≤ (0 : ℝ) * (b - a) := by
  apply riemannSum_sub_le_of_isTaggedRefinement _ T T' _ href
  intro x _ y _ _
  simp

/-- Any two tagged partitions have a common tagged refinement. -/
example {a b : ℝ} (T₁ T₂ : TaggedPartition a b) :
    ∃ T'' : TaggedPartition a b,
      Nonempty (T₁.IsTaggedRefinement T'') ∧
        Nonempty (T₂.IsTaggedRefinement T'') :=
  TaggedPartition.exists_commonRefinement T₁ T₂

/-- For a constant function, the common-refinement bound holds with
oscillations `0`: the two Riemann sums are equal. -/
example {a b : ℝ} (c : ℝ) (T₁ T₂ : TaggedPartition a b) :
    |riemannSum (fun _ => c) T₁ - riemannSum (fun _ => c) T₂| ≤
      ((0 : ℝ) + 0) * (b - a) := by
  obtain ⟨T'', ⟨href₁⟩, ⟨href₂⟩⟩ := TaggedPartition.exists_commonRefinement T₁ T₂
  apply riemannSum_sub_le_of_commonRefinement _ T₁ T₂ _ _ T'' href₁ href₂ <;>
    intro x _ y _ _ <;> simp

/-- The one-subinterval tagged partition of `[0, 1]` with tag `1 / 2`:
the Riemann sum of the identity function is `1 / 2`. -/
example : ∃ T : TaggedPartition (0 : ℝ) 1,
    T.n = 1 ∧ riemannSum (fun x => x) T = 1 / 2 := by
  refine ⟨{
    n := 1
    points := fun i => (i : ℝ)
    ordered := by
      intro a b hab
      dsimp only
      exact_mod_cast hab
    first := by simp
    last := by simp
    tags := fun _ => 1 / 2
    tag_mem := by
      intro i
      fin_cases i; simp; norm_num
  }, rfl, ?_⟩
  simp [riemannSum]

/-- The two-cell partition of `[0, 1]` with left endpoint tags. -/
private noncomputable def twoCellLeft : TaggedPartition (0 : ℝ) 1 where
  n := 2
  points := fun i => (i : ℝ) / 2
  ordered := by
    intro i j hij
    apply div_lt_div_of_pos_right ?_ (by norm_num)
    exact_mod_cast hij
  first := by norm_num
  last := by norm_num
  tags := fun i => (i : ℝ) / 2
  tag_mem := by
    intro i
    fin_cases i <;> norm_num

/-- The four-cell partition of `[0, 1]` with midpoint tags. -/
private noncomputable def fourCellMidpoint : TaggedPartition (0 : ℝ) 1 where
  n := 4
  points := fun i => (i : ℝ) / 4
  ordered := by
    intro i j hij
    apply div_lt_div_of_pos_right ?_ (by norm_num)
    exact_mod_cast hij
  first := by norm_num
  last := by norm_num
  tags := fun i => ((i : ℝ) + 1 / 2) / 4
  tag_mem := by
    intro i
    fin_cases i <;> norm_num

private lemma twoCellLeft_sum : riemannSum (fun x => x) twoCellLeft = 1 / 4 := by
  unfold riemannSum twoCellLeft
  norm_num [Fin.sum_univ_succ]

private lemma fourCellMidpoint_sum : riemannSum (fun x => x) fourCellMidpoint = 1 / 2 := by
  unfold riemannSum fourCellMidpoint
  norm_num [Fin.sum_univ_succ]

private lemma twoCellLeft_mesh : twoCellLeft.toPartition.mesh = 1 / 2 := by
  unfold Partition.mesh twoCellLeft
  norm_num
  have hlen (i : Fin 2) : ((i : ℝ) + 1) / 2 - (i : ℝ) / 2 = 1 / 2 := by
    ring
  simp only [hlen, Finset.sup'_const]

private lemma fourCellMidpoint_mesh : fourCellMidpoint.toPartition.mesh = 1 / 4 := by
  unfold Partition.mesh fourCellMidpoint
  norm_num
  have hlen (i : Fin 4) : ((i : ℝ) + 1) / 4 - (i : ℝ) / 4 = 1 / 4 := by
    ring
  simp only [hlen, Finset.sup'_const]

private lemma fourCellMidpoint_refines_twoCellLeft :
    fourCellMidpoint.toPartition.IsRefinement twoCellLeft.toPartition := by
  unfold Partition.IsRefinement Partition.pointSet twoCellLeft fourCellMidpoint
  rintro x ⟨i, rfl⟩
  fin_cases i
  · refine ⟨0, ?_⟩
    norm_num
  · refine ⟨2, ?_⟩
    norm_num
  · refine ⟨4, ?_⟩
    norm_num

/-- The canonical refinement estimate applies to a nonconstant function,
two coarse cells and four fine cells, with different tag choices. -/
example : |riemannSum (fun x => x) twoCellLeft -
    riemannSum (fun x => x) fourCellMidpoint| ≤ (1 / 2 : ℝ) * (1 - 0) := by
  apply riemannSum_sub_le_of_isRefinement _ twoCellLeft fourCellMidpoint _
    fourCellMidpoint_refines_twoCellLeft
  intro x _ y _ hxy
  simpa only [twoCellLeft_mesh] using hxy

/-- The identity-function sums differ by `1 / 4`, so the bound exercises a
nonzero sum difference. -/
example : |riemannSum (fun x => x) twoCellLeft -
    riemannSum (fun x => x) fourCellMidpoint| = (1 / 4 : ℝ) := by
  rw [twoCellLeft_sum, fourCellMidpoint_sum]
  norm_num

/-- The union-based common-refinement constructor and the existing bound
also apply to the two nonconstant sums. -/
example : |riemannSum (fun x => x) twoCellLeft -
    riemannSum (fun x => x) fourCellMidpoint| ≤
    ((1 / 2 : ℝ) + 1 / 4) * (1 - 0) := by
  obtain ⟨T'', ⟨href₁⟩, ⟨href₂⟩⟩ :=
    TaggedPartition.exists_commonRefinement twoCellLeft fourCellMidpoint
  apply riemannSum_sub_le_of_commonRefinement _ twoCellLeft fourCellMidpoint _ _
    T'' href₁ href₂
  · intro x _ y _ hxy
    simpa only [twoCellLeft_mesh] using hxy
  · intro x _ y _ hxy
    simpa only [fourCellMidpoint_mesh] using hxy

private def zeroCell (c : ℝ) : TaggedPartition c c where
  n := 0
  points := fun _ => c
  ordered := by
    intro i j hij
    have hval : i.val < j.val := hij
    have hi := i.isLt
    have hj := j.isLt
    omega
  first := rfl
  last := rfl
  tags := Fin.elim0
  tag_mem := fun i => Fin.elim0 i

/-- Canonical refinement data also exist for the zero-cell partition. -/
example (c : ℝ) : Nonempty ((zeroCell c).IsTaggedRefinement (zeroCell c)) := by
  apply TaggedPartition.nonempty_isTaggedRefinement_of_isRefinement (zeroCell c) (zeroCell c)
  intro x hx
  exact hx

end MetaMathlibExt
