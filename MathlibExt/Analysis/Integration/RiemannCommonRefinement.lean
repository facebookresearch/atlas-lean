/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Integration.RiemannSumRefinement
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Common refinements of tagged partitions

Any two tagged partitions of `[a, b]` have a common tagged refinement:
the partition whose points are the union of both partitions' points, with
tags chosen at the left endpoint of each subinterval. Combined with the
refinement bound in `RiemannSumRefinement.lean`, this gives the book's
Theorem III for two arbitrary tagged partitions.

## Main results

* `TaggedPartition.exists_commonRefinement`: any two tagged partitions of
  `[a, b]` have a common tagged refinement.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Definition (Refinement),
"The Riemann Integral section", and
`v1/Atlas/RealAnalysis/code/Integration/ModulusContinuity.lean`
(`TaggedPartition.exists_commonRefinement`).
-/

@[expose] public section

namespace MathlibExt.Analysis.Integration

variable {a b : ℝ}

/-- **Common refinement of two tagged partitions.** Let $a, b$ be real numbers. For any two
tagged partitions $T_1$ and $T_2$ of $[a, b]$, there is a tagged partition $T''$ of $[a, b]$
that is a tagged refinement of both $T_1$ and $T_2$.

The proof takes for $T''$ the partition whose points are the union of the points of $T_1$
and $T_2$, with each tag at the left endpoint of its subinterval. -/
theorem TaggedPartition.exists_commonRefinement (T₁ T₂ : TaggedPartition a b) :
    ∃ T'' : TaggedPartition a b,
      Nonempty (T₁.IsTaggedRefinement T'') ∧ Nonempty (T₂.IsTaggedRefinement T'') := by
  classical
  let S := (Finset.image T₁.points Finset.univ) ∪ (Finset.image T₂.points Finset.univ)
  have ha_mem : a ∈ S :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, T₁.first⟩)
  have hb_mem : b ∈ S :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Fin.last T₁.n, Finset.mem_univ _, T₁.last⟩)
  have hS_ne : S.Nonempty := ⟨a, ha_mem⟩
  set n'' := S.card - 1
  have hS_card_pos : 0 < S.card := Finset.card_pos.mpr hS_ne
  have hcard : S.card = n'' + 1 := by omega
  let pts := S.orderEmbOfFin hcard
  have hpts_strict : StrictMono pts := (S.orderEmbOfFin hcard).strictMono
  have hmin : S.min' hS_ne = a := by
    apply le_antisymm (Finset.min'_le _ _ ha_mem)
    apply Finset.le_min'; intro x hx
    simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · linarith [T₁.first, T₁.ordered.monotone (Fin.zero_le i)]
    · linarith [T₂.first, T₂.ordered.monotone (Fin.zero_le i)]
  have hmax : S.max' hS_ne = b := by
    apply le_antisymm
    · apply Finset.max'_le; intro x hx
      simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
      rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · linarith [T₁.last, T₁.ordered.monotone (Fin.le_last i)]
      · linarith [T₂.last, T₂.ordered.monotone (Fin.le_last i)]
    · exact Finset.le_max' _ _ hb_mem
  have hpts_first : pts ⟨0, by omega⟩ = a :=
    (Finset.orderEmbOfFin_zero hcard (by omega)).trans hmin
  have hpts_last : pts (Fin.last n'') = b := by
    have h := Finset.orderEmbOfFin_last hcard (by omega : 0 < n'' + 1)
    have heq : (⟨n'' + 1 - 1, (by omega)⟩ : Fin (n'' + 1)) = Fin.last n'' :=
      Fin.ext (by simp [Fin.last])
    rw [heq] at h; exact h.trans hmax
  let T'' : TaggedPartition a b := {
    n := n''
    points := pts
    ordered := hpts_strict
    first := hpts_first
    last := hpts_last
    tags := fun i => pts i.castSucc
    tag_mem := fun i => ⟨le_refl _, (hpts_strict Fin.castSucc_lt_succ).le⟩
  }
  have hT₁_sub : ∀ i, T₁.points i ∈ S :=
    fun i => Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hT₂_sub : ∀ i, T₂.points i ∈ S :=
    fun i => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let φ₁ : Fin (T₁.n + 1) → Fin (n'' + 1) :=
    fun i => (S.orderIsoOfFin hcard).symm ⟨T₁.points i, hT₁_sub i⟩
  let φ₂ : Fin (T₂.n + 1) → Fin (n'' + 1) :=
    fun i => (S.orderIsoOfFin hcard).symm ⟨T₂.points i, hT₂_sub i⟩
  have hφ₁_spec : ∀ i, pts (φ₁ i) = T₁.points i := fun i => by
    have h := Finset.coe_orderIsoOfFin_apply S hcard
      ((S.orderIsoOfFin hcard).symm ⟨T₁.points i, hT₁_sub i⟩)
    rw [OrderIso.apply_symm_apply] at h; exact h.symm
  have hφ₂_spec : ∀ i, pts (φ₂ i) = T₂.points i := fun i => by
    have h := Finset.coe_orderIsoOfFin_apply S hcard
      ((S.orderIsoOfFin hcard).symm ⟨T₂.points i, hT₂_sub i⟩)
    rw [OrderIso.apply_symm_apply] at h; exact h.symm
  have href₁ : T''.toPartition.IsRefinement T₁.toPartition := by
    change Set.range T₁.points ⊆ Set.range pts
    rintro x ⟨i, rfl⟩
    exact ⟨φ₁ i, hφ₁_spec i⟩
  have href₂ : T''.toPartition.IsRefinement T₂.toPartition := by
    change Set.range T₂.points ⊆ Set.range pts
    rintro x ⟨i, rfl⟩
    exact ⟨φ₂ i, hφ₂_spec i⟩
  exact ⟨T'', T₁.nonempty_isTaggedRefinement_of_isRefinement T'' href₁,
    T₂.nonempty_isTaggedRefinement_of_isRefinement T'' href₂⟩

end MathlibExt.Analysis.Integration
