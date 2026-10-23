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

* `telescope_sum_of_embedding`: the telescoping identity used to verify
  the refinement condition for a common refinement built from an
  embedding of index sets.
* `TaggedPartition.exists_commonRefinement`: any two tagged partitions of
  `[a, b]` have a common tagged refinement.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Definition (Refinement),
"The Riemann Integral section", and
`v1/Atlas/RealAnalysis/code/Integration/ModulusContinuity.lean`
(`telescope_sum_of_embedding`, `TaggedPartition.exists_commonRefinement`).
-/

@[expose] public section

namespace MathlibExt.Analysis.Integration

variable {a b : ℝ}

/-- Telescoping identity: given a strictly monotone embedding `φ` of a coarse
index set into a fine index set, the lengths of the fine subintervals whose
indices are assigned to a coarse index `k` sum to the length of the `k`-th
coarse subinterval. -/
lemma telescope_sum_of_embedding {n'' m : ℕ} (pts : Fin (n'' + 1) → ℝ)
    (φ : Fin (m + 1) → Fin (n'' + 1)) (hφ_strict : StrictMono φ)
    (assign : Fin n'' → Fin m)
    (hassign_spec : ∀ j : Fin n'', (φ (assign j).castSucc).val ≤ j.val ∧
      j.val < (φ (assign j).succ).val)
    (k : Fin m) :
    ∑ j ∈ Finset.univ.filter (fun j => assign j = k),
      (pts j.succ - pts j.castSucc) = pts (φ k.succ) - pts (φ k.castSucc) := by
  have hfilter_eq : Finset.univ.filter (fun j : Fin n'' => assign j = k) =
      Finset.univ.filter (fun j : Fin n'' => (φ k.castSucc).val ≤ j.val ∧
        j.val < (φ k.succ).val) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; have := hassign_spec j; rw [h] at this; exact this
    · intro ⟨hleft, hright⟩
      by_contra hne
      have hspec := hassign_spec j
      rcases Fin.lt_or_lt_of_ne hne with h | h
      · have _h1 := hφ_strict.monotone (Fin.succ_le_castSucc_iff.mpr h)
        have := hspec.2; omega
      · have _h1 := hφ_strict.monotone (Fin.succ_le_castSucc_iff.mpr h)
        have := hspec.1; omega
  rw [hfilter_eq]
  set a' := (φ k.castSucc).val; set b' := (φ k.succ).val
  have hab' : a' ≤ b' := (hφ_strict Fin.castSucc_lt_succ).le
  have hb'_lt : b' < n'' + 1 := (φ k.succ).isLt
  let g : ℕ → ℝ := fun i => if h : i < n'' + 1 then pts ⟨i, h⟩ else 0
  suffices hsuff : ∀ j ∈ Finset.univ.filter (fun j : Fin n'' => a' ≤ j.val ∧ j.val < b'),
      pts j.succ - pts j.castSucc = g (j.val + 1) - g j.val by
    rw [Finset.sum_congr rfl hsuff]
    have hbij : ∑ j ∈ Finset.univ.filter (fun j : Fin n'' => a' ≤ j.val ∧ j.val < b'),
        (g (↑j + 1) - g ↑j) = ∑ i ∈ Finset.Ico a' b', (g (i + 1) - g i) :=
      Finset.sum_nbij (fun j => j.val)
        (fun j hj => Finset.mem_Ico.mpr (Finset.mem_filter.mp hj).2)
        (fun _ _ _ _ h => Fin.ext h)
        (fun i hi => ⟨⟨i, by have := (Finset.mem_Ico.mp hi).2; omega⟩, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Finset.mem_Ico.mp hi⟩, rfl⟩)
        (fun _ _ => rfl)
    rw [hbij, Finset.sum_Ico_sub g hab']
    simp only [g, hb'_lt, Nat.lt_of_le_of_lt hab' hb'_lt, dite_eq_left]
    congr 1
  intro j hj
  have hj' := (Finset.mem_filter.mp hj).2
  simp only [g, show j.val < n'' + 1 from by omega,
    show j.val + 1 < n'' + 1 from by omega, dite_eq_left]
  congr 1

/-- Any two tagged partitions of `[a, b]` have a common tagged refinement:
the partition whose points are the union of both partitions' points. -/
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
  have hφ₁_strict : StrictMono φ₁ := fun i j hij =>
    (S.orderIsoOfFin hcard).symm.strictMono (Subtype.mk_lt_mk.mpr (T₁.ordered hij))
  have hφ₂_strict : StrictMono φ₂ := fun i j hij =>
    (S.orderIsoOfFin hcard).symm.strictMono (Subtype.mk_lt_mk.mpr (T₂.ordered hij))
  have hφ₁_spec : ∀ i, pts (φ₁ i) = T₁.points i := fun i => by
    have h := Finset.coe_orderIsoOfFin_apply S hcard
      ((S.orderIsoOfFin hcard).symm ⟨T₁.points i, hT₁_sub i⟩)
    rw [OrderIso.apply_symm_apply] at h; exact h.symm
  have hφ₂_spec : ∀ i, pts (φ₂ i) = T₂.points i := fun i => by
    have h := Finset.coe_orderIsoOfFin_apply S hcard
      ((S.orderIsoOfFin hcard).symm ⟨T₂.points i, hT₂_sub i⟩)
    rw [OrderIso.apply_symm_apply] at h; exact h.symm
  have hφ₁_zero : (φ₁ 0).val = 0 := by
    have h1 : pts (φ₁ 0) = a := (hφ₁_spec 0).trans T₁.first
    have h3 := (S.orderEmbOfFin hcard).injective (h1.trans hpts_first.symm)
    exact congr_arg Fin.val h3
  have hφ₂_zero : (φ₂ 0).val = 0 := by
    have h1 : pts (φ₂ 0) = a := (hφ₂_spec 0).trans T₂.first
    have h3 := (S.orderEmbOfFin hcard).injective (h1.trans hpts_first.symm)
    exact congr_arg Fin.val h3
  have hφ₁_last : (φ₁ (Fin.last T₁.n)).val = n'' := by
    have h1 : pts (φ₁ (Fin.last T₁.n)) = b := (hφ₁_spec _).trans T₁.last
    have h3 := (S.orderEmbOfFin hcard).injective (h1.trans hpts_last.symm)
    have : (Fin.last n'').val = n'' := rfl
    linarith [congr_arg Fin.val h3, this]
  have hφ₂_last : (φ₂ (Fin.last T₂.n)).val = n'' := by
    have h1 : pts (φ₂ (Fin.last T₂.n)) = b := (hφ₂_spec _).trans T₂.last
    have h3 := (S.orderEmbOfFin hcard).injective (h1.trans hpts_last.symm)
    have : (Fin.last n'').val = n'' := rfl
    linarith [congr_arg Fin.val h3, this]
  have mk_assign₁ : ∀ j : Fin n'', ∃ k : Fin T₁.n,
      (φ₁ k.castSucc).val ≤ j.val ∧ j.val < (φ₁ k.succ).val := by
    intro j
    let good := Finset.univ.filter (fun i : Fin (T₁.n + 1) => (φ₁ i).val ≤ j.val)
    have hgood_ne : good.Nonempty :=
      ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
    have hlast_not : Fin.last T₁.n ∉ good := by
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
      have := hφ₁_last; have := j.isLt; omega
    set k₀ := good.max' hgood_ne
    have hk₀_mem := Finset.max'_mem good hgood_ne
    have hk₀_le : (φ₁ k₀).val ≤ j.val := (Finset.mem_filter.mp hk₀_mem).2
    have hk₀_lt_last : k₀ < Fin.last T₁.n := by
      rcases lt_or_eq_of_le (Fin.le_last k₀) with h | h
      · exact h
      · exact absurd (h ▸ hk₀_mem) hlast_not
    have hk₀_val_lt : k₀.val < T₁.n := by
      simp [Fin.lt_def, Fin.last] at hk₀_lt_last; exact hk₀_lt_last
    refine ⟨⟨k₀.val, hk₀_val_lt⟩, ?_, ?_⟩
    · have : (⟨k₀.val, hk₀_val_lt⟩ : Fin T₁.n).castSucc = k₀ := Fin.ext rfl
      rw [this]; exact hk₀_le
    · have hsucc_eq : (⟨k₀.val, hk₀_val_lt⟩ : Fin T₁.n).succ =
          ⟨k₀.val + 1, by omega⟩ :=
        Fin.ext (by simp [Fin.succ])
      rw [hsucc_eq]
      have hsucc_not : (⟨k₀.val + 1, (by omega : k₀.val + 1 < T₁.n + 1)⟩ :
          Fin (T₁.n + 1)) ∉ good := by
        intro hmem
        have hle := Finset.le_max' good _ hmem
        simp [Fin.le_def] at hle; omega
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hsucc_not
      exact hsucc_not
  have mk_assign₂ : ∀ j : Fin n'', ∃ k : Fin T₂.n,
      (φ₂ k.castSucc).val ≤ j.val ∧ j.val < (φ₂ k.succ).val := by
    intro j
    let good := Finset.univ.filter (fun i : Fin (T₂.n + 1) => (φ₂ i).val ≤ j.val)
    have hgood_ne : good.Nonempty :=
      ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
    have hlast_not : Fin.last T₂.n ∉ good := by
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
      have := hφ₂_last; have := j.isLt; omega
    set k₀ := good.max' hgood_ne
    have hk₀_mem := Finset.max'_mem good hgood_ne
    have hk₀_le : (φ₂ k₀).val ≤ j.val := (Finset.mem_filter.mp hk₀_mem).2
    have hk₀_lt_last : k₀ < Fin.last T₂.n := by
      rcases lt_or_eq_of_le (Fin.le_last k₀) with h | h
      · exact h
      · exact absurd (h ▸ hk₀_mem) hlast_not
    have hk₀_val_lt : k₀.val < T₂.n := by
      simp [Fin.lt_def, Fin.last] at hk₀_lt_last; exact hk₀_lt_last
    refine ⟨⟨k₀.val, hk₀_val_lt⟩, ?_, ?_⟩
    · have : (⟨k₀.val, hk₀_val_lt⟩ : Fin T₂.n).castSucc = k₀ := Fin.ext rfl
      rw [this]; exact hk₀_le
    · have hsucc_eq : (⟨k₀.val, hk₀_val_lt⟩ : Fin T₂.n).succ =
          ⟨k₀.val + 1, by omega⟩ :=
        Fin.ext (by simp [Fin.succ])
      rw [hsucc_eq]
      have hsucc_not : (⟨k₀.val + 1, (by omega : k₀.val + 1 < T₂.n + 1)⟩ :
          Fin (T₂.n + 1)) ∉ good := by
        intro hmem
        have hle := Finset.le_max' good _ hmem
        simp [Fin.le_def] at hle; omega
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hsucc_not
      exact hsucc_not
  let assign₁ : Fin n'' → Fin T₁.n := fun j => (mk_assign₁ j).choose
  let assign₂ : Fin n'' → Fin T₂.n := fun j => (mk_assign₂ j).choose
  have hassign₁_spec : ∀ j, (φ₁ (assign₁ j).castSucc).val ≤ j.val ∧
      j.val < (φ₁ (assign₁ j).succ).val := fun j => (mk_assign₁ j).choose_spec
  have hassign₂_spec : ∀ j, (φ₂ (assign₂ j).castSucc).val ≤ j.val ∧
      j.val < (φ₂ (assign₂ j).succ).val := fun j => (mk_assign₂ j).choose_spec
  refine ⟨T'', ⟨?_⟩, ⟨?_⟩⟩
  · exact {
      assign := assign₁
      contained_left := fun j => by
        rw [← hφ₁_spec (assign₁ j).castSucc]
        exact hpts_strict.monotone (hassign₁_spec j).1
      contained_right := fun j => by
        rw [← hφ₁_spec (assign₁ j).succ]
        exact hpts_strict.monotone (Nat.lt_iff_add_one_le.mp (hassign₁_spec j).2)
      telescope := fun k => by
        show ∑ j ∈ Finset.univ.filter (fun j => assign₁ j = k),
          (pts j.succ - pts j.castSucc) = T₁.points k.succ - T₁.points k.castSucc
        rw [← hφ₁_spec k.succ, ← hφ₁_spec k.castSucc]
        exact telescope_sum_of_embedding pts φ₁ hφ₁_strict assign₁ hassign₁_spec k
    }
  · exact {
      assign := assign₂
      contained_left := fun j => by
        rw [← hφ₂_spec (assign₂ j).castSucc]
        exact hpts_strict.monotone (hassign₂_spec j).1
      contained_right := fun j => by
        rw [← hφ₂_spec (assign₂ j).succ]
        exact hpts_strict.monotone (Nat.lt_iff_add_one_le.mp (hassign₂_spec j).2)
      telescope := fun k => by
        show ∑ j ∈ Finset.univ.filter (fun j => assign₂ j = k),
          (pts j.succ - pts j.castSucc) = T₂.points k.succ - T₂.points k.castSucc
        rw [← hφ₂_spec k.succ, ← hφ₂_spec k.castSucc]
        exact telescope_sum_of_embedding pts φ₂ hφ₂_strict assign₂ hassign₂_spec k
    }

end MathlibExt.Analysis.Integration
