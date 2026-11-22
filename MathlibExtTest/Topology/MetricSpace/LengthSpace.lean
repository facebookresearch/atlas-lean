/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.PiL2
import MathlibExt.Analysis.Convex.LengthSpace

-- L-shape and two-point controls for the induced length metric.

open scoped ENNReal unitInterval

/-- L-shaped subset of the plane. -/
def Lshape : Set (ℝ × ℝ) :=
  {p | (p.2 = 0 ∧ 0 ≤ p.1 ∧ p.1 ≤ 1) ∨ (p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1)}

/-- Right endpoint of the L-shape. -/
def Lx : Lshape := ⟨(1, 0), Or.inl ⟨rfl, zero_le_one, le_refl 1⟩⟩

/-- Top endpoint of the L-shape. -/
def Ly : Lshape := ⟨(0, 1), Or.inr ⟨rfl, zero_le_one, le_refl 1⟩⟩

/-- Restricted distance between L-shape endpoints is 1. -/
theorem lshape_edist : edist Lx Ly = 1 := by
  have hx : (Lx.val : ℝ × ℝ) = (1, 0) := rfl
  have hy : (Ly.val : ℝ × ℝ) = (0, 1) := rfl
  have h10 : edist (1 : ℝ) (0 : ℝ) = 1 := by
    rw [edist_dist, Real.dist_eq]
    have habs : |(1 : ℝ) - (0 : ℝ)| = 1 := by norm_num
    rw [habs, ENNReal.ofReal_one]
  have h01 : edist (0 : ℝ) (1 : ℝ) = 1 := by
    rw [edist_dist, Real.dist_eq]
    have habs : |(0 : ℝ) - (1 : ℝ)| = 1 := by norm_num
    rw [habs, ENNReal.ofReal_one]
  rw [Subtype.edist_eq, hx, hy, Prod.edist_eq, h10, h01, max_self]

/-- Every L-shape path from `Lx` to `Ly` has length at least 2. -/
theorem lshape_lower : 2 ≤ Metric.inducedLengthEdist Lx Ly := by
  apply le_iInf
  intro γ
  have hγ : Continuous (Subtype.val ∘ ⇑γ : ↥I → ℝ × ℝ) :=
    continuous_subtype_val.comp γ.continuous
  have h1 : Continuous (fun t : ↥I => ((γ t).val.1 : ℝ)) :=
    continuous_fst.comp hγ
  have h2 : Continuous (fun t : ↥I => ((γ t).val.2 : ℝ)) :=
    continuous_snd.comp hγ
  have hcont : Continuous (fun t : ↥I => ((γ t).val.1 - (γ t).val.2 : ℝ)) :=
    h1.sub h2
  have hx : (Lx.val : ℝ × ℝ) = (1, 0) := rfl
  have hy : (Ly.val : ℝ × ℝ) = (0, 1) := rfl
  have hsrc : ((γ 0).val : ℝ × ℝ) = (1, 0) := by
    have h : ((γ 0).val : ℝ × ℝ) = Lx.val :=
      congrArg Subtype.val (Path.source γ)
    rw [hx] at h
    exact h
  have htgt : ((γ 1).val : ℝ × ℝ) = (0, 1) := by
    have h : ((γ 1).val : ℝ × ℝ) = Ly.val :=
      congrArg Subtype.val (Path.target γ)
    rw [hy] at h
    exact h
  have hh0 : ((γ 0).val.1 - (γ 0).val.2 : ℝ) = 1 := by
    rw [hsrc]
    norm_num
  have hh1 : ((γ 1).val.1 - (γ 1).val.2 : ℝ) = -1 := by
    rw [htgt]
    norm_num
  have hsub : Set.Icc (-1 : ℝ) (1 : ℝ) ⊆
      Set.range (fun t : ↥I => ((γ t).val.1 - (γ t).val.2 : ℝ)) := by
    have h := intermediate_value_univ (1 : ↥I) (0 : ↥I) hcont
    rw [hh1, hh0] at h
    exact h
  have h0mem : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) (1 : ℝ) := ⟨by norm_num, by norm_num⟩
  obtain ⟨t, ht⟩ := hsub h0mem
  have heq : (γ t).val.1 = (γ t).val.2 := sub_eq_zero.mp ht
  have hmem : (γ t).val ∈ Lshape := (γ t).property
  simp only [Lshape, Set.mem_ofPred_eq] at hmem
  have hcorner : ((γ t).val : ℝ × ℝ) = (0, 0) := by
    cases hmem with
    | inl h =>
      obtain ⟨hc2, _, _⟩ := h
      have hc1 : (γ t).val.1 = 0 := heq.trans hc2
      exact Prod.ext hc1 hc2
    | inr h =>
      obtain ⟨hc1, _, _⟩ := h
      have hc2 : (γ t).val.2 = 0 := heq.symm.trans hc1
      exact Prod.ext hc1 hc2
  have h10 : edist (1 : ℝ) (0 : ℝ) = 1 := by
    rw [edist_dist, Real.dist_eq]
    have habs : |(1 : ℝ) - (0 : ℝ)| = 1 := by norm_num
    rw [habs, ENNReal.ofReal_one]
  have h01 : edist (0 : ℝ) (1 : ℝ) = 1 := by
    rw [edist_dist, Real.dist_eq]
    have habs : |(0 : ℝ) - (1 : ℝ)| = 1 := by norm_num
    rw [habs, ENNReal.ofReal_one]
  have h00 : edist (0 : ℝ) (0 : ℝ) = 0 := by
    rw [edist_dist, Real.dist_eq, sub_self, abs_zero, ENNReal.ofReal_zero]
  have hxγ : edist Lx (γ t) = 1 := by
    rw [Subtype.edist_eq, hx, hcorner, Prod.edist_eq, h10, h00]
    exact max_eq_left bot_le
  have hγy : edist (γ t) Ly = 1 := by
    rw [Subtype.edist_eq, hcorner, hy, Prod.edist_eq, h00, h01]
    exact max_eq_right bot_le
  have e1 : edist (γ t) (γ 0) = 1 := by
    rw [Path.source γ, edist_comm]
    exact hxγ
  have e2 : edist (γ 1) (γ t) = 1 := by
    rw [Path.target γ, edist_comm]
    exact hγy
  let u : ℕ → ↥I := fun i => match i with
    | 0 => 0
    | 1 => t
    | Nat.succ (Nat.succ _) => 1
  have h0t : (0 : ↥I) ≤ t := Subtype.coe_le_coe.mp (unitInterval.nonneg t)
  have ht1 : t ≤ (1 : ↥I) := Subtype.coe_le_coe.mp (unitInterval.le_one t)
  have hmon : Monotone u := monotone_nat_of_le_succ fun n => by
    cases n with
    | zero =>
      show (0 : ↥I) ≤ t
      exact h0t
    | succ n =>
      cases n with
      | zero =>
        show t ≤ (1 : ↥I)
        exact ht1
      | succ n =>
        show (1 : ↥I) ≤ (1 : ↥I)
        exact le_refl 1
  have hmemU : ∀ i : ℕ, u i ∈ (Set.univ : Set ↥I) := fun i => Set.mem_univ _
  have hle := eVariationOn.sum_le (f := ⇑γ) (s := Set.univ) (n := 2) (u := u)
    hmon hmemU
  have hu0 : u 0 = (0 : ↥I) := rfl
  have hu1 : u 1 = t := rfl
  have hu2 : u 2 = (1 : ↥I) := rfl
  have h01n : (0 + 1 : ℕ) = 1 := rfl
  have h12n : (1 + 1 : ℕ) = 2 := rfl
  have h2eq : (2 : ℕ) = 1 + 1 := rfl
  rw [h2eq, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, h01n, h12n, hu0, hu1, hu2, e1, e2,
    one_add_one_eq_two] at hle
  exact hle

/-- L-shape with the restricted metric is not a length space. -/
theorem lshape_not_length : ¬ Metric.IsLengthSpace Lshape := by
  intro h
  have heq := h Lx Ly
  rw [lshape_edist] at heq
  have hle : (2 : ℝ≥0∞) ≤ 1 := heq ▸ lshape_lower
  have h12 : (1 : ℝ≥0∞) < 2 := by norm_num
  exact (not_le_of_gt h12) hle

/-- Two-point subset of the reals. -/
def TwoPoint : Set ℝ := {0, 1}

/-- Lower point of the two-point set. -/
def T0 : TwoPoint := ⟨0, Set.mem_insert_iff.mpr (Or.inl rfl)⟩

/-- Upper point of the two-point set. -/
def T1 : TwoPoint := ⟨1, Set.mem_insert_iff.mpr (Or.inr rfl)⟩

/-- Restricted distance in the two-point set is 1. -/
theorem two_edist : edist T0 T1 = 1 := by
  have hx0 : (T0.val : ℝ) = 0 := rfl
  have hx1 : (T1.val : ℝ) = 1 := rfl
  have h01 : edist (0 : ℝ) (1 : ℝ) = 1 := by
    rw [edist_dist, Real.dist_eq]
    have habs : |(0 : ℝ) - (1 : ℝ)| = 1 := by norm_num
    rw [habs, ENNReal.ofReal_one]
  rw [Subtype.edist_eq, hx0, hx1, h01]

/-- There is no path between the two points. -/
theorem two_empty : IsEmpty (Path T0 T1) := by
  constructor
  intro γ
  have hγcont : Continuous ⇑γ := γ.continuous
  have hf : Continuous (fun t : ↥I => ((γ t).val : ℝ)) :=
    continuous_subtype_val.comp hγcont
  have hx0 : (T0.val : ℝ) = 0 := rfl
  have hx1 : (T1.val : ℝ) = 1 := rfl
  have hf0 : ((γ 0).val : ℝ) = 0 := by
    have h : ((γ 0).val : ℝ) = T0.val :=
      congrArg Subtype.val (Path.source γ)
    rw [hx0] at h
    exact h
  have hf1 : ((γ 1).val : ℝ) = 1 := by
    have h : ((γ 1).val : ℝ) = T1.val :=
      congrArg Subtype.val (Path.target γ)
    rw [hx1] at h
    exact h
  have hsub : Set.Icc (0 : ℝ) (1 : ℝ) ⊆
      Set.range (fun t : ↥I => ((γ t).val : ℝ)) := by
    have h := intermediate_value_univ (0 : ↥I) (1 : ↥I) hf
    rw [hf0, hf1] at h
    exact h
  have h12 : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) (1 : ℝ) := ⟨by norm_num, by norm_num⟩
  obtain ⟨t, ht⟩ := hsub h12
  have hmem : ((γ t).val : ℝ) ∈ TwoPoint := (γ t).property
  have hmem2 : ((γ t).val : ℝ) ∈ ({0, 1} : Set ℝ) := hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem2
  have ht2 : ((γ t).val : ℝ) = 1 / 2 := ht
  cases hmem2 with
  | inl h =>
    rw [h] at ht2
    norm_num at ht2
  | inr h =>
    rw [h] at ht2
    norm_num at ht2

/-- Induced length distance on the two-point set is infinite. -/
theorem two_length : Metric.inducedLengthEdist T0 T1 = ⊤ :=
  Metric.inducedLengthEdist_eq_top_of_isEmpty two_empty

/-- The real line is a length space. -/
theorem real_length : Metric.IsLengthSpace ℝ :=
  isLengthSpace_of_normedSpace

/-- The Euclidean plane is a length space. -/
theorem euclid_length : Metric.IsLengthSpace (EuclideanSpace ℝ (Fin 2)) :=
  isLengthSpace_of_normedSpace

/-- The closed half-plane is a length space. -/
theorem halfplane_length :
    Metric.IsLengthSpace {v : EuclideanSpace ℝ (Fin 2) | 0 ≤ v 1} := by
  have hconv : Convex ℝ {v : EuclideanSpace ℝ (Fin 2) | 0 ≤ v 1} := by
    intro x hx y hy a b ha hb _
    have hx' : (0 : ℝ) ≤ x 1 := hx
    have hy' : (0 : ℝ) ≤ y 1 := hy
    have happly : ((a • x + b • y) 1 : ℝ) = a * x 1 + b * y 1 := rfl
    show (0 : ℝ) ≤ (a • x + b • y) 1
    rw [happly]
    exact add_nonneg (mul_nonneg ha hx') (mul_nonneg hb hy')
  exact hconv.isLengthSpace
