/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.ConfigurationSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section

/-!
# Local Euclidean path shortening

For a feasible polyline in the Euclidean plane with a non-weakly-between bend
at an interior point of the feasible set, a strictly shorter feasible polyline
with the same endpoints exists, obtained by shortcutting the bend with nearby
points on the two incident segments. Consequently, a length-minimal feasible
polyline is weakly between at every interior bend.

Context: shortest-path roadmaps (LaValle, Planning Algorithms, Chapter 6).
The local statements here are precise Euclidean helpers.
-/


namespace Cslib.Planning.MotionPlanning.PathShortening

open Metric

/-- Total Euclidean length of a finite polyline (sum of consecutive distances). -/
noncomputable def polyLen : List plane → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => dist a b + polyLen (b :: rest)

/-- Every vertex lies in `F`, and every closed segment between consecutive vertices lies in `F`; the empty polyline is vacuously feasible. -/
def Feasible (F : Set plane) : List plane → Prop
  | [] => True
  | [x] => x ∈ F
  | a :: b :: rest => segment ℝ a b ⊆ F ∧ Feasible F (b :: rest)

@[simp]
theorem polyLen_nil : polyLen [] = 0 :=
  rfl

@[simp]
theorem polyLen_singleton (x : plane) : polyLen [x] = 0 :=
  rfl

theorem polyLen_cons_cons (a b : plane) (rest : List plane) :
    polyLen (a :: b :: rest) = dist a b + polyLen (b :: rest) :=
  rfl

@[simp]
theorem feasible_nil (F : Set plane) : Feasible F [] :=
  trivial

@[simp]
theorem feasible_singleton (F : Set plane) (x : plane) : x ∈ F → Feasible F [x] :=
  fun h => h

theorem feasible_cons_cons (F : Set plane) (a b : plane) (rest : List plane) :
    Feasible F (a :: b :: rest) ↔ segment ℝ a b ⊆ F ∧ Feasible F (b :: rest) :=
  Iff.rfl

theorem feasible_head_mem (F : Set plane) (a : plane) (rest : List plane)
    (h : Feasible F (a :: rest)) : a ∈ F := by
  cases rest with
  | nil => exact h
  | cons b rest' =>
    rw [feasible_cons_cons] at h
    exact h.1 (left_mem_segment ℝ a b)

theorem feasible_append_cons (F : Set plane) (a : plane) (rest : List plane) :
    ∀ l₁ : List plane,
      Feasible F (l₁ ++ a :: rest) ↔ Feasible F (l₁ ++ [a]) ∧ Feasible F (a :: rest)
  | [] => by
    simp only [List.nil_append]
    exact ⟨fun h => ⟨feasible_head_mem F a rest h, h⟩, And.right⟩
  | [y] => by
    simp only [List.cons_append, List.nil_append, feasible_cons_cons]
    exact ⟨fun h => ⟨⟨h.1, feasible_head_mem F a rest h.2⟩, h.2⟩,
      fun h => ⟨h.1.1, h.2⟩⟩
  | y :: z :: l₁ => by
    have ih := feasible_append_cons F a rest (z :: l₁)
    simp only [List.cons_append, feasible_cons_cons] at ih ⊢
    rw [ih]
    tauto

theorem polyLen_append_cons (a : plane) (rest : List plane) :
    ∀ l₁ : List plane,
      polyLen (l₁ ++ a :: rest) = polyLen (l₁ ++ [a]) + polyLen (a :: rest)
  | [] => by simp
  | [y] => by simp [polyLen_cons_cons]
  | y :: z :: l₁ => by
    have ih := polyLen_append_cons a rest (z :: l₁)
    simp only [List.cons_append, polyLen_cons_cons] at ih ⊢
    rw [ih]
    ring

/-- (L-core) Shared shortening core: shortcut a non-between bend given a
locally convex feasible neighborhood. Both `local_shortening` and
`local_shortening_of_locally_convex` derive from this lemma. -/
theorem local_shortening_core (F : Set plane) (l₁ l₂ : List plane) (a b c : plane)
    (hfeas : Feasible F (l₁ ++ [a, b, c] ++ l₂))
    (hconv : ∃ U ∈ nhds b, Convex ℝ (U ∩ F))
    (hbc : ¬ Wbtw ℝ a b c) (ε : ℝ) (hε : 0 < ε) :
    ∃ a' c' : plane, a' ∈ segment ℝ a b ∧ c' ∈ segment ℝ b c ∧
      dist a' b < ε ∧ dist c' b < ε ∧
      Feasible F (l₁ ++ [a, a', c', c] ++ l₂) ∧
      polyLen (l₁ ++ [a, a', c', c] ++ l₂) < polyLen (l₁ ++ [a, b, c] ++ l₂) := by
  have hab_ne : a ≠ b := fun h' => hbc (by subst h'; exact wbtw_self_left ℝ _ _)
  have hbc_ne : b ≠ c := fun h' => hbc (by subst h'; exact wbtw_self_right ℝ _ _)
  have hD1 : 0 < dist a b := dist_pos.mpr hab_ne
  have hD2 : 0 < dist b c := dist_pos.mpr hbc_ne
  obtain ⟨U, hU_mem, hU_conv⟩ := hconv
  rw [Metric.mem_nhds_iff] at hU_mem
  obtain ⟨δ, hδpos, hδsub⟩ := hU_mem
  set M : ℝ := max (dist a b) (dist b c) with hM_def
  have hM1 : dist a b ≤ M := le_max_left _ _
  have hM2 : dist b c ≤ M := le_max_right _ _
  have hMpos : 0 < M := lt_max_iff.mpr (Or.inl hD1)
  have hMne : M ≠ 0 := ne_of_gt hMpos
  set u : ℝ := min (min (1 / 2) (ε / (2 * M))) (δ / (2 * M)) with hu_def
  have hu_pos : 0 < u := by
    rw [hu_def]
    exact lt_min (lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) hMpos)))
      (div_pos hδpos (mul_pos (by norm_num) hMpos))
  have hu_half : u ≤ 1 / 2 := by
    rw [hu_def]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hu_eps : u ≤ ε / (2 * M) := by
    rw [hu_def]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hu_small : u ≤ δ / (2 * M) := by
    rw [hu_def]
    exact min_le_right _ _
  have hu_lt1 : u < 1 := lt_of_le_of_lt hu_half (by norm_num)
  have hu1u : 0 ≤ 1 - u := sub_nonneg.mpr hu_lt1.le
  have huM : u * M < δ := by
    have h1 : u * M ≤ (δ / (2 * M)) * M :=
      mul_le_mul_of_nonneg_right hu_small hMpos.le
    have h2 : (δ / (2 * M)) * M = δ / 2 := by
      field_simp
    rw [h2] at h1
    linarith
  have huD1 : u * dist a b < δ :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hM1 hu_pos.le) huM
  have huD2 : u * dist b c < δ :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hM2 hu_pos.le) huM
  have huM_eps : u * M < ε := by
    have h1 : u * M ≤ (ε / (2 * M)) * M :=
      mul_le_mul_of_nonneg_right hu_eps hMpos.le
    have h2 : (ε / (2 * M)) * M = ε / 2 := by
      field_simp
    rw [h2] at h1
    linarith
  have huD1_eps : u * dist a b < ε :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hM1 hu_pos.le) huM_eps
  have huD2_eps : u * dist b c < ε :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hM2 hu_pos.le) huM_eps
  set a' : plane := u • a + (1 - u) • b with ha'_def
  set c' : plane := (1 - u) • b + u • c with hc'_def
  have ha'_mem : a' ∈ segment ℝ a b :=
    ⟨u, 1 - u, hu_pos.le, hu1u, by ring, ha'_def.symm⟩
  have hc'_mem : c' ∈ segment ℝ b c :=
    ⟨1 - u, u, hu1u, hu_pos.le, by ring, hc'_def.symm⟩
  have hsub_ab : a' - b = u • (a - b) := by
    simp only [ha'_def]
    module
  have hdist_a'b : dist a' b = u * dist a b := by
    rw [dist_eq_norm, hsub_ab, norm_smul, Real.norm_of_nonneg hu_pos.le, dist_eq_norm]
  have hsub_cb : c' - b = u • (c - b) := by
    simp only [hc'_def]
    module
  have hdist_c'b : dist c' b = u * dist c b := by
    rw [dist_eq_norm, hsub_cb, norm_smul, Real.norm_of_nonneg hu_pos.le, dist_eq_norm]
  have hdist_bc' : dist b c' = u * dist b c := by
    rw [dist_comm b c', hdist_c'b, dist_comm c b]
  have hsub_ac : a' - c' = u • (a - c) := by
    simp only [ha'_def, hc'_def]
    module
  have hdist_a'c' : dist a' c' = u * dist a c := by
    rw [dist_eq_norm, hsub_ac, norm_smul, Real.norm_of_nonneg hu_pos.le, dist_eq_norm]
  have hadd1 : dist a a' + dist a' b = dist a b := dist_add_dist_of_mem_segment ha'_mem
  have hadd2 : dist b c' + dist c' c = dist b c := dist_add_dist_of_mem_segment hc'_mem
  have hstrict : dist a c < dist a b + dist b c := dist_lt_dist_add_dist_iff.mpr hbc
  have hmul : u * dist a c < u * dist a b + u * dist b c := by
    have h := mul_lt_mul_of_pos_left hstrict hu_pos
    rwa [mul_add] at h
  have hmid : dist a a' + dist a' c' + dist c' c < dist a b + dist b c := by
    linarith [hadd1, hdist_a'b, hadd2, hdist_bc', hdist_a'c', hmul]
  have ha'_ball : a' ∈ ball b δ := by
    rw [mem_ball, hdist_a'b]
    exact huD1
  have hc'_ball : c' ∈ ball b δ := by
    rw [mem_ball, dist_comm c' b, hdist_bc']
    exact huD2
  have hcons3 : [a, b, c] ++ l₂ = a :: b :: c :: l₂ := by simp
  rw [List.append_assoc, hcons3] at hfeas
  rw [feasible_append_cons] at hfeas
  simp only [feasible_cons_cons] at hfeas
  obtain ⟨hpre, hab_seg, hbc_seg, hsuf⟩ := hfeas
  have hseg1 : segment ℝ a a' ⊆ F :=
    ((convex_segment a b).segment_subset (left_mem_segment ℝ a b) ha'_mem).trans hab_seg
  have ha'_U : a' ∈ U := hδsub ha'_ball
  have hc'_U : c' ∈ U := hδsub hc'_ball
  have hseg2 : segment ℝ a' c' ⊆ F :=
    (hU_conv.segment_subset ⟨ha'_U, hab_seg ha'_mem⟩
      ⟨hc'_U, hbc_seg hc'_mem⟩).trans Set.inter_subset_right
  have hseg3 : segment ℝ c' c ⊆ F :=
    ((convex_segment b c).segment_subset hc'_mem (right_mem_segment ℝ b c)).trans hbc_seg
  have hcons4 : [a, a', c', c] ++ l₂ = a :: a' :: c' :: c :: l₂ := by simp
  refine ⟨a', c', ha'_mem, hc'_mem, ?_, ?_, ?_, ?_⟩
  · rw [hdist_a'b]
    exact huD1_eps
  · rw [hdist_c'b, dist_comm c b]
    exact huD2_eps
  · rw [List.append_assoc, hcons4, feasible_append_cons]
    simp only [feasible_cons_cons]
    exact ⟨hpre, hseg1, hseg2, hseg3, hsuf⟩
  · have hlen_orig :
        polyLen (l₁ ++ [a, b, c] ++ l₂)
          = polyLen (l₁ ++ [a]) + ((dist a b + dist b c) + polyLen (c :: l₂)) := by
      rw [List.append_assoc, hcons3, polyLen_append_cons]
      simp only [polyLen_cons_cons]
      ring
    have hlen_new :
        polyLen (l₁ ++ [a, a', c', c] ++ l₂)
          = polyLen (l₁ ++ [a])
            + ((dist a a' + dist a' c' + dist c' c) + polyLen (c :: l₂)) := by
      rw [List.append_assoc, hcons4, polyLen_append_cons]
      simp only [polyLen_cons_cons]
      ring
    rw [hlen_orig, hlen_new]
    linarith [hmid]

/-- (L) Local shortening at an interior non-between bend. -/
theorem local_shortening (F : Set plane) (l₁ l₂ : List plane) (a b c : plane)
    (hfeas : Feasible F (l₁ ++ [a, b, c] ++ l₂))
    (hb : b ∈ interior F) (hbc : ¬ Wbtw ℝ a b c) (ε : ℝ) (hε : 0 < ε) :
    ∃ a' c' : plane, a' ∈ segment ℝ a b ∧ c' ∈ segment ℝ b c ∧
      dist a' b < ε ∧ dist c' b < ε ∧
      Feasible F (l₁ ++ [a, a', c', c] ++ l₂) ∧
      polyLen (l₁ ++ [a, a', c', c] ++ l₂) < polyLen (l₁ ++ [a, b, c] ++ l₂) := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hb
  obtain ⟨δ, hδpos, hδsub⟩ := hb
  exact local_shortening_core F l₁ l₂ a b c hfeas
    ⟨ball b δ, ball_mem_nhds b hδpos, by
      rw [Set.inter_eq_self_of_subset_left hδsub]
      exact convex_ball b δ⟩
    hbc ε hε

/-- (T0) A length-minimal feasible polyline is weakly between at every interior bend. -/
theorem wbtw_of_minimal (F : Set plane) (l₁ l₂ : List plane) (a b c : plane)
    (hfeas : Feasible F (l₁ ++ [a, b, c] ++ l₂)) (hb : b ∈ interior F)
    (hmin : ∀ l' : List plane, Feasible F l' →
      l'.head? = (l₁ ++ [a, b, c] ++ l₂).head? →
      l'.getLast? = (l₁ ++ [a, b, c] ++ l₂).getLast? →
      polyLen (l₁ ++ [a, b, c] ++ l₂) ≤ polyLen l') :
    Wbtw ℝ a b c := by
  by_contra hbc
  obtain ⟨a', c', _, _, _, _, hfeas', hlt⟩ :=
    local_shortening F l₁ l₂ a b c hfeas hb hbc 1 one_pos
  have hhead : (l₁ ++ [a, a', c', c] ++ l₂).head? = (l₁ ++ [a, b, c] ++ l₂).head? := by simp
  have hlast : (l₁ ++ [a, a', c', c] ++ l₂).getLast? = (l₁ ++ [a, b, c] ++ l₂).getLast? := by simp
  have hle := hmin _ hfeas' hhead hlast
  linarith

end Cslib.Planning.MotionPlanning.PathShortening
