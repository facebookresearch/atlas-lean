/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Finset.Prod

/-!
# Decreasing finite unions of compact convex sets

Let E be a proper normed real vector space and K ⊆ E compact. There are
decreasing compact closed neighborhoods F_n of K, each a finite union of
compact convex pieces, with K ⊆ interior(F_n) in E. Every x ∈ F_n is within
distance 1/(n+1) of some c ∈ K, and the intersection of the F_n is K.
Empty K, empty pieces and empty finite families are permitted.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set

universe w

/-- For n ∈ ℕ, the real approximation radius is ρ_n = 1/((n : ℝ)+1). -/
private def compactApproximationRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- For every n ∈ ℕ, the real radius ρ_n = 1/((n : ℝ)+1) is positive. -/
private theorem compactApproximationRadius_pos (n : ℕ) :
    0 < compactApproximationRadius n :=
  one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one)

/-- For finite families s,t of subsets of any type E, form the finite family
of intersections A ∩ B with A ∈ s and B ∈ t. -/
private def compactIntersectionPieces {E : Type w}
    (s t : Finset (Set E)) : Finset (Set E) := by
  classical
  exact (s ×ˢ t).image (fun p => p.1 ∩ p.2)

/-- For finite families s,t of subsets of any type E, the union of their
pairwise intersections equals (⋃ A ∈ s, A) ∩ (⋃ B ∈ t, B). -/
private theorem compactIntersectionPieces_union {E : Type w} (s t : Finset (Set E)) :
    (⋃ C ∈ compactIntersectionPieces s t, C) = (⋃ C ∈ s, C) ∩ ⋃ C ∈ t, C := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hx
    change C ∈ (s ×ˢ t).image (fun p => p.1 ∩ p.2) at hC
    obtain ⟨⟨A, B⟩, hAB, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨hA, hB⟩ := Finset.mem_product.mp hAB
    exact ⟨mem_iUnion₂.mpr ⟨A, hA, hxC.1⟩, mem_iUnion₂.mpr ⟨B, hB, hxC.2⟩⟩
  · rintro ⟨hxS, hxT⟩
    obtain ⟨A, hA, hxA⟩ := mem_iUnion₂.mp hxS
    obtain ⟨B, hB, hxB⟩ := mem_iUnion₂.mp hxT
    refine mem_iUnion₂.mpr ⟨A ∩ B, ?_, hxA, hxB⟩
    exact Finset.mem_image.mpr ⟨(A, B), Finset.mem_product.mpr ⟨hA, hB⟩, rfl⟩

/-- Let E be a normed real vector space and s,t finite families of subsets of E.
If every member of both families is compact and convex over ℝ, each pairwise
intersection A ∩ B with A ∈ s and B ∈ t is compact and convex over ℝ. -/
private theorem compactIntersectionPieces_properties {E : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (s t : Finset (Set E))
    (hs : ∀ C ∈ s, IsCompact C ∧ Convex ℝ C)
    (ht : ∀ C ∈ t, IsCompact C ∧ Convex ℝ C) :
    ∀ C ∈ compactIntersectionPieces s t, IsCompact C ∧ Convex ℝ C := by
  classical
  intro C hC
  change C ∈ (s ×ˢ t).image (fun p => p.1 ∩ p.2) at hC
  obtain ⟨⟨A, B⟩, hAB, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨hA, hB⟩ := Finset.mem_product.mp hAB
  exact ⟨(hs A hA).1.inter_right (ht B hB).1.isClosed, (hs A hA).2.inter (ht B hB).2⟩

/-- For a sequence Q_n of finite families of subsets of E, define P_0 = Q_0
and P_(n+1) as all intersections of a member of P_n with a member of Q_(n+1). -/
private def cumulativeCompactPieces {E : Type w} (Q : ℕ → Finset (Set E)) :
    ℕ → Finset (Set E)
  | 0 => Q 0
  | n + 1 => compactIntersectionPieces (cumulativeCompactPieces Q n) (Q (n + 1))

/-- Let E be a proper normed real vector space and K ⊆ E compact. There are
an antitone sequence F_n and finite families P_n with F_n = ⋃ C ∈ P_n, C.
Every piece C ∈ P_n is compact and convex over ℝ. Each F_n is compact and
closed, K ⊆ interior(F_n) in E, and every x ∈ F_n has c ∈ K satisfying
dist(x,c) ≤ 1/((n : ℝ)+1). Moreover ⋂ n, F_n = K.
Empty K and empty finite families are allowed. -/
theorem IsCompact.exists_antitone_compact_convex_union
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {K : Set E} (hK : IsCompact K) :
    ∃ (F : ℕ → Set E) (P : ℕ → Finset (Set E)),
      Antitone F ∧
      (∀ n, F n = ⋃ C ∈ P n, C) ∧
      (∀ n C, C ∈ P n → IsCompact C ∧ Convex ℝ C) ∧
      (∀ n, IsCompact (F n) ∧ IsClosed (F n) ∧ K ⊆ interior (F n)) ∧
      (∀ n x, x ∈ F n → ∃ c ∈ K, dist x c ≤ 1 / ((n : ℝ) + 1)) ∧
      (⋂ n, F n) = K := by
  classical
  have hcover (n : ℕ) : ∃ t : Finset E, (∀ c ∈ t, c ∈ K) ∧
      K ⊆ ⋃ c ∈ t, Metric.ball c (compactApproximationRadius n) :=
    hK.elim_nhds_subcover (fun c => Metric.ball c (compactApproximationRadius n))
      (fun c _ => Metric.ball_mem_nhds c (compactApproximationRadius_pos n))
  choose t htK htCover using hcover
  let Q : ℕ → Finset (Set E) := fun n =>
    (t n).image (fun c => Metric.closedBall c (compactApproximationRadius n))
  let P := cumulativeCompactPieces Q
  let F : ℕ → Set E := fun n => ⋃ C ∈ P n, C
  have hQ_union (n : ℕ) : (⋃ C ∈ Q n, C) =
      ⋃ c ∈ t n, Metric.closedBall c (compactApproximationRadius n) := by
    simp only [Q, Finset.set_biUnion_finset_image]
  have hQ_properties (n : ℕ) : ∀ C ∈ Q n, IsCompact C ∧ Convex ℝ C := by
    intro C hC
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨isCompact_closedBall c _, convex_closedBall c _⟩
  have hQ_interior (n : ℕ) : K ⊆ interior (⋃ C ∈ Q n, C) := by
    rw [hQ_union]
    intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (htCover n hx)
    have hBall : Metric.closedBall c (compactApproximationRadius n) ⊆
        ⋃ c ∈ t n, Metric.closedBall c (compactApproximationRadius n) :=
      fun y hy => mem_iUnion₂.mpr ⟨c, hc, hy⟩
    exact interior_mono hBall (Metric.ball_subset_interior_closedBall hxc)
  have hP_properties (n : ℕ) : ∀ C ∈ P n, IsCompact C ∧ Convex ℝ C := by
    induction n with
    | zero => exact hQ_properties 0
    | succ n ih =>
      exact compactIntersectionPieces_properties (P n) (Q (n + 1)) ih (hQ_properties (n + 1))
  have hF_succ (n : ℕ) : F (n + 1) = F n ∩ ⋃ C ∈ Q (n + 1), C :=
    compactIntersectionPieces_union (P n) (Q (n + 1))
  have hF_antitone : Antitone F := by
    apply antitone_nat_of_succ_le
    intro n
    rw [hF_succ]
    exact inter_subset_left
  have hF_interior (n : ℕ) : K ⊆ interior (F n) := by
    induction n with
    | zero => exact hQ_interior 0
    | succ n ih =>
      rw [hF_succ, interior_inter]
      exact fun x hx => ⟨ih hx, hQ_interior (n + 1) hx⟩
  have hF_compact (n : ℕ) : IsCompact (F n) :=
    (P n).isCompact_biUnion (fun C hC => (hP_properties n C hC).1)
  have hF_subset (n : ℕ) : F n ⊆ ⋃ C ∈ Q n, C := by
    cases n with
    | zero => exact Subset.rfl
    | succ n =>
      rw [hF_succ]
      exact inter_subset_right
  have hF_dist (n : ℕ) (x : E) (hx : x ∈ F n) :
      ∃ c ∈ K, dist x c ≤ 1 / ((n : ℝ) + 1) := by
    have hxQ := hF_subset n hx
    rw [hQ_union] at hxQ
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hxQ
    exact ⟨c, htK n c hc, Metric.mem_closedBall.mp hxc⟩
  have hIntersection : (⋂ n, F n) = K := by
    apply Subset.antisymm
    · intro x hx
      apply hK.isClosed.closure_subset
      rw [Metric.mem_closure_iff]
      intro δ hδ
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
      obtain ⟨c, hc, hxc⟩ := hF_dist N x (mem_iInter.mp hx N)
      exact ⟨c, hc, hxc.trans_lt hN⟩
    · exact subset_iInter (fun n => (hF_interior n).trans interior_subset)
  exact ⟨F, P, hF_antitone, fun _ => rfl, hP_properties,
    fun n => ⟨hF_compact n, (hF_compact n).isClosed, hF_interior n⟩,
    hF_dist, hIntersection⟩
