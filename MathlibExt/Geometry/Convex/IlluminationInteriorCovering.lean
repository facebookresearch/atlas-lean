/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Convex.Illumination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Illumination by directions and covering by interior translates

The least number of illuminating directions equals the least number of interior translates
covering a convex body in positive dimension.
-/

public section

namespace ConvexCovering

open NormedSpace Set

private theorem coveredByTranslates_of_illuminatedByDirections {n q : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (h : IlluminatedByDirections K q) : CoveredByTranslates K (interior K) q := by
  obtain ⟨v, hv, hillum⟩ := h
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨b, hb⟩ := nonempty_frontier_iff.mpr ⟨hK.2.2.mono interior_subset, hK.1.ne_univ⟩
  obtain ⟨i₀, _⟩ := hillum b hb
  -- U t consists of points of K that enter the interior after a step of length t.
  let U (t : Ioi (0 : ℝ)) : Set K :=
    ⋃ i, (fun x : K ↦ x.val + t.val • v i) ⁻¹' interior K
  have hOpen (t) : IsOpen (U t) := isOpen_iUnion fun i ↦
    isOpen_interior.preimage (continuous_subtype_val.add_const _)
  have hCover : (univ : Set K) ⊆ ⋃ t, U t := by
    intro x _
    by_cases hx : x.val ∈ interior K
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x.val hx
      refine mem_iUnion.mpr ⟨⟨r / 2, half_pos hr⟩, mem_iUnion.mpr ⟨i₀, hball ?_⟩⟩
      simpa [Metric.mem_ball, dist_eq_norm, norm_smul, hv, abs_of_pos hr] using half_lt_self hr
    · obtain ⟨i, _, _, t, ht, hi⟩ := hillum x.val ⟨subset_closure x.property, hx⟩
      exact mem_iUnion.mpr ⟨⟨t, ht⟩, mem_iUnion.mpr ⟨i, hi⟩⟩
  -- Shortening any successful step keeps its endpoint inside, by convexity.
  have hAnti : Antitone U := by
    intro s t hst x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hratio : s.val / t.val ∈ Ioc (0 : ℝ) 1 :=
      ⟨div_pos s.property t.property, (div_le_one t.property).mpr hst⟩
    refine mem_iUnion.mpr ⟨i, ?_⟩
    simpa [smul_smul, t.property.ne'] using
      hK.2.1.add_smul_mem_interior x.property hi hratio
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK.1
  obtain ⟨t, ht⟩ := isCompact_univ.elim_directed_cover U hOpen hCover
    (fun s t ↦ ⟨min s t, hAnti (min_le_left _ _), hAnti (min_le_right _ _)⟩)
  refine (coveredByTranslates_iff _ _).mpr ⟨fun i ↦ -(t.val • v i), fun x hx ↦ ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (ht (mem_univ (⟨x, hx⟩ : K)))
  exact ⟨i, x + t.val • v i, hi, by simp⟩

private theorem illuminatedByDirections_of_coveredByTranslates {n q : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (h : CoveredByTranslates K (interior K) q) : IlluminatedByDirections K q := by
  classical
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨u, hu⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin n)) zero_le_one
  obtain ⟨w, hw⟩ := (coveredByTranslates_iff _ _).mp h
  -- A zero translate covers no boundary point, so it can be assigned any unit direction.
  let v (i : Fin q) := if w i = 0 then u else normalize (-w i)
  have hv (i) : ‖v i‖ = 1 := by
    by_cases hi : w i = 0
    · simpa [v, hi] using hu
    · simp [v, hi, norm_normalize]
  refine ⟨v, hv, fun x hx ↦ ?_⟩
  obtain ⟨i, y, hy, rfl⟩ := hw x (hK.1.isClosed.frontier_subset hx)
  have hi : w i ≠ 0 := fun he ↦ hx.2 (by simpa [he] using hy)
  refine ⟨i, hx, hv i, ‖-w i‖, norm_pos_iff.mpr (neg_ne_zero.mpr hi), ?_⟩
  simpa [v, hi] using hy

/-- **Directional illumination number equals the interior-translate covering number.** For every
$n \ge 1$ and every convex body $K \subseteq \mathbb{R}^n$, the directional illumination number of
$K$ equals the least $q$ such that $K$ is covered by $q$ translates of its interior
$\operatorname{int} K$. Both sides take the value $\infty$ when no finite family exists.

Source: Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction; follows from the
finite-count equivalence, whose Lean proof is also requested here. -/
theorem directionalInteriorCoveringNumbersEqual (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K) :
    directionalIlluminationNumber K = translateCoveringNumber K (interior K) := by
  have hcounts : {q : ℕ | IlluminatedByDirections K q} =
      {q : ℕ | CoveredByTranslates K (interior K) q} :=
    Set.ext fun _ ↦ ⟨coveredByTranslates_of_illuminatedByDirections hn hK,
      illuminatedByDirections_of_coveredByTranslates hn hK⟩
  simp only [directionalIlluminationNumber, translateCoveringNumber, hcounts]

end ConvexCovering
