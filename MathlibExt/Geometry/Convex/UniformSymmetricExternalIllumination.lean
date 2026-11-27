/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Convex.Illumination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# Uniform covering of symmetric bodies and uniform illumination by external points

For a convex body $K \subseteq \mathbb{R}^n$ with $n \ge 1$, a cover of $K$ by $q$ translates of
its interior and an illumination of $K$ by $q$ points outside $K$ determine each other. The main
result, `ConvexCovering.uniformSymmetricExternalIlluminationInterpretation`, deduces that every
centrally symmetric convex body in $\mathbb{R}^n$ is covered by $q$ translates of its interior if
and only if every such body is illuminated by $q$ external points.

Sources: Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction; Bezdek and Khan,
arXiv:1602.06040v2, introduction.
-/

public section

namespace ConvexCovering

open Filter Metric Set Topology

/- A cover by translates `w i + int K` gives light sources. For a small `τ > 0`, every boundary
point `x` moves to `x + τ • (x - c)`, still inside some `w i + int K`; then the ray from
`c + τ⁻¹ • w i` through `x` meets the interior beyond `x`, which by convexity forces that source to
lie outside `K`. -/
private theorem illuminatedByExternalPoints_of_coveredByInteriorTranslates {n q : ℕ}
    (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (h : CoveredByInteriorTranslates K q) : IlluminatedByExternalPoints K q := by
  classical
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨c, hc⟩ := hK.2.2
  obtain ⟨z, hz⟩ := (ne_univ_iff_exists_notMem K).mp hK.1.ne_univ
  obtain ⟨w, hw⟩ := h
  -- A whole neighbourhood of `K` still lies in the open union of the translates.
  obtain ⟨δ, hδ, hthick⟩ := hK.1.exists_thickening_subset_open
    (isOpen_iUnion fun i ↦ isOpenMap_add_left (w i) _ isOpen_interior) hw
  obtain ⟨r, hKr⟩ := hK.1.isBounded.subset_closedBall c
  -- Steps `τ • (x - c)` from points `x` of `K` are shorter than `δ`.
  obtain ⟨τ, hτ, hτr⟩ := exists_pos_mul_lt hδ r
  -- The translate `w i` gives the source `c + τ⁻¹ • w i` when that point lies outside `K`.
  let p (i : Fin q) : EuclideanSpace ℝ (Fin n) :=
    if c + τ⁻¹ • w i ∈ K then z else c + τ⁻¹ • w i
  refine ⟨p, fun i ↦ ?_, fun x hx ↦ ?_⟩
  · change (if c + τ⁻¹ • w i ∈ K then z else c + τ⁻¹ • w i) ∉ K
    split_ifs with hi
    exacts [hz, hi]
  have hxK : x ∈ K := hK.1.isClosed.frontier_subset hx
  have hnear : x + τ • (x - c) ∈ thickening δ K := by
    refine mem_thickening_iff.mpr ⟨x, hxK, ?_⟩
    have hxc : ‖x - c‖ ≤ r := mem_closedBall_iff_norm.mp (hKr hxK)
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ.le]
    calc τ * ‖x - c‖ ≤ τ * r := by gcongr
      _ = r * τ := mul_comm τ r
      _ < δ := hτr
  obtain ⟨i, y, hy, hyx⟩ := mem_iUnion.mp (hthick hnear)
  set P := c + τ⁻¹ • w i with hP_def
  have hray : x + τ • (x - P) = y := by
    have hyx' : w i + y = x + τ • (x - c) := hyx
    calc x + τ • (x - P) = x + τ • (x - c) - w i := by
          rw [hP_def, sub_add_eq_sub_sub, smul_sub _ (x - c), smul_inv_smul₀ hτ.ne']; abel
      _ = y := by rw [← hyx']; abel
  -- A source in `K` would put `x`, which lies between it and an interior point, in the interior.
  have hout : P ∉ K := by
    intro hP
    apply hx.2
    have hy' : x + τ • (x - P) ∈ interior K := by rwa [hray]
    have hmem := hK.2.1.add_smul_sub_mem_interior hP hy' (t := (1 + τ)⁻¹)
      ⟨by positivity, inv_le_one_of_one_le₀ (by linarith)⟩
    have hcalc : P + (1 + τ)⁻¹ • (x + τ • (x - P) - P) = x := by
      rw [show x + τ • (x - P) - P = (1 + τ) • (x - P) by module,
        inv_smul_smul₀ (by positivity : (1 + τ) ≠ 0), add_sub_cancel]
    rwa [hcalc] at hmem
  have hpi : p i = P := ite_eq_right hout
  refine ⟨i, (externalPointIlluminates_iff_inwardRay _ _ _).mpr ⟨hpi ▸ hout, hx, τ, hτ, ?_⟩⟩
  rw [hpi, hray]
  exact hy

/- Light sources `p i` give a cover by the translates `ε • (p i - c) + int K` for one `ε > 0`. By
convexity, a boundary point illuminated by `p i` enters the interior after a step along
`c - p i`, and compactness of `K` makes one step length work for every point. -/
private theorem coveredByInteriorTranslates_of_illuminatedByExternalPoints {n q : ℕ}
    (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (h : IlluminatedByExternalPoints K q) : CoveredByInteriorTranslates K q := by
  obtain ⟨p, -, hillum⟩ := h
  obtain ⟨c, hc⟩ := hK.2.2
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨b, hb⟩ := nonempty_frontier_iff.mpr ⟨⟨c, interior_subset hc⟩, hK.1.ne_univ⟩
  obtain ⟨i₀, _⟩ := hillum b hb
  -- `U t` consists of the points of `K` that enter the interior after a step `t • (c - p i)`.
  let U (t : Ioi (0 : ℝ)) : Set K :=
    ⋃ i, (fun x : K ↦ x.val + t.val • (c - p i)) ⁻¹' interior K
  have hOpen (t) : IsOpen (U t) := isOpen_iUnion fun i ↦
    isOpen_interior.preimage (continuous_subtype_val.add_const _)
  have hCover : (univ : Set K) ⊆ ⋃ t, U t := by
    intro x _
    by_cases hx : x.val ∈ interior K
    · -- A short enough step keeps an interior point inside.
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), x.val + t • (c - p i₀) ∈ interior K := by
        apply nhdsWithin_le_nhds
        have hcont : Continuous fun t : ℝ ↦ x.val + t • (c - p i₀) := by fun_prop
        exact hcont.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hx)
      obtain ⟨t, ht, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
      exact mem_iUnion.mpr ⟨⟨t, ht0⟩, mem_iUnion.mpr ⟨i₀, ht⟩⟩
    · obtain ⟨i, hi⟩ := hillum x.val ⟨subset_closure x.property, hx⟩
      obtain ⟨-, -, τ, hτ, hin⟩ := (externalPointIlluminates_iff_inwardRay _ _ _).mp hi
      -- The point `x + τ • (x - p i)` and the centre `c` are interior, so is a point between them.
      have hmem := hK.2.1.add_smul_sub_mem_interior (interior_subset hin) hc
        (t := τ / (1 + τ))
        ⟨by positivity, (div_le_one (by positivity : (0 : ℝ) < 1 + τ)).mpr (by linarith)⟩
      have hstep : x.val + τ • (x.val - p i) + (τ / (1 + τ)) • (c - (x.val + τ • (x.val - p i)))
          = x.val + (τ / (1 + τ)) • (c - p i) := by
        match_scalars <;> field_simp <;> ring
      rw [hstep] at hmem
      exact mem_iUnion.mpr ⟨⟨τ / (1 + τ), mem_Ioi.mpr (by positivity)⟩, mem_iUnion.mpr ⟨i, hmem⟩⟩
  -- Shortening a successful step keeps its endpoint inside, by convexity.
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
  refine (coveredByTranslates_iff _ _).mpr ⟨fun i ↦ -(t.val • (c - p i)), fun x hx ↦ ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (ht (mem_univ (⟨x, hx⟩ : K)))
  exact ⟨i, x + t.val • (c - p i), hi, by simp⟩

/-- **Uniform covering of symmetric bodies and uniform illumination by external points.** For
integers $n \ge 1$ and $q \ge 0$, every centrally symmetric convex body in $\mathbb{R}^n$ (a
compact convex set with nonempty interior that is symmetric about some point) can be covered by
$q$ translates of its interior if and only if every centrally symmetric convex body $K$ in
$\mathbb{R}^n$ is illuminated by $q$ external points: there are points $p_1, \dots, p_q$ outside
$K$ such that each boundary point $x$ of $K$ has some $i$ and some $t > 1$ with
$p_i + t(x - p_i)$ in the interior of $K$.

Source: Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction, and Bezdek and Khan,
arXiv:1602.06040v2, introduction; follows from the two finite-count equivalences. -/
theorem uniformSymmetricExternalIlluminationInterpretation (n : ℕ) (hn : 0 < n) (q : ℕ) :
    UniformSymmetricInteriorTranslateBound n q ↔
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K → IsCentrallySymmetric K →
        IlluminatedByExternalPoints K q :=
  ⟨fun h K hK hsymm ↦
      illuminatedByExternalPoints_of_coveredByInteriorTranslates hn hK (h K hK hsymm),
    fun h K hK hsymm ↦
      coveredByInteriorTranslates_of_illuminatedByExternalPoints hn hK (h K hK hsymm)⟩

end ConvexCovering
