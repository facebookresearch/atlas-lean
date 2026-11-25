/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import MathlibExt.Geometry.Euclidean.CarnotInradius

@[expose] public section

section
namespace MetaMathlibExt

/-- Four points on a common metric sphere are cospherical in Mathlib's sense. -/
private lemma cospherical_of_mem_sphere
    (O : EuclideanSpace ℝ (Fin 2)) (R : ℝ)
    (A B C D : EuclideanSpace ℝ (Fin 2))
    (hA : A ∈ Metric.sphere O R) (hB : B ∈ Metric.sphere O R)
    (hC : C ∈ Metric.sphere O R) (hD : D ∈ Metric.sphere O R) :
    EuclideanGeometry.Cospherical ({A, B, C, D} : Set (EuclideanSpace ℝ (Fin 2))) := by
  rw [EuclideanGeometry.cospherical_iff_exists_sphere]
  refine ⟨⟨O, R⟩, ?_⟩
  intro x hx
  change x ∈ Metric.sphere O R
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hA
  · exact hB
  · exact hC
  · exact hD

/-- Rotate a 2D vector by 90 degrees: `(-y, x)`. Perpendicular to the input. -/
private def perp2 (d : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[-(d 1), d 0]

private lemma perp2_zero (d : EuclideanSpace ℝ (Fin 2)) : (perp2 d) 0 = -(d 1) :=
  rfl

private lemma perp2_one (d : EuclideanSpace ℝ (Fin 2)) : (perp2 d) 1 = d 0 :=
  rfl

private lemma inner_perp2_self (d : EuclideanSpace ℝ (Fin 2)) :
    inner (𝕜 := ℝ) d (perp2 d) = 0 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, perp2_zero, perp2_one]
  simp only [RCLike.inner_apply, RCLike.conj_to_real]
  ring

private lemma norm_perp2 (d : EuclideanSpace ℝ (Fin 2)) :
    ‖perp2 d‖ = ‖d‖ := by
  have hsq : ‖perp2 d‖ ^ 2 = ‖d‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_two, Fin.sum_univ_two, perp2_zero, perp2_one]
    ring
  have h1 : Real.sqrt (‖perp2 d‖ ^ 2) = Real.sqrt (‖d‖ ^ 2) := by rw [hsq]
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1

/-- Any nonzero 2D direction has a unit perpendicular. -/
private lemma exists_unit_perp (d : EuclideanSpace ℝ (Fin 2)) (hd : d ≠ 0) :
    ∃ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 ∧ inner (𝕜 := ℝ) d n = 0 := by
  have hnorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hinv : 0 < (‖d‖⁻¹ : ℝ) := inv_pos.mpr hnorm
  refine ⟨(‖d‖⁻¹) • perp2 d, ?_, ?_⟩
  · rw [norm_smul, norm_perp2, Real.norm_eq_abs, abs_of_pos hinv]
    exact inv_mul_cancel₀ (ne_of_gt hnorm)
  · rw [inner_smul_right, inner_perp2_self, mul_zero]

private theorem japaneseQuads_orth_eq_aux
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)]
    (u n : V) (hu : u ≠ 0) (hn : ‖n‖ = 1) (hun : inner (𝕜 := ℝ) u n = 0)
    (w : V) (hw : inner (𝕜 := ℝ) u w = 0) :
    w = (inner (𝕜 := ℝ) w n) • n := by
  have h2 : Module.finrank ℝ V = 1 + 1 := by have h : Module.finrank ℝ V = 2 := Fact.out; omega
  have : Fact (Module.finrank ℝ V = 1 + 1) := Fact.mk h2
  have hfr := Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (E := V) (n := 1) (v := u) hu
  have hfin : Module.finrank ℝ ((ℝ ∙ u)ᗮ) = 1 := hfr
  rw [finrank_eq_one_iff'] at hfin
  obtain ⟨g, hg0, hg⟩ := hfin
  have hnmem : n ∈ (ℝ ∙ u)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]; exact hun
  have hwmem : w ∈ (ℝ ∙ u)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]; exact hw
  have hn0 : n ≠ 0 := by intro h0; rw [h0, norm_zero] at hn; norm_num at hn
  obtain ⟨c, hc⟩ := hg ⟨n, hnmem⟩
  obtain ⟨d, hd⟩ := hg ⟨w, hwmem⟩
  have hnc : c • (g : V) = n := by have := congrArg Subtype.val hc; simpa using this
  have hwd : d • (g : V) = w := by have := congrArg Subtype.val hd; simpa using this
  have hc0 : c ≠ 0 := by intro h0; rw [h0, zero_smul] at hnc; exact hn0 hnc.symm
  have hnn : inner (𝕜 := ℝ) n n = 1 := by rw [real_inner_self_eq_norm_sq, hn, one_pow]
  have hgw : (g : V) = c⁻¹ • n := by
    have h1 : (c⁻¹ * c) • (g : V) = (g : V) := by rw [inv_mul_cancel₀ hc0, one_smul]
    rw [mul_smul, hnc] at h1; exact h1.symm
  have hw2 : w = (d * c⁻¹) • n := by
    have h1 : (d * c⁻¹) • n = d • (c⁻¹ • n) := by rw [mul_smul]
    rw [h1, ← hgw, ← hwd]
  have hcoeff : d * c⁻¹ = inner (𝕜 := ℝ) w n := by
    rw [hw2, inner_smul_left, hnn]; simp
  rw [← hcoeff]; exact hw2

/-- Off-line point has nonzero signed distance to the line. -/
private lemma inner_ne_zero_of_not_collinear
    (P Q R : EuclideanSpace ℝ (Fin 2))
    (hTri : ¬Collinear ℝ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2))))
    (hQR : Q ≠ R)
    (n : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1)
    (hperp : inner (𝕜 := ℝ) (R -ᵥ Q) n = 0) :
    inner (𝕜 := ℝ) (P -ᵥ Q) n ≠ 0 := by
  have hfin : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro h0
  have hd : (R -ᵥ Q) ≠ 0 := vsub_ne_zero.mpr hQR.symm
  have hn0 : n ≠ 0 := by
    intro h00
    rw [h00, norm_zero] at hn
    norm_num at hn
  have hnorm_d : 0 < ‖R -ᵥ Q‖ := norm_pos_iff.mpr hd
  set n' : EuclideanSpace ℝ (Fin 2) := (‖R -ᵥ Q‖⁻¹) • (R -ᵥ Q) with hn'def
  have hn'_unit : ‖n'‖ = 1 := by
    rw [hn'def, norm_smul, Real.norm_eq_abs]
    have hinv : 0 < ((‖R -ᵥ Q‖⁻¹ : ℝ)) := inv_pos.mpr hnorm_d
    rw [abs_of_pos hinv]
    exact inv_mul_cancel₀ (ne_of_gt hnorm_d)
  have hnn' : inner (𝕜 := ℝ) n n' = 0 := by
    rw [hn'def, inner_smul_right, real_inner_comm _ n, hperp, mul_zero]
  have hnv : inner (𝕜 := ℝ) n (P -ᵥ Q) = 0 := by
    rw [real_inner_comm]; exact h0
  have hdep := japaneseQuads_orth_eq_aux n n' hn0 hn'_unit hnn' (P -ᵥ Q) hnv
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r • (R -ᵥ Q) = P -ᵥ Q := by
    refine ⟨inner (𝕜 := ℝ) (P -ᵥ Q) n' * ‖R -ᵥ Q‖⁻¹, ?_⟩
    conv_rhs => rw [hdep, hn'def]
    rw [smul_smul]
  have hmem : P ∈ line[ℝ, Q, R] := by
    have hv : (P -ᵥ Q) +ᵥ Q ∈ line[ℝ, Q, R] := by
      rw [vadd_left_mem_affineSpan_pair]
      exact ⟨r, hr⟩
    rwa [vsub_vadd] at hv
  exact hTri (collinear_insert_of_mem_affineSpan_pair hmem)

/-- Closed half-space defined by a point and normal is convex. -/
private lemma convex_halfspace (Q : EuclideanSpace ℝ (Fin 2))
    (n : EuclideanSpace ℝ (Fin 2)) :
    Convex ℝ {p : EuclideanSpace ℝ (Fin 2) | 0 ≤ inner (𝕜 := ℝ) (p -ᵥ Q) n} := by
  intro a ha b hb t1 t2 ht1 ht2 hsum
  simp only [Set.mem_ofPred_eq] at ha hb ⊢
  have hQ' : t1 • Q + t2 • Q = Q := by
    rw [← add_smul, hsum, one_smul]
  have hv : (t1 • a + t2 • b) -ᵥ Q = t1 • (a -ᵥ Q) + t2 • (b -ᵥ Q) := by
    rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub]
    calc (t1 • a + t2 • b) - Q
        = (t1 • a + t2 • b) - (t1 • Q + t2 • Q) := by rw [hQ']
      _ = t1 • (a - Q) + t2 • (b - Q) := by module
  rw [hv, inner_add_left, inner_smul_left, inner_smul_left]
  exact add_nonneg (mul_nonneg ht1 ha) (mul_nonneg ht2 hb)

/-- Triangle lies in the closed half-space of a sideline containing it. -/
private lemma hull_subset_halfspace
    (P Q R : EuclideanSpace ℝ (Fin 2))
    (n : EuclideanSpace ℝ (Fin 2))
    (hperp : inner (𝕜 := ℝ) (R -ᵥ Q) n = 0)
    (hin : 0 ≤ inner (𝕜 := ℝ) (P -ᵥ Q) n) :
    convexHull ℝ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2))) ⊆
      {p : EuclideanSpace ℝ (Fin 2) | 0 ≤ inner (𝕜 := ℝ) (p -ᵥ Q) n} := by
  apply convexHull_min _ (convex_halfspace Q n)
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  simp only [Set.mem_ofPred_eq]
  rcases hp with rfl | rfl | rfl
  · exact hin
  · rw [vsub_self, inner_zero_left]
  · rw [hperp]

/-- Segment point minus base is a multiple of the side direction. -/
private lemma vsub_of_mem_segment
    (Q R x : EuclideanSpace ℝ (Fin 2)) (h : x ∈ segment ℝ Q R) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x -ᵥ Q = t • (R -ᵥ Q) := by
  obtain ⟨a, b, ha, hb, hab, hx⟩ := h
  refine ⟨b, hb, ?_, ?_⟩
  · have ha' : a = 1 - b := by linarith
    have h1b : 0 ≤ 1 - b := by rw [← ha']; exact ha
    linarith
  · rw [← hx, vsub_eq_sub, vsub_eq_sub]
    have h1 : (a + b) • Q = Q := by rw [hab, one_smul]
    calc a • Q + b • R - Q
        = a • Q + b • R - (a + b) • Q := by congr 1; exact h1.symm
      _ = b • (R - Q) := by rw [add_smul]; module

/-- Incircle center is at signed distance `r` from each sideline. -/
private lemma inner_eq_radius_of_incircle
    (P Q R I : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 < r)
    (hsub : Metric.closedBall I r ⊆ convexHull ℝ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2))))
    (htouch : (segment ℝ Q R ∩ Metric.sphere I r).Nonempty)
    (n : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1)
    (hperp : inner (𝕜 := ℝ) (R -ᵥ Q) n = 0)
    (hin : 0 < inner (𝕜 := ℝ) (P -ᵥ Q) n) :
    inner (𝕜 := ℝ) (I -ᵥ Q) n = r := by
  apply le_antisymm
  · obtain ⟨x, hxseg, hxsph⟩ := htouch
    have hdist : dist x I = r := Metric.mem_sphere.mp hxsph
    obtain ⟨t, ht0, ht1, hxv⟩ := vsub_of_mem_segment Q R x hxseg
    have hx0 : inner (𝕜 := ℝ) (x -ᵥ Q) n = 0 := by
      rw [hxv, inner_smul_left, hperp, mul_zero]
    have hdecomp : I -ᵥ Q = (I -ᵥ x) + (x -ᵥ Q) := by
      rw [← vsub_add_vsub_cancel I x Q]
    have hI : inner (𝕜 := ℝ) (I -ᵥ Q) n = inner (𝕜 := ℝ) (I -ᵥ x) n := by
      rw [hdecomp, inner_add_left, hx0, add_zero]
    rw [hI]
    have hcs : inner (𝕜 := ℝ) (I -ᵥ x) n ≤ ‖I -ᵥ x‖ * ‖n‖ :=
      real_inner_le_norm _ _
    rw [hn, mul_one] at hcs
    have hnorm : ‖I -ᵥ x‖ = r := by
      have hdx : dist I x = r := by rw [dist_comm]; exact hdist
      rwa [dist_eq_norm_vsub] at hdx
    rwa [hnorm] at hcs
  · by_contra hlt
    push Not at hlt
    set y : EuclideanSpace ℝ (Fin 2) := I - r • n with hydef
    have hyball : y ∈ Metric.closedBall I r := by
      rw [Metric.mem_closedBall, dist_eq_norm_vsub]
      have hvy : y -ᵥ I = -(r • n) := by
        rw [hydef, vsub_eq_sub]
        module
      rw [hvy, norm_neg, norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos hr]
    have yhull : y ∈ convexHull ℝ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2))) :=
      hsub hyball
    have hhalf := hull_subset_halfspace P Q R n hperp hin.le yhull
    simp only [Set.mem_ofPred_eq] at hhalf
    have hnn : inner (𝕜 := ℝ) n n = 1 := by
      rw [real_inner_self_eq_norm_sq, hn, one_pow]
    have hyv : y -ᵥ Q = (I -ᵥ Q) - r • n := by
      rw [hydef, vsub_eq_sub, vsub_eq_sub]
      module
    have hinner : inner (𝕜 := ℝ) (y -ᵥ Q) n
        = inner (𝕜 := ℝ) (I -ᵥ Q) n - r := by
      rw [hyv, inner_sub_left, real_inner_smul_left, hnn, mul_one]
    linarith

/-- Triangle hull lies in half-space, with hull vertices possibly permuted. -/
private lemma hull_subset_halfspace_of_mem
    (A B C P Q R : EuclideanSpace ℝ (Fin 2))
    (n : EuclideanSpace ℝ (Fin 2))
    (hperp : inner (𝕜 := ℝ) (R -ᵥ Q) n = 0)
    (hin : 0 ≤ inner (𝕜 := ℝ) (P -ᵥ Q) n)
    (hAmem : A ∈ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2))))
    (hBmem : B ∈ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2))))
    (hCmem : C ∈ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2)))) :
    convexHull ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) ⊆
      {p : EuclideanSpace ℝ (Fin 2) | 0 ≤ inner (𝕜 := ℝ) (p -ᵥ Q) n} := by
  apply convexHull_min _ (convex_halfspace Q n)
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  simp only [Set.mem_ofPred_eq]
  have hP : 0 ≤ inner (𝕜 := ℝ) (P -ᵥ Q) n := hin
  have hQ : 0 ≤ inner (𝕜 := ℝ) (Q -ᵥ Q) n := by
    rw [vsub_self, inner_zero_left]
  have hR : 0 ≤ inner (𝕜 := ℝ) (R -ᵥ Q) n := by rw [hperp]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hAmem hBmem hCmem
  rcases hp with rfl | rfl | rfl
  · rcases hAmem with rfl | rfl | rfl
    · exact hP
    · exact hQ
    · exact hR
  · rcases hBmem with rfl | rfl | rfl
    · exact hP
    · exact hQ
    · exact hR
  · rcases hCmem with rfl | rfl | rfl
    · exact hP
    · exact hQ
    · exact hR

/-- Incircle signed distance, with hull vertices possibly permuted. -/
private lemma inner_eq_radius_of_incircle_of_mem
    (A B C P Q R I : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 < r)
    (hsub : Metric.closedBall I r ⊆ convexHull ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (htouch : (segment ℝ Q R ∩ Metric.sphere I r).Nonempty)
    (n : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1)
    (hperp : inner (𝕜 := ℝ) (R -ᵥ Q) n = 0)
    (hin : 0 < inner (𝕜 := ℝ) (P -ᵥ Q) n)
    (hAmem : A ∈ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2))))
    (hBmem : B ∈ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2))))
    (hCmem : C ∈ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2)))) :
    inner (𝕜 := ℝ) (I -ᵥ Q) n = r := by
  apply le_antisymm
  · obtain ⟨x, hxseg, hxsph⟩ := htouch
    have hdist : dist x I = r := Metric.mem_sphere.mp hxsph
    obtain ⟨t, ht0, ht1, hxv⟩ := vsub_of_mem_segment Q R x hxseg
    have hx0 : inner (𝕜 := ℝ) (x -ᵥ Q) n = 0 := by
      rw [hxv, inner_smul_left, hperp, mul_zero]
    have hdecomp : I -ᵥ Q = (I -ᵥ x) + (x -ᵥ Q) := by
      rw [← vsub_add_vsub_cancel I x Q]
    have hI : inner (𝕜 := ℝ) (I -ᵥ Q) n = inner (𝕜 := ℝ) (I -ᵥ x) n := by
      rw [hdecomp, inner_add_left, hx0, add_zero]
    rw [hI]
    have hcs : inner (𝕜 := ℝ) (I -ᵥ x) n ≤ ‖I -ᵥ x‖ * ‖n‖ :=
      real_inner_le_norm _ _
    rw [hn, mul_one] at hcs
    have hnorm : ‖I -ᵥ x‖ = r := by
      have hdx : dist I x = r := by rw [dist_comm]; exact hdist
      rwa [dist_eq_norm_vsub] at hdx
    rwa [hnorm] at hcs
  · by_contra hlt
    push Not at hlt
    set y : EuclideanSpace ℝ (Fin 2) := I - r • n with hydef
    have hyball : y ∈ Metric.closedBall I r := by
      rw [Metric.mem_closedBall, dist_eq_norm_vsub]
      have hvy : y -ᵥ I = -(r • n) := by
        rw [hydef, vsub_eq_sub]
        module
      rw [hvy, norm_neg, norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos hr]
    have yhull : y ∈ convexHull ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) :=
      hsub hyball
    have hhalf := hull_subset_halfspace_of_mem A B C P Q R n hperp hin.le
      hAmem hBmem hCmem yhull
    simp only [Set.mem_ofPred_eq] at hhalf
    have hnn : inner (𝕜 := ℝ) n n = 1 := by
      rw [real_inner_self_eq_norm_sq, hn, one_pow]
    have hyv : y -ᵥ Q = (I -ᵥ Q) - r • n := by
      rw [hydef, vsub_eq_sub, vsub_eq_sub]
      module
    have hinner : inner (𝕜 := ℝ) (y -ᵥ Q) n
        = inner (𝕜 := ℝ) (I -ᵥ Q) n - r := by
      rw [hyv, inner_sub_left, real_inner_smul_left, hnn, mul_one]
    linarith

/-- Edge AB: C and D lie strictly on the same side of line AB. -/
private lemma same_side_AB
    (A B C D Q : EuclideanSpace ℝ (Fin 2))
    (hAB : A ≠ B)
    (hQAC : Q ∈ segment ℝ A C) (hQBD : Q ∈ segment ℝ B D)
    (n0 : EuclideanSpace ℝ (Fin 2))
    (hperp0 : inner (𝕜 := ℝ) (B -ᵥ A) n0 = 0)
    (hc0 : inner (𝕜 := ℝ) (C -ᵥ A) n0 ≠ 0)
    (hd0 : inner (𝕜 := ℝ) (D -ᵥ A) n0 ≠ 0) :
    0 < inner (𝕜 := ℝ) (C -ᵥ A) n0 * inner (𝕜 := ℝ) (D -ᵥ A) n0 := by
  rcases lt_or_gt_of_ne hc0 with hcneg | hcpos
  · rcases lt_or_gt_of_ne hd0 with hdneg | hdpos
    · exact mul_pos_of_neg_of_neg hcneg hdneg
    · exfalso
      obtain ⟨t, ht0, ht1, hQt⟩ := vsub_of_mem_segment A C Q hQAC
      obtain ⟨s, hs0, hs1, hQs⟩ := vsub_of_mem_segment B D Q hQBD
      have hDB : D -ᵥ B = (D -ᵥ A) - (B -ᵥ A) := by
        rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub]
        module
      have hDBin : inner (𝕜 := ℝ) (D -ᵥ B) n0
          = inner (𝕜 := ℝ) (D -ᵥ A) n0 := by
        rw [hDB, inner_sub_left, hperp0, sub_zero]
      have hQA : Q -ᵥ A = (Q -ᵥ B) + (B -ᵥ A) :=
        (vsub_add_vsub_cancel Q B A).symm
      have hQin1 : inner (𝕜 := ℝ) (Q -ᵥ A) n0
          = t * inner (𝕜 := ℝ) (C -ᵥ A) n0 := by
        rw [hQt, real_inner_smul_left]
      have hQin2 : inner (𝕜 := ℝ) (Q -ᵥ A) n0
          = s * inner (𝕜 := ℝ) (D -ᵥ A) n0 := by
        rw [hQA, hQs, inner_add_left, real_inner_smul_left, hDBin, hperp0,
          add_zero]
      have heq : t * inner (𝕜 := ℝ) (C -ᵥ A) n0
          = s * inner (𝕜 := ℝ) (D -ᵥ A) n0 := hQin1.symm.trans hQin2
      have hL : t * inner (𝕜 := ℝ) (C -ᵥ A) n0 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht0 (le_of_lt hcneg)
      have hR : 0 ≤ s * inner (𝕜 := ℝ) (D -ᵥ A) n0 :=
        mul_nonneg hs0 (le_of_lt hdpos)
      have hL0 : t * inner (𝕜 := ℝ) (C -ᵥ A) n0 = 0 :=
        le_antisymm hL (by rw [heq]; exact hR)
      have ht0' : t = 0 := by
        rcases mul_eq_zero.mp hL0 with ht | hc
        · exact ht
        · exact absurd hc hc0
      have hQA0 : Q -ᵥ A = 0 := by rw [hQt, ht0', zero_smul]
      have hQeqA : Q = A := vsub_eq_zero_iff_eq.mp hQA0
      have hR0 : s * inner (𝕜 := ℝ) (D -ᵥ A) n0 = 0 :=
        le_antisymm (by rw [← heq]; exact hL) hR
      have hs0' : s = 0 := by
        rcases mul_eq_zero.mp hR0 with hs | hd
        · exact hs
        · exact absurd hd hd0
      have hQB0 : Q -ᵥ B = 0 := by rw [hQs, hs0', zero_smul]
      have hQeqB : Q = B := vsub_eq_zero_iff_eq.mp hQB0
      exact hAB (hQeqA.symm.trans hQeqB)
  · rcases lt_or_gt_of_ne hd0 with hdneg | hdpos
    · exfalso
      obtain ⟨t, ht0, ht1, hQt⟩ := vsub_of_mem_segment A C Q hQAC
      obtain ⟨s, hs0, hs1, hQs⟩ := vsub_of_mem_segment B D Q hQBD
      have hDB : D -ᵥ B = (D -ᵥ A) - (B -ᵥ A) := by
        rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub]
        module
      have hDBin : inner (𝕜 := ℝ) (D -ᵥ B) n0
          = inner (𝕜 := ℝ) (D -ᵥ A) n0 := by
        rw [hDB, inner_sub_left, hperp0, sub_zero]
      have hQA : Q -ᵥ A = (Q -ᵥ B) + (B -ᵥ A) :=
        (vsub_add_vsub_cancel Q B A).symm
      have hQin1 : inner (𝕜 := ℝ) (Q -ᵥ A) n0
          = t * inner (𝕜 := ℝ) (C -ᵥ A) n0 := by
        rw [hQt, real_inner_smul_left]
      have hQin2 : inner (𝕜 := ℝ) (Q -ᵥ A) n0
          = s * inner (𝕜 := ℝ) (D -ᵥ A) n0 := by
        rw [hQA, hQs, inner_add_left, real_inner_smul_left, hDBin, hperp0,
          add_zero]
      have heq : t * inner (𝕜 := ℝ) (C -ᵥ A) n0
          = s * inner (𝕜 := ℝ) (D -ᵥ A) n0 := hQin1.symm.trans hQin2
      have hL : 0 ≤ t * inner (𝕜 := ℝ) (C -ᵥ A) n0 :=
        mul_nonneg ht0 (le_of_lt hcpos)
      have hR : s * inner (𝕜 := ℝ) (D -ᵥ A) n0 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hs0 (le_of_lt hdneg)
      have hL0 : t * inner (𝕜 := ℝ) (C -ᵥ A) n0 = 0 :=
        le_antisymm (by rw [heq]; exact hR) hL
      have ht0' : t = 0 := by
        rcases mul_eq_zero.mp hL0 with ht | hc
        · exact ht
        · exact absurd hc hc0
      have hQA0 : Q -ᵥ A = 0 := by rw [hQt, ht0', zero_smul]
      have hQeqA : Q = A := vsub_eq_zero_iff_eq.mp hQA0
      have hR0 : s * inner (𝕜 := ℝ) (D -ᵥ A) n0 = 0 :=
        le_antisymm hR (by rw [← heq]; exact hL)
      have hs0' : s = 0 := by
        rcases mul_eq_zero.mp hR0 with hs | hd
        · exact hs
        · exact absurd hd hd0
      have hQB0 : Q -ᵥ B = 0 := by rw [hQs, hs0', zero_smul]
      have hQeqB : Q = B := vsub_eq_zero_iff_eq.mp hQB0
      exact hAB (hQeqA.symm.trans hQeqB)
    · exact mul_pos hcpos hdpos

/-- Edge BC: A and D lie strictly on the same side of line BC. -/
private lemma same_side_BC
    (A B C D Q : EuclideanSpace ℝ (Fin 2))
    (hBC : B ≠ C)
    (hQAC : Q ∈ segment ℝ A C) (hQBD : Q ∈ segment ℝ B D)
    (n0 : EuclideanSpace ℝ (Fin 2))
    (hperp0 : inner (𝕜 := ℝ) (C -ᵥ B) n0 = 0)
    (ha0 : inner (𝕜 := ℝ) (A -ᵥ B) n0 ≠ 0)
    (hd0 : inner (𝕜 := ℝ) (D -ᵥ B) n0 ≠ 0) :
    0 < inner (𝕜 := ℝ) (A -ᵥ B) n0 * inner (𝕜 := ℝ) (D -ᵥ B) n0 := by
  rcases lt_or_gt_of_ne ha0 with haneg | hapos
  · rcases lt_or_gt_of_ne hd0 with hdneg | hdpos
    · exact mul_pos_of_neg_of_neg haneg hdneg
    · exfalso
      obtain ⟨t, ht0, ht1, hQt⟩ := vsub_of_mem_segment A C Q hQAC
      obtain ⟨s, hs0, hs1, hQs⟩ := vsub_of_mem_segment B D Q hQBD
      have hCAB : C -ᵥ A = (C -ᵥ B) + (B -ᵥ A) :=
        (vsub_add_vsub_cancel C B A).symm
      have hBAB : B -ᵥ A = -(A -ᵥ B) := by
        rw [← neg_vsub_eq_vsub_rev]
      have hQB : Q -ᵥ B = (Q -ᵥ A) + (A -ᵥ B) :=
        (vsub_add_vsub_cancel Q A B).symm
      have hQin1 : inner (𝕜 := ℝ) (Q -ᵥ B) n0
          = (1 - t) * inner (𝕜 := ℝ) (A -ᵥ B) n0 := by
        rw [hQB, hQt, hCAB, hBAB, inner_add_left, real_inner_smul_left,
          inner_add_left, hperp0, inner_neg_left]
        ring
      have hQin2 : inner (𝕜 := ℝ) (Q -ᵥ B) n0
          = s * inner (𝕜 := ℝ) (D -ᵥ B) n0 := by
        rw [hQs, real_inner_smul_left]
      have heq : (1 - t) * inner (𝕜 := ℝ) (A -ᵥ B) n0
          = s * inner (𝕜 := ℝ) (D -ᵥ B) n0 := hQin1.symm.trans hQin2
      have ht1t : 0 ≤ 1 - t := by linarith
      have hL : (1 - t) * inner (𝕜 := ℝ) (A -ᵥ B) n0 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht1t (le_of_lt haneg)
      have hR : 0 ≤ s * inner (𝕜 := ℝ) (D -ᵥ B) n0 :=
        mul_nonneg hs0 (le_of_lt hdpos)
      have hL0 : (1 - t) * inner (𝕜 := ℝ) (A -ᵥ B) n0 = 0 :=
        le_antisymm hL (by rw [heq]; exact hR)
      have ht1' : t = 1 := by
        rcases mul_eq_zero.mp hL0 with ht | ha
        · have : (1 : ℝ) - t = 0 := ht
          linarith
        · exact absurd ha ha0
      have hQeqC : Q = C := by
        have hQC : Q -ᵥ A = C -ᵥ A := by rw [hQt, ht1', one_smul]
        have h0 : (Q -ᵥ A) - (C -ᵥ A) = 0 := sub_eq_zero.mpr hQC
        have hcan := vsub_sub_vsub_cancel_right Q C A
        have hQ0 : Q -ᵥ C = 0 := by rw [← hcan]; exact h0
        exact vsub_eq_zero_iff_eq.mp hQ0
      have hR0 : s * inner (𝕜 := ℝ) (D -ᵥ B) n0 = 0 :=
        le_antisymm (by rw [← heq]; exact hL) hR
      have hs0' : s = 0 := by
        rcases mul_eq_zero.mp hR0 with hs | hd
        · exact hs
        · exact absurd hd hd0
      have hQB0 : Q -ᵥ B = 0 := by rw [hQs, hs0', zero_smul]
      have hQeqB : Q = B := vsub_eq_zero_iff_eq.mp hQB0
      exact hBC (hQeqB.symm.trans hQeqC)
  · rcases lt_or_gt_of_ne hd0 with hdneg | hdpos
    · exfalso
      obtain ⟨t, ht0, ht1, hQt⟩ := vsub_of_mem_segment A C Q hQAC
      obtain ⟨s, hs0, hs1, hQs⟩ := vsub_of_mem_segment B D Q hQBD
      have hCAB : C -ᵥ A = (C -ᵥ B) + (B -ᵥ A) :=
        (vsub_add_vsub_cancel C B A).symm
      have hBAB : B -ᵥ A = -(A -ᵥ B) := by
        rw [← neg_vsub_eq_vsub_rev]
      have hQB : Q -ᵥ B = (Q -ᵥ A) + (A -ᵥ B) :=
        (vsub_add_vsub_cancel Q A B).symm
      have hQin1 : inner (𝕜 := ℝ) (Q -ᵥ B) n0
          = (1 - t) * inner (𝕜 := ℝ) (A -ᵥ B) n0 := by
        rw [hQB, hQt, hCAB, hBAB, inner_add_left, real_inner_smul_left,
          inner_add_left, hperp0, inner_neg_left]
        ring
      have hQin2 : inner (𝕜 := ℝ) (Q -ᵥ B) n0
          = s * inner (𝕜 := ℝ) (D -ᵥ B) n0 := by
        rw [hQs, real_inner_smul_left]
      have heq : (1 - t) * inner (𝕜 := ℝ) (A -ᵥ B) n0
          = s * inner (𝕜 := ℝ) (D -ᵥ B) n0 := hQin1.symm.trans hQin2
      have ht1t : 0 ≤ 1 - t := by linarith
      have hL : 0 ≤ (1 - t) * inner (𝕜 := ℝ) (A -ᵥ B) n0 :=
        mul_nonneg ht1t (le_of_lt hapos)
      have hR : s * inner (𝕜 := ℝ) (D -ᵥ B) n0 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hs0 (le_of_lt hdneg)
      have hL0 : (1 - t) * inner (𝕜 := ℝ) (A -ᵥ B) n0 = 0 :=
        le_antisymm (by rw [heq]; exact hR) hL
      have ht1' : t = 1 := by
        rcases mul_eq_zero.mp hL0 with ht | ha
        · have : (1 : ℝ) - t = 0 := ht
          linarith
        · exact absurd ha ha0
      have hQeqC : Q = C := by
        have hQC : Q -ᵥ A = C -ᵥ A := by rw [hQt, ht1', one_smul]
        have h0 : (Q -ᵥ A) - (C -ᵥ A) = 0 := sub_eq_zero.mpr hQC
        have hcan := vsub_sub_vsub_cancel_right Q C A
        have hQ0 : Q -ᵥ C = 0 := by rw [← hcan]; exact h0
        exact vsub_eq_zero_iff_eq.mp hQ0
      have hR0 : s * inner (𝕜 := ℝ) (D -ᵥ B) n0 = 0 :=
        le_antisymm hR (by rw [← heq]; exact hL)
      have hs0' : s = 0 := by
        rcases mul_eq_zero.mp hR0 with hs | hd
        · exact hs
        · exact absurd hd hd0
      have hQB0 : Q -ᵥ B = 0 := by rw [hQs, hs0', zero_smul]
      have hQeqB : Q = B := vsub_eq_zero_iff_eq.mp hQB0
      exact hBC (hQeqB.symm.trans hQeqC)
    · exact mul_pos hapos hdpos

/-- Edge CD: A and B lie strictly on the same side of line CD. -/
private lemma same_side_CD
    (A B C D Q : EuclideanSpace ℝ (Fin 2))
    (hCD : C ≠ D)
    (hQAC : Q ∈ segment ℝ A C) (hQBD : Q ∈ segment ℝ B D)
    (n0 : EuclideanSpace ℝ (Fin 2))
    (hperp0 : inner (𝕜 := ℝ) (D -ᵥ C) n0 = 0)
    (ha0 : inner (𝕜 := ℝ) (A -ᵥ C) n0 ≠ 0)
    (hb0 : inner (𝕜 := ℝ) (B -ᵥ C) n0 ≠ 0) :
    0 < inner (𝕜 := ℝ) (A -ᵥ C) n0 * inner (𝕜 := ℝ) (B -ᵥ C) n0 := by
  rcases lt_or_gt_of_ne ha0 with haneg | hapos
  · rcases lt_or_gt_of_ne hb0 with hbneg | hbpos
    · exact mul_pos_of_neg_of_neg haneg hbneg
    · exfalso
      obtain ⟨t, ht0, ht1, hQt⟩ := vsub_of_mem_segment A C Q hQAC
      obtain ⟨s, hs0, hs1, hQs⟩ := vsub_of_mem_segment B D Q hQBD
      have hQC : Q -ᵥ C = (Q -ᵥ A) + (A -ᵥ C) :=
        (vsub_add_vsub_cancel Q A C).symm
      have hQin1 : inner (𝕜 := ℝ) (Q -ᵥ C) n0
          = (1 - t) * inner (𝕜 := ℝ) (A -ᵥ C) n0 := by
        have hCA : C -ᵥ A = -(A -ᵥ C) := by rw [← neg_vsub_eq_vsub_rev]
        rw [hQC, hQt, hCA, inner_add_left, real_inner_smul_left,
          inner_neg_left]
        ring
      have hDB : D -ᵥ B = (D -ᵥ C) + (C -ᵥ B) :=
        (vsub_add_vsub_cancel D C B).symm
      have hCB : C -ᵥ B = -(B -ᵥ C) := by rw [← neg_vsub_eq_vsub_rev]
      have hQB : Q -ᵥ C = (Q -ᵥ B) + (B -ᵥ C) :=
        (vsub_add_vsub_cancel Q B C).symm
      have hQin2 : inner (𝕜 := ℝ) (Q -ᵥ C) n0
          = (1 - s) * inner (𝕜 := ℝ) (B -ᵥ C) n0 := by
        rw [hQB, hQs, hDB, hCB, inner_add_left, real_inner_smul_left,
          inner_add_left, hperp0, inner_neg_left]
        ring
      have heq : (1 - t) * inner (𝕜 := ℝ) (A -ᵥ C) n0
          = (1 - s) * inner (𝕜 := ℝ) (B -ᵥ C) n0 := hQin1.symm.trans hQin2
      have ht1t : 0 ≤ 1 - t := by linarith
      have hs1s : 0 ≤ 1 - s := by linarith
      have hL : (1 - t) * inner (𝕜 := ℝ) (A -ᵥ C) n0 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht1t (le_of_lt haneg)
      have hR : 0 ≤ (1 - s) * inner (𝕜 := ℝ) (B -ᵥ C) n0 :=
        mul_nonneg hs1s (le_of_lt hbpos)
      have hL0 : (1 - t) * inner (𝕜 := ℝ) (A -ᵥ C) n0 = 0 :=
        le_antisymm hL (by rw [heq]; exact hR)
      have ht1' : t = 1 := by
        rcases mul_eq_zero.mp hL0 with ht | ha
        · have : (1 : ℝ) - t = 0 := ht
          linarith
        · exact absurd ha ha0
      have hQeqC : Q = C := by
        have hQC0 : Q -ᵥ A = C -ᵥ A := by rw [hQt, ht1', one_smul]
        have h0 : (Q -ᵥ A) - (C -ᵥ A) = 0 := sub_eq_zero.mpr hQC0
        have hcan := vsub_sub_vsub_cancel_right Q C A
        have hQ0 : Q -ᵥ C = 0 := by rw [← hcan]; exact h0
        exact vsub_eq_zero_iff_eq.mp hQ0
      have hR0 : (1 - s) * inner (𝕜 := ℝ) (B -ᵥ C) n0 = 0 :=
        le_antisymm (by rw [← heq]; exact hL) hR
      have hs1' : s = 1 := by
        rcases mul_eq_zero.mp hR0 with hs | hb
        · have : (1 : ℝ) - s = 0 := hs
          linarith
        · exact absurd hb hb0
      have hQeqD : Q = D := by
        have hQD : Q -ᵥ B = D -ᵥ B := by rw [hQs, hs1', one_smul]
        have h0 : (Q -ᵥ B) - (D -ᵥ B) = 0 := sub_eq_zero.mpr hQD
        have hcan := vsub_sub_vsub_cancel_right Q D B
        have hQ0 : Q -ᵥ D = 0 := by rw [← hcan]; exact h0
        exact vsub_eq_zero_iff_eq.mp hQ0
      exact hCD (hQeqC.symm.trans hQeqD)
  · rcases lt_or_gt_of_ne hb0 with hbneg | hbpos
    · exfalso
      obtain ⟨t, ht0, ht1, hQt⟩ := vsub_of_mem_segment A C Q hQAC
      obtain ⟨s, hs0, hs1, hQs⟩ := vsub_of_mem_segment B D Q hQBD
      have hQC : Q -ᵥ C = (Q -ᵥ A) + (A -ᵥ C) :=
        (vsub_add_vsub_cancel Q A C).symm
      have hQin1 : inner (𝕜 := ℝ) (Q -ᵥ C) n0
          = (1 - t) * inner (𝕜 := ℝ) (A -ᵥ C) n0 := by
        have hCA : C -ᵥ A = -(A -ᵥ C) := by rw [← neg_vsub_eq_vsub_rev]
        rw [hQC, hQt, hCA, inner_add_left, real_inner_smul_left,
          inner_neg_left]
        ring
      have hDB : D -ᵥ B = (D -ᵥ C) + (C -ᵥ B) :=
        (vsub_add_vsub_cancel D C B).symm
      have hCB : C -ᵥ B = -(B -ᵥ C) := by rw [← neg_vsub_eq_vsub_rev]
      have hQB : Q -ᵥ C = (Q -ᵥ B) + (B -ᵥ C) :=
        (vsub_add_vsub_cancel Q B C).symm
      have hQin2 : inner (𝕜 := ℝ) (Q -ᵥ C) n0
          = (1 - s) * inner (𝕜 := ℝ) (B -ᵥ C) n0 := by
        rw [hQB, hQs, hDB, hCB, inner_add_left, real_inner_smul_left,
          inner_add_left, hperp0, inner_neg_left]
        ring
      have heq : (1 - t) * inner (𝕜 := ℝ) (A -ᵥ C) n0
          = (1 - s) * inner (𝕜 := ℝ) (B -ᵥ C) n0 := hQin1.symm.trans hQin2
      have ht1t : 0 ≤ 1 - t := by linarith
      have hs1s : 0 ≤ 1 - s := by linarith
      have hL : 0 ≤ (1 - t) * inner (𝕜 := ℝ) (A -ᵥ C) n0 :=
        mul_nonneg ht1t (le_of_lt hapos)
      have hR : (1 - s) * inner (𝕜 := ℝ) (B -ᵥ C) n0 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hs1s (le_of_lt hbneg)
      have hL0 : (1 - t) * inner (𝕜 := ℝ) (A -ᵥ C) n0 = 0 :=
        le_antisymm (by rw [heq]; exact hR) hL
      have ht1' : t = 1 := by
        rcases mul_eq_zero.mp hL0 with ht | ha
        · have : (1 : ℝ) - t = 0 := ht
          linarith
        · exact absurd ha ha0
      have hQeqC : Q = C := by
        have hQC0 : Q -ᵥ A = C -ᵥ A := by rw [hQt, ht1', one_smul]
        have h0 : (Q -ᵥ A) - (C -ᵥ A) = 0 := sub_eq_zero.mpr hQC0
        have hcan := vsub_sub_vsub_cancel_right Q C A
        have hQ0 : Q -ᵥ C = 0 := by rw [← hcan]; exact h0
        exact vsub_eq_zero_iff_eq.mp hQ0
      have hR0 : (1 - s) * inner (𝕜 := ℝ) (B -ᵥ C) n0 = 0 :=
        le_antisymm hR (by rw [← heq]; exact hL)
      have hs1' : s = 1 := by
        rcases mul_eq_zero.mp hR0 with hs | hb
        · have : (1 : ℝ) - s = 0 := hs
          linarith
        · exact absurd hb hb0
      have hQeqD : Q = D := by
        have hQD : Q -ᵥ B = D -ᵥ B := by rw [hQs, hs1', one_smul]
        have h0 : (Q -ᵥ B) - (D -ᵥ B) = 0 := sub_eq_zero.mpr hQD
        have hcan := vsub_sub_vsub_cancel_right Q D B
        have hQ0 : Q -ᵥ D = 0 := by rw [← hcan]; exact h0
        exact vsub_eq_zero_iff_eq.mp hQ0
      exact hCD (hQeqC.symm.trans hQeqD)
    · exact mul_pos hapos hbpos

/-- Edge DA: B and C lie strictly on the same side of line DA. -/
private lemma same_side_DA
    (A B C D Q : EuclideanSpace ℝ (Fin 2))
    (hDA : D ≠ A)
    (hQAC : Q ∈ segment ℝ A C) (hQBD : Q ∈ segment ℝ B D)
    (n0 : EuclideanSpace ℝ (Fin 2))
    (hperp0 : inner (𝕜 := ℝ) (D -ᵥ A) n0 = 0)
    (hb0 : inner (𝕜 := ℝ) (B -ᵥ A) n0 ≠ 0)
    (hc0 : inner (𝕜 := ℝ) (C -ᵥ A) n0 ≠ 0) :
    0 < inner (𝕜 := ℝ) (B -ᵥ A) n0 * inner (𝕜 := ℝ) (C -ᵥ A) n0 := by
  rcases lt_or_gt_of_ne hb0 with hbneg | hbpos
  · rcases lt_or_gt_of_ne hc0 with hcneg | hcpos
    · exact mul_pos_of_neg_of_neg hbneg hcneg
    · exfalso
      obtain ⟨t, ht0, ht1, hQt⟩ := vsub_of_mem_segment A C Q hQAC
      obtain ⟨s, hs0, hs1, hQs⟩ := vsub_of_mem_segment B D Q hQBD
      have hQin1 : inner (𝕜 := ℝ) (Q -ᵥ A) n0
          = t * inner (𝕜 := ℝ) (C -ᵥ A) n0 := by
        rw [hQt, real_inner_smul_left]
      have hDB : D -ᵥ B = (D -ᵥ A) + (A -ᵥ B) :=
        (vsub_add_vsub_cancel D A B).symm
      have hAB : A -ᵥ B = -(B -ᵥ A) := by rw [← neg_vsub_eq_vsub_rev]
      have hQA : Q -ᵥ A = (Q -ᵥ B) + (B -ᵥ A) :=
        (vsub_add_vsub_cancel Q B A).symm
      have hQin2 : inner (𝕜 := ℝ) (Q -ᵥ A) n0
          = (1 - s) * inner (𝕜 := ℝ) (B -ᵥ A) n0 := by
        rw [hQA, hQs, hDB, hAB, inner_add_left, real_inner_smul_left,
          inner_add_left, hperp0, inner_neg_left]
        ring
      have heq : t * inner (𝕜 := ℝ) (C -ᵥ A) n0
          = (1 - s) * inner (𝕜 := ℝ) (B -ᵥ A) n0 := hQin1.symm.trans hQin2
      have hs1s : 0 ≤ 1 - s := by linarith
      have hL : 0 ≤ t * inner (𝕜 := ℝ) (C -ᵥ A) n0 :=
        mul_nonneg ht0 (le_of_lt hcpos)
      have hR : (1 - s) * inner (𝕜 := ℝ) (B -ᵥ A) n0 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hs1s (le_of_lt hbneg)
      have hL0 : t * inner (𝕜 := ℝ) (C -ᵥ A) n0 = 0 :=
        le_antisymm (by rw [heq]; exact hR) hL
      have ht0' : t = 0 := by
        rcases mul_eq_zero.mp hL0 with ht | hc
        · exact ht
        · exact absurd hc hc0
      have hQA0 : Q -ᵥ A = 0 := by rw [hQt, ht0', zero_smul]
      have hQeqA : Q = A := vsub_eq_zero_iff_eq.mp hQA0
      have hR0 : (1 - s) * inner (𝕜 := ℝ) (B -ᵥ A) n0 = 0 :=
        le_antisymm hR (by rw [← heq]; exact hL)
      have hs1' : s = 1 := by
        rcases mul_eq_zero.mp hR0 with hs | hb
        · have : (1 : ℝ) - s = 0 := hs
          linarith
        · exact absurd hb hb0
      have hQeqD : Q = D := by
        have hQD : Q -ᵥ B = D -ᵥ B := by rw [hQs, hs1', one_smul]
        have h0 : (Q -ᵥ B) - (D -ᵥ B) = 0 := sub_eq_zero.mpr hQD
        have hcan := vsub_sub_vsub_cancel_right Q D B
        have hQ0 : Q -ᵥ D = 0 := by rw [← hcan]; exact h0
        exact vsub_eq_zero_iff_eq.mp hQ0
      exact hDA (hQeqD.symm.trans hQeqA)
  · rcases lt_or_gt_of_ne hc0 with hcneg | hcpos
    · exfalso
      obtain ⟨t, ht0, ht1, hQt⟩ := vsub_of_mem_segment A C Q hQAC
      obtain ⟨s, hs0, hs1, hQs⟩ := vsub_of_mem_segment B D Q hQBD
      have hQin1 : inner (𝕜 := ℝ) (Q -ᵥ A) n0
          = t * inner (𝕜 := ℝ) (C -ᵥ A) n0 := by
        rw [hQt, real_inner_smul_left]
      have hDB : D -ᵥ B = (D -ᵥ A) + (A -ᵥ B) :=
        (vsub_add_vsub_cancel D A B).symm
      have hAB : A -ᵥ B = -(B -ᵥ A) := by rw [← neg_vsub_eq_vsub_rev]
      have hQA : Q -ᵥ A = (Q -ᵥ B) + (B -ᵥ A) :=
        (vsub_add_vsub_cancel Q B A).symm
      have hQin2 : inner (𝕜 := ℝ) (Q -ᵥ A) n0
          = (1 - s) * inner (𝕜 := ℝ) (B -ᵥ A) n0 := by
        rw [hQA, hQs, hDB, hAB, inner_add_left, real_inner_smul_left,
          inner_add_left, hperp0, inner_neg_left]
        ring
      have heq : t * inner (𝕜 := ℝ) (C -ᵥ A) n0
          = (1 - s) * inner (𝕜 := ℝ) (B -ᵥ A) n0 := hQin1.symm.trans hQin2
      have hs1s : 0 ≤ 1 - s := by linarith
      have hL : t * inner (𝕜 := ℝ) (C -ᵥ A) n0 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht0 (le_of_lt hcneg)
      have hR : 0 ≤ (1 - s) * inner (𝕜 := ℝ) (B -ᵥ A) n0 :=
        mul_nonneg hs1s (le_of_lt hbpos)
      have hL0 : t * inner (𝕜 := ℝ) (C -ᵥ A) n0 = 0 :=
        le_antisymm hL (by rw [heq]; exact hR)
      have ht0' : t = 0 := by
        rcases mul_eq_zero.mp hL0 with ht | hc
        · exact ht
        · exact absurd hc hc0
      have hQA0 : Q -ᵥ A = 0 := by rw [hQt, ht0', zero_smul]
      have hQeqA : Q = A := vsub_eq_zero_iff_eq.mp hQA0
      have hR0 : (1 - s) * inner (𝕜 := ℝ) (B -ᵥ A) n0 = 0 :=
        le_antisymm (by rw [← heq]; exact hL) hR
      have hs1' : s = 1 := by
        rcases mul_eq_zero.mp hR0 with hs | hb
        · have : (1 : ℝ) - s = 0 := hs
          linarith
        · exact absurd hb hb0
      have hQeqD : Q = D := by
        have hQD : Q -ᵥ B = D -ᵥ B := by rw [hQs, hs1', one_smul]
        have h0 : (Q -ᵥ B) - (D -ᵥ B) = 0 := sub_eq_zero.mpr hQD
        have hcan := vsub_sub_vsub_cancel_right Q D B
        have hQ0 : Q -ᵥ D = 0 := by rw [← hcan]; exact h0
        exact vsub_eq_zero_iff_eq.mp hQ0
      exact hDA (hQeqD.symm.trans hQeqA)
    · exact mul_pos hbpos hcpos

/-- Diagonal AC: B and D lie strictly on opposite sides of line AC. -/
private lemma opp_side_AC
    (A B C D Q : EuclideanSpace ℝ (Fin 2))
    (hQAC : Q ∈ segment ℝ A C) (hQBD : Q ∈ segment ℝ B D)
    (n0 : EuclideanSpace ℝ (Fin 2))
    (hperp0 : inner (𝕜 := ℝ) (C -ᵥ A) n0 = 0)
    (hb0 : inner (𝕜 := ℝ) (B -ᵥ A) n0 ≠ 0)
    (hd0 : inner (𝕜 := ℝ) (D -ᵥ A) n0 ≠ 0) :
    inner (𝕜 := ℝ) (B -ᵥ A) n0 * inner (𝕜 := ℝ) (D -ᵥ A) n0 < 0 := by
  rcases lt_or_gt_of_ne hb0 with hbneg | hbpos
  · rcases lt_or_gt_of_ne hd0 with hdneg | hdpos
    · exfalso
      obtain ⟨t, ht0, ht1, hQt⟩ := vsub_of_mem_segment A C Q hQAC
      obtain ⟨s, hs0, hs1, hQs⟩ := vsub_of_mem_segment B D Q hQBD
      have hQ0 : inner (𝕜 := ℝ) (Q -ᵥ A) n0 = 0 := by
        rw [hQt, real_inner_smul_left, hperp0, mul_zero]
      have hDB : D -ᵥ B = (D -ᵥ A) - (B -ᵥ A) := by
        rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub]
        module
      have hQA : Q -ᵥ A = (Q -ᵥ B) + (B -ᵥ A) :=
        (vsub_add_vsub_cancel Q B A).symm
      have hQin : inner (𝕜 := ℝ) (Q -ᵥ A) n0
          = (1 - s) * inner (𝕜 := ℝ) (B -ᵥ A) n0
            + s * inner (𝕜 := ℝ) (D -ᵥ A) n0 := by
        rw [hQA, hQs, hDB]
        rw [inner_add_left, real_inner_smul_left, inner_sub_left]
        ring
      have hs1s : 0 ≤ 1 - s := by linarith
      have hneg : inner (𝕜 := ℝ) (Q -ᵥ A) n0 < 0 := by
        rw [hQin]
        rcases eq_or_ne s 1 with hs1eq | hs1ne
        · subst hs1eq
          simp only [sub_self, zero_mul, zero_add, one_mul]
          exact hdneg
        · have hslt : s < 1 := lt_of_le_of_ne hs1 hs1ne
          have h1s : 0 < 1 - s := sub_pos.mpr hslt
          have h1 : (1 - s) * inner (𝕜 := ℝ) (B -ᵥ A) n0 < 0 :=
            mul_neg_of_pos_of_neg h1s hbneg
          have h2 : s * inner (𝕜 := ℝ) (D -ᵥ A) n0 ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hs0 (le_of_lt hdneg)
          linarith
      linarith
    · exact mul_neg_of_neg_of_pos hbneg hdpos
  · rcases lt_or_gt_of_ne hd0 with hdneg | hdpos
    · exact mul_neg_of_pos_of_neg hbpos hdneg
    · exfalso
      obtain ⟨t, ht0, ht1, hQt⟩ := vsub_of_mem_segment A C Q hQAC
      obtain ⟨s, hs0, hs1, hQs⟩ := vsub_of_mem_segment B D Q hQBD
      have hQ0 : inner (𝕜 := ℝ) (Q -ᵥ A) n0 = 0 := by
        rw [hQt, real_inner_smul_left, hperp0, mul_zero]
      have hDB : D -ᵥ B = (D -ᵥ A) - (B -ᵥ A) := by
        rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub]
        module
      have hQA : Q -ᵥ A = (Q -ᵥ B) + (B -ᵥ A) :=
        (vsub_add_vsub_cancel Q B A).symm
      have hQin : inner (𝕜 := ℝ) (Q -ᵥ A) n0
          = (1 - s) * inner (𝕜 := ℝ) (B -ᵥ A) n0
            + s * inner (𝕜 := ℝ) (D -ᵥ A) n0 := by
        rw [hQA, hQs, hDB]
        rw [inner_add_left, real_inner_smul_left, inner_sub_left]
        ring
      have hs1s : 0 ≤ 1 - s := by linarith
      have hpos : 0 < inner (𝕜 := ℝ) (Q -ᵥ A) n0 := by
        rw [hQin]
        rcases eq_or_ne s 1 with hs1eq | hs1ne
        · subst hs1eq
          simp only [sub_self, zero_mul, zero_add, one_mul]
          exact hdpos
        · have hslt : s < 1 := lt_of_le_of_ne hs1 hs1ne
          have h1s : 0 < 1 - s := sub_pos.mpr hslt
          have h1 : 0 < (1 - s) * inner (𝕜 := ℝ) (B -ᵥ A) n0 :=
            mul_pos h1s hbpos
          have h2 : 0 ≤ s * inner (𝕜 := ℝ) (D -ᵥ A) n0 :=
            mul_nonneg hs0 (le_of_lt hdpos)
          linarith
      linarith

/-- Diagonal BD: A and C lie strictly on opposite sides of line BD. -/
private lemma opp_side_BD
    (A B C D Q : EuclideanSpace ℝ (Fin 2))
    (hQAC : Q ∈ segment ℝ A C) (hQBD : Q ∈ segment ℝ B D)
    (n0 : EuclideanSpace ℝ (Fin 2))
    (hperp0 : inner (𝕜 := ℝ) (D -ᵥ B) n0 = 0)
    (ha0 : inner (𝕜 := ℝ) (A -ᵥ B) n0 ≠ 0)
    (hc0 : inner (𝕜 := ℝ) (C -ᵥ B) n0 ≠ 0) :
    inner (𝕜 := ℝ) (A -ᵥ B) n0 * inner (𝕜 := ℝ) (C -ᵥ B) n0 < 0 := by
  rcases lt_or_gt_of_ne ha0 with haneg | hapos
  · rcases lt_or_gt_of_ne hc0 with hcneg | hcpos
    · exfalso
      obtain ⟨t, ht0, ht1, hQt⟩ := vsub_of_mem_segment A C Q hQAC
      obtain ⟨s, hs0, hs1, hQs⟩ := vsub_of_mem_segment B D Q hQBD
      have hQ0 : inner (𝕜 := ℝ) (Q -ᵥ B) n0 = 0 := by
        rw [hQs, real_inner_smul_left]
        have hDB0 : inner (𝕜 := ℝ) (D -ᵥ B) n0 = 0 := hperp0
        rw [hDB0, mul_zero]
      have hCA : C -ᵥ A = (C -ᵥ B) + (B -ᵥ A) :=
        (vsub_add_vsub_cancel C B A).symm
      have hBA : B -ᵥ A = -(A -ᵥ B) := by rw [← neg_vsub_eq_vsub_rev]
      have hQB : Q -ᵥ B = (Q -ᵥ A) + (A -ᵥ B) :=
        (vsub_add_vsub_cancel Q A B).symm
      have hQin : inner (𝕜 := ℝ) (Q -ᵥ B) n0
          = (1 - t) * inner (𝕜 := ℝ) (A -ᵥ B) n0
            + t * inner (𝕜 := ℝ) (C -ᵥ B) n0 := by
        rw [hQB, hQt, hCA, hBA, inner_add_left, real_inner_smul_left,
          inner_add_left, inner_neg_left]
        ring
      have ht1t : 0 ≤ 1 - t := by linarith
      have hneg : inner (𝕜 := ℝ) (Q -ᵥ B) n0 < 0 := by
        rw [hQin]
        rcases eq_or_ne t 1 with ht1eq | ht1ne
        · subst ht1eq
          simp only [sub_self, zero_mul, zero_add, one_mul]
          exact hcneg
        · have htlt : t < 1 := lt_of_le_of_ne ht1 ht1ne
          have h1t : 0 < 1 - t := sub_pos.mpr htlt
          have h1 : (1 - t) * inner (𝕜 := ℝ) (A -ᵥ B) n0 < 0 :=
            mul_neg_of_pos_of_neg h1t haneg
          have h2 : t * inner (𝕜 := ℝ) (C -ᵥ B) n0 ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos ht0 (le_of_lt hcneg)
          linarith
      linarith
    · exact mul_neg_of_neg_of_pos haneg hcpos
  · rcases lt_or_gt_of_ne hc0 with hcneg | hcpos
    · exact mul_neg_of_pos_of_neg hapos hcneg
    · exfalso
      obtain ⟨t, ht0, ht1, hQt⟩ := vsub_of_mem_segment A C Q hQAC
      obtain ⟨s, hs0, hs1, hQs⟩ := vsub_of_mem_segment B D Q hQBD
      have hQ0 : inner (𝕜 := ℝ) (Q -ᵥ B) n0 = 0 := by
        rw [hQs, real_inner_smul_left]
        have hDB0 : inner (𝕜 := ℝ) (D -ᵥ B) n0 = 0 := hperp0
        rw [hDB0, mul_zero]
      have hCA : C -ᵥ A = (C -ᵥ B) + (B -ᵥ A) :=
        (vsub_add_vsub_cancel C B A).symm
      have hBA : B -ᵥ A = -(A -ᵥ B) := by rw [← neg_vsub_eq_vsub_rev]
      have hQB : Q -ᵥ B = (Q -ᵥ A) + (A -ᵥ B) :=
        (vsub_add_vsub_cancel Q A B).symm
      have hQin : inner (𝕜 := ℝ) (Q -ᵥ B) n0
          = (1 - t) * inner (𝕜 := ℝ) (A -ᵥ B) n0
            + t * inner (𝕜 := ℝ) (C -ᵥ B) n0 := by
        rw [hQB, hQt, hCA, hBA, inner_add_left, real_inner_smul_left,
          inner_add_left, inner_neg_left]
        ring
      have ht1t : 0 ≤ 1 - t := by linarith
      have hpos : 0 < inner (𝕜 := ℝ) (Q -ᵥ B) n0 := by
        rw [hQin]
        rcases eq_or_ne t 1 with ht1eq | ht1ne
        · subst ht1eq
          simp only [sub_self, zero_mul, zero_add, one_mul]
          exact hcpos
        · have htlt : t < 1 := lt_of_le_of_ne ht1 ht1ne
          have h1t : 0 < 1 - t := sub_pos.mpr htlt
          have h1 : 0 < (1 - t) * inner (𝕜 := ℝ) (A -ᵥ B) n0 :=
            mul_pos h1t hapos
          have h2 : 0 ≤ t * inner (𝕜 := ℝ) (C -ᵥ B) n0 :=
            mul_nonneg ht0 (le_of_lt hcpos)
          linarith
      linarith

/-- **Japanese theorem for concyclic quadrilaterals.** Let $A, B, C, D$ be pairwise distinct
points of the Euclidean plane $\mathbb{R}^2$ lying on a circle of positive radius, such that the
diagonals $AC$ and $BD$, as closed segments, intersect; so $ABCD$ is a convex cyclic
quadrilateral. Let $r_1, r_2, r_3, r_4 > 0$, and suppose that for each of the triangles $ABC$,
$CDA$, $BCD$ and $DAB$ there is a closed disc of radius $r_1$, $r_2$, $r_3$ and $r_4$
respectively that is contained in the closed triangle and whose boundary circle meets each of
the three closed sides of the triangle; so $r_1, r_2$ are the inradii of the triangles $ABC$,
$CDA$ of one triangulation and $r_3, r_4$ those of the triangles $BCD$, $DAB$ of the other.
Then $r_1 + r_2 = r_3 + r_4$.

Proves `Wanted` entry `japanese_theorem_concyclic_quadrilaterals`.

Source: https://en.wikipedia.org/wiki/Japanese_theorem_for_concyclic_quadrilaterals
(statement japanese-quads-s1).
-/
theorem japanese_theorem_concyclic_quadrilaterals :
    ∀ (A B C D : EuclideanSpace ℝ (Fin 2)) (r1 r2 r3 r4 : ℝ),
      (∃ O : EuclideanSpace ℝ (Fin 2), ∃ R : ℝ, 0 < R ∧
        A ∈ Metric.sphere O R ∧ B ∈ Metric.sphere O R ∧
        C ∈ Metric.sphere O R ∧ D ∈ Metric.sphere O R) →
      (segment ℝ A C ∩ segment ℝ B D).Nonempty →
      A ≠ B → B ≠ C → C ≠ D → D ≠ A → A ≠ C → B ≠ D →
      0 < r1 → 0 < r2 → 0 < r3 → 0 < r4 →
      (∃ I1 : EuclideanSpace ℝ (Fin 2),
        Metric.closedBall I1 r1 ⊆ convexHull ℝ {A, B, C} ∧
        (segment ℝ A B ∩ Metric.sphere I1 r1).Nonempty ∧
        (segment ℝ B C ∩ Metric.sphere I1 r1).Nonempty ∧
        (segment ℝ C A ∩ Metric.sphere I1 r1).Nonempty) →
      (∃ I2 : EuclideanSpace ℝ (Fin 2),
        Metric.closedBall I2 r2 ⊆ convexHull ℝ {C, D, A} ∧
        (segment ℝ C D ∩ Metric.sphere I2 r2).Nonempty ∧
        (segment ℝ D A ∩ Metric.sphere I2 r2).Nonempty ∧
        (segment ℝ A C ∩ Metric.sphere I2 r2).Nonempty) →
      (∃ I3 : EuclideanSpace ℝ (Fin 2),
        Metric.closedBall I3 r3 ⊆ convexHull ℝ {B, C, D} ∧
        (segment ℝ B C ∩ Metric.sphere I3 r3).Nonempty ∧
        (segment ℝ C D ∩ Metric.sphere I3 r3).Nonempty ∧
        (segment ℝ D B ∩ Metric.sphere I3 r3).Nonempty) →
      (∃ I4 : EuclideanSpace ℝ (Fin 2),
        Metric.closedBall I4 r4 ⊆ convexHull ℝ {D, A, B} ∧
        (segment ℝ D A ∩ Metric.sphere I4 r4).Nonempty ∧
        (segment ℝ A B ∩ Metric.sphere I4 r4).Nonempty ∧
        (segment ℝ B D ∩ Metric.sphere I4 r4).Nonempty) →
      r1 + r2 = r3 + r4 := by
  intro A B C D r1 r2 r3 r4 hconc hseg hAB hBC hCD hDA hAC hBD
    hr1 hr2 hr3 hr4 hI1 hI2 hI3 hI4
  obtain ⟨O, R, hR, hA, hB, hC, hD⟩ := hconc
  have hcos := cospherical_of_mem_sphere O R A B C D hA hB hC hD
  have hfin : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hTri1 : ¬Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hai : AffineIndependent ℝ ![A, B, C] :=
      hcos.affineIndependent_of_mem_of_ne (by simp) (by simp) (by simp)
        hAB hAC hBC
    exact affineIndependent_iff_not_collinear_set.mp hai
  have hTri2 : ¬Collinear ℝ ({C, D, A} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hai : AffineIndependent ℝ ![C, D, A] :=
      hcos.affineIndependent_of_mem_of_ne (by simp) (by simp) (by simp)
        hCD hAC.symm hDA
    exact affineIndependent_iff_not_collinear_set.mp hai
  have hTri3 : ¬Collinear ℝ ({B, C, D} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hai : AffineIndependent ℝ ![B, C, D] :=
      hcos.affineIndependent_of_mem_of_ne (by simp) (by simp) (by simp)
        hBC hBD hCD
    exact affineIndependent_iff_not_collinear_set.mp hai
  have hTri4 : ¬Collinear ℝ ({D, A, B} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hai : AffineIndependent ℝ ![D, A, B] :=
      hcos.affineIndependent_of_mem_of_ne (by simp) (by simp) (by simp)
        hDA hBD.symm hAB
    exact affineIndependent_iff_not_collinear_set.mp hai
  obtain ⟨Q, hQ⟩ := hseg
  have hQAC : Q ∈ segment ℝ A C := hQ.1
  have hQBD : Q ∈ segment ℝ B D := hQ.2
  obtain ⟨I1, hsub1, ht1AB, ht1BC, ht1CA⟩ := hI1
  obtain ⟨I2, hsub2, ht2CD, ht2DA, ht2AC⟩ := hI2
  obtain ⟨I3, hsub3, ht3BC, ht3CD, ht3DB⟩ := hI3
  obtain ⟨I4, hsub4, ht4DA, ht4AB, ht4BD⟩ := hI4
  have hBA0 : (B -ᵥ A) ≠ 0 := vsub_ne_zero.mpr hAB.symm
  have hCB0 : (C -ᵥ B) ≠ 0 := vsub_ne_zero.mpr hBC.symm
  have hDC0 : (D -ᵥ C) ≠ 0 := vsub_ne_zero.mpr hCD.symm
  have hDA0 : (D -ᵥ A) ≠ 0 := vsub_ne_zero.mpr hDA
  have hCA0 : (C -ᵥ A) ≠ 0 := vsub_ne_zero.mpr hAC.symm
  have hDB0 : (D -ᵥ B) ≠ 0 := vsub_ne_zero.mpr hBD.symm
  obtain ⟨nAB0, hnAB0, hpAB0⟩ := exists_unit_perp (B -ᵥ A) hBA0
  obtain ⟨nBC0, hnBC0, hpBC0⟩ := exists_unit_perp (C -ᵥ B) hCB0
  obtain ⟨nCD0, hnCD0, hpCD0⟩ := exists_unit_perp (D -ᵥ C) hDC0
  obtain ⟨nDA0, hnDA0, hpDA0⟩ := exists_unit_perp (D -ᵥ A) hDA0
  obtain ⟨nAC0, hnAC0, hpAC0⟩ := exists_unit_perp (C -ᵥ A) hCA0
  obtain ⟨nBD0, hnBD0, hpBD0⟩ := exists_unit_perp (D -ᵥ B) hDB0
  have hTriCAB : ¬Collinear ℝ ({C, A, B} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hai : AffineIndependent ℝ ![C, A, B] :=
      hcos.affineIndependent_of_mem_of_ne (by simp) (by simp) (by simp)
        hAC.symm hBC.symm hAB
    exact affineIndependent_iff_not_collinear_set.mp hai
  have hTriDBC : ¬Collinear ℝ ({D, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hai : AffineIndependent ℝ ![D, B, C] :=
      hcos.affineIndependent_of_mem_of_ne (by simp) (by simp) (by simp)
        hBD.symm hCD.symm hBC
    exact affineIndependent_iff_not_collinear_set.mp hai
  have hTriACD : ¬Collinear ℝ ({A, C, D} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hai : AffineIndependent ℝ ![A, C, D] :=
      hcos.affineIndependent_of_mem_of_ne (by simp) (by simp) (by simp)
        hAC hDA.symm hCD
    exact affineIndependent_iff_not_collinear_set.mp hai
  have hTriBAD : ¬Collinear ℝ ({B, A, D} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hai : AffineIndependent ℝ ![B, A, D] :=
      hcos.affineIndependent_of_mem_of_ne (by simp) (by simp) (by simp)
        hAB.symm hBD hDA.symm
    exact affineIndependent_iff_not_collinear_set.mp hai
  have hTriCAD : ¬Collinear ℝ ({C, A, D} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hai : AffineIndependent ℝ ![C, A, D] :=
      hcos.affineIndependent_of_mem_of_ne (by simp) (by simp) (by simp)
        hAC.symm hCD hDA.symm
    exact affineIndependent_iff_not_collinear_set.mp hai
  have hTriBAC : ¬Collinear ℝ ({B, A, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hai : AffineIndependent ℝ ![B, A, C] :=
      hcos.affineIndependent_of_mem_of_ne (by simp) (by simp) (by simp)
        hAB.symm hBC hAC
    exact affineIndependent_iff_not_collinear_set.mp hai
  have hTriDAC : ¬Collinear ℝ ({D, A, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hai : AffineIndependent ℝ ![D, A, C] :=
      hcos.affineIndependent_of_mem_of_ne (by simp) (by simp) (by simp)
        hDA hCD.symm hAC
    exact affineIndependent_iff_not_collinear_set.mp hai
  have hTriABD : ¬Collinear ℝ ({A, B, D} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hai : AffineIndependent ℝ ![A, B, D] :=
      hcos.affineIndependent_of_mem_of_ne (by simp) (by simp) (by simp)
        hAB hDA.symm hBD
    exact affineIndependent_iff_not_collinear_set.mp hai
  have hTriCBD : ¬Collinear ℝ ({C, B, D} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hai : AffineIndependent ℝ ![C, B, D] :=
      hcos.affineIndependent_of_mem_of_ne (by simp) (by simp) (by simp)
        hBC.symm hCD hBD
    exact affineIndependent_iff_not_collinear_set.mp hai
  have hCAB0 : inner (𝕜 := ℝ) (C -ᵥ A) nAB0 ≠ 0 :=
    inner_ne_zero_of_not_collinear C A B hTriCAB hAB nAB0 hnAB0 hpAB0
  have hDAB0 : inner (𝕜 := ℝ) (D -ᵥ A) nAB0 ≠ 0 :=
    inner_ne_zero_of_not_collinear D A B hTri4 hAB nAB0 hnAB0 hpAB0
  have hABC0 : inner (𝕜 := ℝ) (A -ᵥ B) nBC0 ≠ 0 :=
    inner_ne_zero_of_not_collinear A B C hTri1 hBC nBC0 hnBC0 hpBC0
  have hDBC0 : inner (𝕜 := ℝ) (D -ᵥ B) nBC0 ≠ 0 :=
    inner_ne_zero_of_not_collinear D B C hTriDBC hBC nBC0 hnBC0 hpBC0
  have hACD0 : inner (𝕜 := ℝ) (A -ᵥ C) nCD0 ≠ 0 :=
    inner_ne_zero_of_not_collinear A C D hTriACD hCD nCD0 hnCD0 hpCD0
  have hBCD0 : inner (𝕜 := ℝ) (B -ᵥ C) nCD0 ≠ 0 :=
    inner_ne_zero_of_not_collinear B C D hTri3 hCD nCD0 hnCD0 hpCD0
  have hBAD0 : inner (𝕜 := ℝ) (B -ᵥ A) nDA0 ≠ 0 :=
    inner_ne_zero_of_not_collinear B A D hTriBAD hDA.symm nDA0 hnDA0 hpDA0
  have hCAD0 : inner (𝕜 := ℝ) (C -ᵥ A) nDA0 ≠ 0 :=
    inner_ne_zero_of_not_collinear C A D hTriCAD hDA.symm nDA0 hnDA0 hpDA0
  have hBAC0 : inner (𝕜 := ℝ) (B -ᵥ A) nAC0 ≠ 0 :=
    inner_ne_zero_of_not_collinear B A C hTriBAC hAC nAC0 hnAC0 hpAC0
  have hDAC0 : inner (𝕜 := ℝ) (D -ᵥ A) nAC0 ≠ 0 :=
    inner_ne_zero_of_not_collinear D A C hTriDAC hAC nAC0 hnAC0 hpAC0
  have hABD0 : inner (𝕜 := ℝ) (A -ᵥ B) nBD0 ≠ 0 :=
    inner_ne_zero_of_not_collinear A B D hTriABD hBD nBD0 hnBD0 hpBD0
  have hCBD0 : inner (𝕜 := ℝ) (C -ᵥ B) nBD0 ≠ 0 :=
    inner_ne_zero_of_not_collinear C B D hTriCBD hBD nBD0 hnBD0 hpBD0
  have hABsame := same_side_AB A B C D Q hAB hQAC hQBD nAB0 hpAB0 hCAB0 hDAB0
  have hBCsame := same_side_BC A B C D Q hBC hQAC hQBD nBC0 hpBC0 hABC0 hDBC0
  have hCDsame := same_side_CD A B C D Q hCD hQAC hQBD nCD0 hpCD0 hACD0 hBCD0
  have hDAsame := same_side_DA A B C D Q hDA hQAC hQBD nDA0 hpDA0 hBAD0 hCAD0
  have hACopp := opp_side_AC A B C D Q hQAC hQBD nAC0 hpAC0 hBAC0 hDAC0
  have hBDopp := opp_side_BD A B C D Q hQAC hQBD nBD0 hpBD0 hABD0 hCBD0
  obtain ⟨nAB, hnAB, hpAB, hinABC, hinABD⟩ :
      ∃ nAB : EuclideanSpace ℝ (Fin 2), ‖nAB‖ = 1 ∧
        inner (𝕜 := ℝ) (B -ᵥ A) nAB = 0 ∧
        0 < inner (𝕜 := ℝ) (C -ᵥ A) nAB ∧
        0 < inner (𝕜 := ℝ) (D -ᵥ A) nAB := by
    rcases lt_or_gt_of_ne hCAB0 with hcneg | hcpos
    · have hdneg : inner (𝕜 := ℝ) (D -ᵥ A) nAB0 < 0 := by
        rcases lt_or_gt_of_ne hDAB0 with hdneg | hdpos
        · exact hdneg
        · exfalso
          have hcon := mul_neg_of_neg_of_pos hcneg hdpos
          linarith
      refine ⟨-nAB0, ?_, ?_, ?_, ?_⟩
      · rw [norm_neg, hnAB0]
      · rw [inner_neg_right, hpAB0, neg_zero]
      · rw [inner_neg_right]; exact neg_pos.mpr hcneg
      · rw [inner_neg_right]; exact neg_pos.mpr hdneg
    · have hdpos : 0 < inner (𝕜 := ℝ) (D -ᵥ A) nAB0 := by
        rcases lt_or_gt_of_ne hDAB0 with hdneg | hdpos
        · exfalso
          have hcon := mul_neg_of_pos_of_neg hcpos hdneg
          linarith
        · exact hdpos
      exact ⟨nAB0, hnAB0, hpAB0, hcpos, hdpos⟩
  obtain ⟨nBC, hnBC, hpBC, hinBCA, hinBCD⟩ :
      ∃ nBC : EuclideanSpace ℝ (Fin 2), ‖nBC‖ = 1 ∧
        inner (𝕜 := ℝ) (C -ᵥ B) nBC = 0 ∧
        0 < inner (𝕜 := ℝ) (A -ᵥ B) nBC ∧
        0 < inner (𝕜 := ℝ) (D -ᵥ B) nBC := by
    rcases lt_or_gt_of_ne hABC0 with haneg | hapos
    · have hdneg : inner (𝕜 := ℝ) (D -ᵥ B) nBC0 < 0 := by
        rcases lt_or_gt_of_ne hDBC0 with hdneg | hdpos
        · exact hdneg
        · exfalso
          have hcon := mul_neg_of_neg_of_pos haneg hdpos
          linarith
      refine ⟨-nBC0, ?_, ?_, ?_, ?_⟩
      · rw [norm_neg, hnBC0]
      · rw [inner_neg_right, hpBC0, neg_zero]
      · rw [inner_neg_right]; exact neg_pos.mpr haneg
      · rw [inner_neg_right]; exact neg_pos.mpr hdneg
    · have hdpos : 0 < inner (𝕜 := ℝ) (D -ᵥ B) nBC0 := by
        rcases lt_or_gt_of_ne hDBC0 with hdneg | hdpos
        · exfalso
          have hcon := mul_neg_of_pos_of_neg hapos hdneg
          linarith
        · exact hdpos
      exact ⟨nBC0, hnBC0, hpBC0, hapos, hdpos⟩
  obtain ⟨nCD, hnCD, hpCD, hinCDA, hinCDB⟩ :
      ∃ nCD : EuclideanSpace ℝ (Fin 2), ‖nCD‖ = 1 ∧
        inner (𝕜 := ℝ) (D -ᵥ C) nCD = 0 ∧
        0 < inner (𝕜 := ℝ) (A -ᵥ C) nCD ∧
        0 < inner (𝕜 := ℝ) (B -ᵥ C) nCD := by
    rcases lt_or_gt_of_ne hACD0 with haneg | hapos
    · have hbneg : inner (𝕜 := ℝ) (B -ᵥ C) nCD0 < 0 := by
        rcases lt_or_gt_of_ne hBCD0 with hbneg | hbpos
        · exact hbneg
        · exfalso
          have hcon := mul_neg_of_neg_of_pos haneg hbpos
          linarith
      refine ⟨-nCD0, ?_, ?_, ?_, ?_⟩
      · rw [norm_neg, hnCD0]
      · rw [inner_neg_right, hpCD0, neg_zero]
      · rw [inner_neg_right]; exact neg_pos.mpr haneg
      · rw [inner_neg_right]; exact neg_pos.mpr hbneg
    · have hbpos : 0 < inner (𝕜 := ℝ) (B -ᵥ C) nCD0 := by
        rcases lt_or_gt_of_ne hBCD0 with hbneg | hbpos
        · exfalso
          have hcon := mul_neg_of_pos_of_neg hapos hbneg
          linarith
        · exact hbpos
      exact ⟨nCD0, hnCD0, hpCD0, hapos, hbpos⟩
  obtain ⟨nDA, hnDA, hpDA, hinDAB, hinDAC⟩ :
      ∃ nDA : EuclideanSpace ℝ (Fin 2), ‖nDA‖ = 1 ∧
        inner (𝕜 := ℝ) (D -ᵥ A) nDA = 0 ∧
        0 < inner (𝕜 := ℝ) (B -ᵥ A) nDA ∧
        0 < inner (𝕜 := ℝ) (C -ᵥ A) nDA := by
    rcases lt_or_gt_of_ne hBAD0 with hbneg | hbpos
    · have hcneg : inner (𝕜 := ℝ) (C -ᵥ A) nDA0 < 0 := by
        rcases lt_or_gt_of_ne hCAD0 with hcneg | hcpos
        · exact hcneg
        · exfalso
          have hcon := mul_neg_of_neg_of_pos hbneg hcpos
          linarith
      refine ⟨-nDA0, ?_, ?_, ?_, ?_⟩
      · rw [norm_neg, hnDA0]
      · rw [inner_neg_right, hpDA0, neg_zero]
      · rw [inner_neg_right]; exact neg_pos.mpr hbneg
      · rw [inner_neg_right]; exact neg_pos.mpr hcneg
    · have hcpos : 0 < inner (𝕜 := ℝ) (C -ᵥ A) nDA0 := by
        rcases lt_or_gt_of_ne hCAD0 with hcneg | hcpos
        · exfalso
          have hcon := mul_neg_of_pos_of_neg hbpos hcneg
          linarith
        · exact hcpos
      exact ⟨nDA0, hnDA0, hpDA0, hbpos, hcpos⟩
  obtain ⟨nACB, nACD, hnACB, hpACB, hinACB, hnACD, hpACD, hinACD, hACopp'⟩ :
      ∃ nACB nACD : EuclideanSpace ℝ (Fin 2), ‖nACB‖ = 1 ∧
        inner (𝕜 := ℝ) (C -ᵥ A) nACB = 0 ∧
        0 < inner (𝕜 := ℝ) (B -ᵥ A) nACB ∧ ‖nACD‖ = 1 ∧
        inner (𝕜 := ℝ) (C -ᵥ A) nACD = 0 ∧
        0 < inner (𝕜 := ℝ) (D -ᵥ A) nACD ∧ nACD = -nACB := by
    rcases lt_or_gt_of_ne hBAC0 with hbneg | hbpos
    · have hdpos : 0 < inner (𝕜 := ℝ) (D -ᵥ A) nAC0 := by
        rcases lt_or_gt_of_ne hDAC0 with hdneg | hdpos
        · exfalso
          have hcon := mul_pos_of_neg_of_neg hbneg hdneg
          linarith
        · exact hdpos
      refine ⟨-nAC0, nAC0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [norm_neg, hnAC0]
      · rw [inner_neg_right, hpAC0, neg_zero]
      · rw [inner_neg_right]; exact neg_pos.mpr hbneg
      · exact hnAC0
      · exact hpAC0
      · exact hdpos
      · simp only [neg_neg]
    · have hdneg : inner (𝕜 := ℝ) (D -ᵥ A) nAC0 < 0 := by
        rcases lt_or_gt_of_ne hDAC0 with hdneg | hdpos
        · exact hdneg
        · exfalso
          have hcon := mul_pos hbpos hdpos
          linarith
      refine ⟨nAC0, -nAC0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hnAC0
      · exact hpAC0
      · exact hbpos
      · rw [norm_neg, hnAC0]
      · rw [inner_neg_right, hpAC0, neg_zero]
      · rw [inner_neg_right]; exact neg_pos.mpr hdneg
      · rfl
  obtain ⟨nBDA, nBDC, hnBDA, hpBDA, hinBDA, hnBDC, hpBDC, hinBDC, hBDopp'⟩ :
      ∃ nBDA nBDC : EuclideanSpace ℝ (Fin 2), ‖nBDA‖ = 1 ∧
        inner (𝕜 := ℝ) (D -ᵥ B) nBDA = 0 ∧
        0 < inner (𝕜 := ℝ) (A -ᵥ B) nBDA ∧ ‖nBDC‖ = 1 ∧
        inner (𝕜 := ℝ) (D -ᵥ B) nBDC = 0 ∧
        0 < inner (𝕜 := ℝ) (C -ᵥ B) nBDC ∧ nBDC = -nBDA := by
    rcases lt_or_gt_of_ne hABD0 with haneg | hapos
    · have hcpos : 0 < inner (𝕜 := ℝ) (C -ᵥ B) nBD0 := by
        rcases lt_or_gt_of_ne hCBD0 with hcneg | hcpos
        · exfalso
          have hcon := mul_pos_of_neg_of_neg haneg hcneg
          linarith
        · exact hcpos
      refine ⟨-nBD0, nBD0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [norm_neg, hnBD0]
      · rw [inner_neg_right, hpBD0, neg_zero]
      · rw [inner_neg_right]; exact neg_pos.mpr haneg
      · exact hnBD0
      · exact hpBD0
      · exact hcpos
      · simp only [neg_neg]
    · have hcneg : inner (𝕜 := ℝ) (C -ᵥ B) nBD0 < 0 := by
        rcases lt_or_gt_of_ne hCBD0 with hcneg | hcpos
        · exact hcneg
        · exfalso
          have hcon := mul_pos hapos hcpos
          linarith
      refine ⟨nBD0, -nBD0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hnBD0
      · exact hpBD0
      · exact hapos
      · rw [norm_neg, hnBD0]
      · rw [inner_neg_right, hpBD0, neg_zero]
      · rw [inner_neg_right]; exact neg_pos.mpr hcneg
      · rfl
  have hADneg : A -ᵥ D = -(D -ᵥ A) := by rw [← neg_vsub_eq_vsub_rev]
  have hpDA_D : inner (𝕜 := ℝ) (A -ᵥ D) nDA = 0 := by
    rw [hADneg, inner_neg_left, hpDA, neg_zero]
  have hBDdecomp : B -ᵥ D = (B -ᵥ A) + (A -ᵥ D) :=
    (vsub_add_vsub_cancel B A D).symm
  have hinBDD : 0 < inner (𝕜 := ℝ) (B -ᵥ D) nDA := by
    rw [hBDdecomp, inner_add_left, hpDA_D, add_zero]
    exact hinDAB
  have hCDdecomp : C -ᵥ D = (C -ᵥ A) + (A -ᵥ D) :=
    (vsub_add_vsub_cancel C A D).symm
  have hinCDD : 0 < inner (𝕜 := ℝ) (C -ᵥ D) nDA := by
    rw [hCDdecomp, inner_add_left, hpDA_D, add_zero]
    exact hinDAC
  have hACneg : A -ᵥ C = -(C -ᵥ A) := by rw [← neg_vsub_eq_vsub_rev]
  have hpACB_C : inner (𝕜 := ℝ) (A -ᵥ C) nACB = 0 := by
    rw [hACneg, inner_neg_left, hpACB, neg_zero]
  have hBCdecomp : B -ᵥ C = (B -ᵥ A) + (A -ᵥ C) :=
    (vsub_add_vsub_cancel B A C).symm
  have hinBCB : 0 < inner (𝕜 := ℝ) (B -ᵥ C) nACB := by
    rw [hBCdecomp, inner_add_left, hpACB_C, add_zero]
    exact hinACB
  have hBDneg : B -ᵥ D = -(D -ᵥ B) := by rw [← neg_vsub_eq_vsub_rev]
  have hpBDC_D : inner (𝕜 := ℝ) (B -ᵥ D) nBDC = 0 := by
    rw [hBDneg, inner_neg_left, hpBDC, neg_zero]
  have hCDdecomp : C -ᵥ D = (C -ᵥ B) + (B -ᵥ D) :=
    (vsub_add_vsub_cancel C B D).symm
  have hinCDD2 : 0 < inner (𝕜 := ℝ) (C -ᵥ D) nBDC := by
    rw [hCDdecomp, inner_add_left, hpBDC_D, add_zero]
    exact hinBDC
  have hIr1BC : inner (𝕜 := ℝ) (I1 -ᵥ B) nBC = r1 :=
    inner_eq_radius_of_incircle A B C I1 r1 hr1 hsub1 ht1BC nBC hnBC hpBC
      hinBCA
  have hIr2DA : inner (𝕜 := ℝ) (I2 -ᵥ D) nDA = r2 :=
    inner_eq_radius_of_incircle C D A I2 r2 hr2 hsub2 ht2DA nDA hnDA hpDA_D
      hinCDD
  have hIr3CD : inner (𝕜 := ℝ) (I3 -ᵥ C) nCD = r3 :=
    inner_eq_radius_of_incircle B C D I3 r3 hr3 hsub3 ht3CD nCD hnCD hpCD
      hinCDB
  have hIr4AB : inner (𝕜 := ℝ) (I4 -ᵥ A) nAB = r4 :=
    inner_eq_radius_of_incircle D A B I4 r4 hr4 hsub4 ht4AB nAB hnAB hpAB
      hinABD
  have hIr1AB : inner (𝕜 := ℝ) (I1 -ᵥ A) nAB = r1 :=
    inner_eq_radius_of_incircle_of_mem A B C C A B I1 r1 hr1 hsub1 ht1AB nAB
      hnAB hpAB hinABC (by simp) (by simp) (by simp)
  have hIr1CA : inner (𝕜 := ℝ) (I1 -ᵥ C) nACB = r1 :=
    inner_eq_radius_of_incircle_of_mem A B C B C A I1 r1 hr1 hsub1 ht1CA nACB
      hnACB hpACB_C hinBCB (by simp) (by simp) (by simp)
  have hIr2CD : inner (𝕜 := ℝ) (I2 -ᵥ C) nCD = r2 :=
    inner_eq_radius_of_incircle_of_mem C D A A C D I2 r2 hr2 hsub2 ht2CD nCD
      hnCD hpCD hinCDA (by simp) (by simp) (by simp)
  have hIr2AC : inner (𝕜 := ℝ) (I2 -ᵥ A) nACD = r2 :=
    inner_eq_radius_of_incircle_of_mem C D A D A C I2 r2 hr2 hsub2 ht2AC nACD
      hnACD hpACD hinACD (by simp) (by simp) (by simp)
  have hIr3BC : inner (𝕜 := ℝ) (I3 -ᵥ B) nBC = r3 :=
    inner_eq_radius_of_incircle_of_mem B C D D B C I3 r3 hr3 hsub3 ht3BC nBC
      hnBC hpBC hinBCD (by simp) (by simp) (by simp)
  have hIr3DB : inner (𝕜 := ℝ) (I3 -ᵥ D) nBDC = r3 :=
    inner_eq_radius_of_incircle_of_mem B C D C D B I3 r3 hr3 hsub3 ht3DB nBDC
      hnBDC hpBDC_D hinCDD2 (by simp) (by simp) (by simp)
  have hIr4DA : inner (𝕜 := ℝ) (I4 -ᵥ D) nDA = r4 :=
    inner_eq_radius_of_incircle_of_mem D A B B D A I4 r4 hr4 hsub4 ht4DA nDA
      hnDA hpDA_D hinBDD (by simp) (by simp) (by simp)
  have hIr4BD : inner (𝕜 := ℝ) (I4 -ᵥ B) nBDA = r4 :=
    inner_eq_radius_of_incircle_of_mem D A B A B D I4 r4 hr4 hsub4 ht4BD nBDA
      hnBDA hpBDA hinBDA (by simp) (by simp) (by simp)
  have hCar1 := carnot_inradius_circumradius_general A B C O I1 R r1
    (inner (𝕜 := ℝ) (O -ᵥ B) nBC) (inner (𝕜 := ℝ) (O -ᵥ C) nACB)
    (inner (𝕜 := ℝ) (O -ᵥ A) nAB) nBC nACB nAB hTri1 hR hA hB hC hnBC hpBC
    hinBCA hnACB hpACB_C hinBCB hnAB hpAB hinABC rfl rfl rfl hIr1BC hIr1CA
    hIr1AB
  have hCar2 := carnot_inradius_circumradius_general C D A O I2 R r2
    (inner (𝕜 := ℝ) (O -ᵥ D) nDA) (inner (𝕜 := ℝ) (O -ᵥ A) nACD)
    (inner (𝕜 := ℝ) (O -ᵥ C) nCD) nDA nACD nCD hTri2 hR hC hD hA hnDA hpDA_D
    hinCDD hnACD hpACD hinACD hnCD hpCD hinCDA rfl rfl rfl hIr2DA hIr2AC
    hIr2CD
  have hCar3 := carnot_inradius_circumradius_general B C D O I3 R r3
    (inner (𝕜 := ℝ) (O -ᵥ C) nCD) (inner (𝕜 := ℝ) (O -ᵥ D) nBDC)
    (inner (𝕜 := ℝ) (O -ᵥ B) nBC) nCD nBDC nBC hTri3 hR hB hC hD hnCD hpCD
    hinCDB hnBDC hpBDC_D hinCDD2 hnBC hpBC hinBCD rfl rfl rfl hIr3CD hIr3DB
    hIr3BC
  have hCar4 := carnot_inradius_circumradius_general D A B O I4 R r4
    (inner (𝕜 := ℝ) (O -ᵥ A) nAB) (inner (𝕜 := ℝ) (O -ᵥ B) nBDA)
    (inner (𝕜 := ℝ) (O -ᵥ D) nDA) nAB nBDA nDA hTri4 hR hD hA hB hnAB hpAB
    hinABD hnBDA hpBDA hinBDA hnDA hpDA_D hinBDD rfl rfl rfl hIr4AB hIr4BD
    hIr4DA
  have hACcan : inner (𝕜 := ℝ) (O -ᵥ C) nACB
      + inner (𝕜 := ℝ) (O -ᵥ A) nACD = 0 := by
    have hOC : O -ᵥ C = (O -ᵥ A) + (A -ᵥ C) :=
      (vsub_add_vsub_cancel O A C).symm
    have hbase : inner (𝕜 := ℝ) (O -ᵥ C) nACB
        = inner (𝕜 := ℝ) (O -ᵥ A) nACB := by
      rw [hOC, inner_add_left, hpACB_C, add_zero]
    rw [hACopp', inner_neg_right, ← hbase]
    ring
  have hBDcan : inner (𝕜 := ℝ) (O -ᵥ D) nBDC
      + inner (𝕜 := ℝ) (O -ᵥ B) nBDA = 0 := by
    have hOD : O -ᵥ D = (O -ᵥ B) + (B -ᵥ D) :=
      (vsub_add_vsub_cancel O B D).symm
    have hbase : inner (𝕜 := ℝ) (O -ᵥ D) nBDC
        = inner (𝕜 := ℝ) (O -ᵥ B) nBDC := by
      rw [hOD, inner_add_left, hpBDC_D, add_zero]
    rw [hbase, hBDopp', inner_neg_right]
    ring
  linear_combination -hCar1 - hCar2 + hCar3 + hCar4 + hACcan - hBDcan

end MetaMathlibExt
end
