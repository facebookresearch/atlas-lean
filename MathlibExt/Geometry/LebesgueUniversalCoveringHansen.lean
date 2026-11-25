/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.LebesgueUniversalCoveringConstant
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Order.Zorn
import Mathlib.Topology.Order.IntermediateValue

/-!
# Hansen's corrected upper bound for Lebesgue's covering problem

The Lebesgue universal covering constant is at most `0.844137708398`.

The proof uses Reduction 1 through Reduction 3 of Baez, Bagdasaryan and Gibbs,
*The Lebesgue universal covering problem*, J. Comput. Geom. 6 (2015), 288–299,
[arXiv:1502.01251](https://arxiv.org/abs/1502.01251).

Every planar diameter-one set is contained in a maximal set with the same diameter bound, which
has width one in every direction. A rotation and a translation place it inside a regular
hexagon. The construction arranges two missing corners by rotation, uses contacts on the
remaining sides to cut the opposite corner, and uses reflection to make a final straight cut.

The formal cover uses finitely many rational supporting half-spaces in place of circular
boundaries. Fourteen rational trapezoid areas bound its area.
-/

open MeasureTheory Set
open scoped InnerProductSpace

namespace MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted

/-! ## Diameter-one completions -/

private def PairwiseUnitBound (K : Set Plane) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ 1

private theorem exists_complete {K : Set Plane} (hK : PairwiseUnitBound K) :
    ∃ L : Set Plane, K ⊆ L ∧ PairwiseUnitBound L ∧
      ∀ z, (∀ y ∈ L, ‖z - y‖ ≤ 1) → z ∈ L := by
  obtain ⟨L, hKL, hL⟩ := zorn_subset_nonempty {S | PairwiseUnitBound S} (by
    rintro c hc chain _
    refine ⟨⋃₀ c, ?_, fun S hS => subset_sUnion_of_mem hS⟩
    intro x hx y hy
    obtain ⟨A, hA, hx⟩ := mem_sUnion.1 hx
    obtain ⟨B, hB, hy⟩ := mem_sUnion.1 hy
    rcases chain.total hA hB with hAB | hBA
    · exact hc hB x (hAB hx) y hy
    · exact hc hA x hx y (hBA hy)) K hK
  refine ⟨L, hKL, hL.prop, fun z hz => ?_⟩
  have hins : PairwiseUnitBound (insert z L) := by
    intro x hx y hy
    rcases mem_insert_iff.1 hx with hzx | hx
    · subst x
      rcases mem_insert_iff.1 hy with hzy | hy
      · subst y
        simp
      · exact hz _ hy
    · rcases (mem_insert_iff.1 hy : y = z ∨ y ∈ L) with hzy | hy
      · subst y
        rw [norm_sub_rev]
        exact hz _ hx
      · exact hL.prop _ hx _ hy
  have h := hL.eq_of_subset hins (subset_insert z L)
  exact h ▸ mem_insert z L

private theorem complete_eq_iInter_closedBall {L : Set Plane} (hL : PairwiseUnitBound L)
    (hcomplete : ∀ z, (∀ y ∈ L, ‖z - y‖ ≤ 1) → z ∈ L) :
    L = ⋂ y ∈ L, Metric.closedBall y 1 := by
  ext z
  simp only [mem_iInter, Metric.mem_closedBall, dist_eq_norm]
  exact ⟨fun hz y hy => hL _ hz _ hy, hcomplete z⟩

private theorem norm_sub_sq_le_one {x y : Plane} (h : ‖x - y‖ ≤ 1) :
    ‖x - y‖ ^ 2 ≤ 1 := by
  have hn := norm_nonneg (x - y)
  nlinarith

/-- At a supporting point `p` with unit normal `u`, the opposite point `p - u` belongs to
the completion. If some `x` is too far from `p - u`, a short step from `p` toward a positive
multiple of `u` minus `p - x` stays in the completion and increases the support value. -/
private theorem complete_antipode {L : Set Plane} (hL : PairwiseUnitBound L)
    (hcomplete : ∀ z, (∀ y ∈ L, ‖z - y‖ ≤ 1) → z ∈ L)
    {p u : Plane} (hp : p ∈ L) (hu : ‖u‖ = 1)
    (hsupport : ∀ y ∈ L, ⟪u, y⟫_ℝ ≤ ⟪u, p⟫_ℝ) :
    p - u ∈ L := by
  apply hcomplete
  intro x hx
  by_contra! hfar
  let b := ⟪u, p - x⟫_ℝ
  let c := ‖p - x‖ ^ 2 / 2
  have hfar_sq : 1 < ‖p - u - x‖ ^ 2 := by nlinarith
  rw [show p - u - x = (p - x) - u by abel, norm_sub_sq_real, hu,
    real_inner_comm u (p - x)] at hfar_sq
  have hbc : b < c := by dsimp [b, c]; linarith
  have hb : 0 ≤ b := by
    dsimp [b]
    rw [inner_sub_right]
    exact sub_nonneg.mpr (hsupport x hx)
  let m := (b + c) / 2
  have hbm : b < m := by dsimp [m]; linarith
  have hmc : m < c := by dsimp [m]; linarith
  have hm : 0 ≤ m := hb.trans hbm.le
  let d := m • u - (p - x)
  let t := min 1 ((c - m) / (‖d‖ ^ 2 + 1))
  have ht : 0 < t := lt_min (by norm_num) (div_pos (sub_pos.mpr hmc) (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htd : t * (‖d‖ ^ 2 + 1) ≤ c - m :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  have hnew : p + t • d ∈ L := by
    apply hcomplete
    intro y hy
    have hpysq := norm_sub_sq_le_one (hL p hp y hy)
    have hxysq := norm_sub_sq_le_one (hL x hx y hy)
    rw [show x - y = (p - y) - (p - x) by abel, norm_sub_sq_real] at hxysq
    have hinner := real_inner_le_norm (p - y) u
    rw [hu, mul_one] at hinner
    have hinner' : ⟪p - y, u⟫_ℝ ≤ 1 := hinner.trans (hL p hp y hy)
    have hinnerd : ⟪p - y, d⟫_ℝ ≤ m - c + (1 - ‖p - y‖ ^ 2) / 2 := by
      dsimp [d]
      rw [inner_sub_right, real_inner_smul_right]
      have := mul_le_mul_of_nonneg_left hinner' hm
      dsimp [c]
      linarith
    have hsq : ‖p + t • d - y‖ ^ 2 ≤ 1 := by
      rw [show p + t • d - y = (p - y) + t • d by abel, norm_add_sq_real,
        real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.le, mul_pow]
      have h1 := mul_le_mul_of_nonneg_left hinnerd ht.le
      have h2 := mul_le_mul_of_nonneg_left hpysq (sub_nonneg.2 ht1)
      have h3 := mul_le_mul_of_nonneg_left htd ht.le
      nlinarith only [h1, h2, h3, mul_pos ht (sub_pos.mpr hmc), ht.le]
    exact le_of_not_gt (fun h => by nlinarith)
  have hpos : 0 < ⟪u, d⟫_ℝ := by
    dsimp [d]
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu]
    change 0 < m * 1 ^ 2 - b
    simpa using sub_pos.mpr hbm
  have hcontra := hsupport _ hnew
  rw [inner_add_right, real_inner_smul_right] at hcontra
  linarith [mul_pos ht hpos]

/-! ## Coordinates, rotations, and support -/

private noncomputable def pt (x y : ℝ) : Plane := !₂[x, y]

private theorem plane_ext {p q : Plane} (hx : p 0 = q 0) (hy : p 1 = q 1) : p = q := by
  ext i
  fin_cases i
  · exact hx
  · exact hy

private theorem inner_coords (p q : Plane) :
    ⟪p, q⟫_ℝ = p 0 * q 0 + p 1 * q 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

private theorem norm_sq_coords (p : Plane) : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

private theorem norm_one_coords {p : Plane} (hp : p 0 ^ 2 + p 1 ^ 2 = 1) : ‖p‖ = 1 := by
  have := norm_nonneg p
  rw [← norm_sq_coords] at hp
  nlinarith

/-- In coordinates the transpose of an orthogonal matrix is its inverse. -/
private noncomputable def matrixIsometry (a b c d : ℝ)
    (h₁ : a ^ 2 + c ^ 2 = 1) (h₂ : b ^ 2 + d ^ 2 = 1)
    (h₃ : a * b + c * d = 0) (h₄ : a ^ 2 + b ^ 2 = 1)
    (h₅ : c ^ 2 + d ^ 2 = 1) (h₆ : a * c + b * d = 0) :
    Plane ≃ₗᵢ[ℝ] Plane where
  toFun p := pt (a * p 0 + b * p 1) (c * p 0 + d * p 1)
  invFun p := pt (a * p 0 + c * p 1) (b * p 0 + d * p 1)
  left_inv p := by
    apply plane_ext
    · change a * (a * p 0 + b * p 1) + c * (c * p 0 + d * p 1) = p 0
      linear_combination p 0 * h₁ + p 1 * h₃
    · change b * (a * p 0 + b * p 1) + d * (c * p 0 + d * p 1) = p 1
      linear_combination p 0 * h₃ + p 1 * h₂
  right_inv p := by
    apply plane_ext
    · change a * (a * p 0 + c * p 1) + b * (b * p 0 + d * p 1) = p 0
      linear_combination p 0 * h₄ + p 1 * h₆
    · change c * (a * p 0 + c * p 1) + d * (b * p 0 + d * p 1) = p 1
      linear_combination p 0 * h₆ + p 1 * h₅
  map_add' p q := by
    apply plane_ext
    · change a * (p 0 + q 0) + b * (p 1 + q 1) =
        a * p 0 + b * p 1 + (a * q 0 + b * q 1)
      ring
    · change c * (p 0 + q 0) + d * (p 1 + q 1) =
        c * p 0 + d * p 1 + (c * q 0 + d * q 1)
      ring
  map_smul' t p := by
    apply plane_ext
    · change a * (t * p 0) + b * (t * p 1) = t * (a * p 0 + b * p 1)
      ring
    · change c * (t * p 0) + d * (t * p 1) = t * (c * p 0 + d * p 1)
      ring
  norm_map' p := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    simp only [norm_sq_coords]
    change (a * p 0 + b * p 1) ^ 2 + (c * p 0 + d * p 1) ^ 2 = p 0 ^ 2 + p 1 ^ 2
    linear_combination p 0 ^ 2 * h₁ + p 1 ^ 2 * h₂ + 2 * p 0 * p 1 * h₃

private noncomputable def rotate (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    Plane ≃ₗᵢ[ℝ] Plane :=
  matrixIsometry c (-s) s c h (by linear_combination h) (by ring)
    (by linear_combination h) (by linear_combination h) (by ring)

private theorem rotate_apply (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (p : Plane) :
    rotate c s h p = pt (c * p 0 - s * p 1) (s * p 0 + c * p 1) := by
  apply plane_ext
  · change c * p 0 + (-s) * p 1 = c * p 0 - s * p 1
    ring
  · rfl

private theorem continuous_pt {α : Type*} [TopologicalSpace α] {x y : α → ℝ}
    (hx : Continuous x) (hy : Continuous y) : Continuous fun t => pt (x t) (y t) := by
  change Continuous ((WithLp.toLp 2) ∘ fun t => ![x t, y t])
  apply (PiLp.continuous_toLp _ _).comp
  rw [continuous_pi_iff]
  intro i
  fin_cases i
  · exact hx
  · exact hy

private noncomputable def support (K : Set Plane) (u : Plane) :=
  sSup ((fun p => ⟪u, p⟫_ℝ) '' K)

private theorem support_attained {K : Set Plane} (hc : IsCompact K) (hn : K.Nonempty)
    (u : Plane) :
    ∃ p ∈ K, support K u = ⟪u, p⟫_ℝ ∧ ∀ q ∈ K, ⟪u, q⟫_ℝ ≤ ⟪u, p⟫_ℝ :=
  hc.exists_sSup_image_eq_and_ge hn (continuous_const.inner continuous_id).continuousOn

private theorem inner_sub_le_one {K : Set Plane} (hK : PairwiseUnitBound K)
    {p q u : Plane} (hp : p ∈ K) (hq : q ∈ K) (hu : ‖u‖ = 1) :
    ⟪u, p⟫_ℝ - ⟪u, q⟫_ℝ ≤ 1 := by
  rw [← inner_sub_right]
  exact (real_inner_le_norm _ _).trans (by simpa [hu] using hK p hp q hq)

private theorem support_lower_attained {K : Set Plane} (hc : IsCompact K) (hn : K.Nonempty)
    (hK : PairwiseUnitBound K) (hcomplete : ∀ z, (∀ y ∈ K, ‖z - y‖ ≤ 1) → z ∈ K)
    {u : Plane} (hu : ‖u‖ = 1) :
    ∃ q ∈ K, ⟪u, q⟫_ℝ = support K u - 1 := by
  obtain ⟨p, hp, hpu, hmax⟩ := support_attained hc hn u
  refine ⟨p - u, complete_antipode hK hcomplete hp hu hmax, ?_⟩
  rw [inner_sub_right, real_inner_self_eq_norm_sq, hu, hpu, one_pow]

private theorem support_neg {K : Set Plane} (hc : IsCompact K) (hn : K.Nonempty)
    (hK : PairwiseUnitBound K) (hcomplete : ∀ z, (∀ y ∈ K, ‖z - y‖ ≤ 1) → z ∈ K)
    {u : Plane} (hu : ‖u‖ = 1) :
    support K (-u) = 1 - support K u := by
  obtain ⟨p, hp, hpu, _⟩ := support_attained hc hn u
  obtain ⟨v, hv, hvu, hmax⟩ := support_attained hc hn (-u)
  obtain ⟨q, hq, hqu⟩ := support_lower_attained hc hn hK hcomplete hu
  have h1 := inner_sub_le_one hK hp hv hu
  have h2 := hmax q hq
  rw [inner_neg_left, inner_neg_left, hqu] at h2
  rw [hvu, inner_neg_left, hpu]
  linarith

private theorem compact_complete {K : Set Plane} (hn : K.Nonempty) (hK : PairwiseUnitBound K)
    (hcomplete : ∀ z, (∀ y ∈ K, ‖z - y‖ ≤ 1) → z ∈ K) : IsCompact K := by
  obtain ⟨p, hp⟩ := hn
  apply Metric.isCompact_iff_isClosed_bounded.2
  refine ⟨?_, (Metric.isBounded_closedBall (x := p) (r := 1)).subset ?_⟩
  · rw [complete_eq_iInter_closedBall hK hcomplete]
    exact isClosed_iInter fun _ => isClosed_iInter fun _ => Metric.isClosed_closedBall
  · intro x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hK x hx p hp

private theorem pairwise_image {K : Set Plane} (hK : PairwiseUnitBound K)
    (e : Plane ≃ᵢ Plane) : PairwiseUnitBound (e '' K) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  simpa only [← dist_eq_norm, e.isometry.dist_eq] using hK p hp q hq

private theorem complete_image {K : Set Plane}
    (hcomplete : ∀ z, (∀ y ∈ K, ‖z - y‖ ≤ 1) → z ∈ K)
    (e : Plane ≃ᵢ Plane) :
    ∀ z, (∀ y ∈ e '' K, ‖z - y‖ ≤ 1) → z ∈ e '' K := by
  intro z hz
  refine ⟨e.symm z, hcomplete _ (fun y hy => ?_), e.apply_symm_apply _⟩
  have h := hz _ (mem_image_of_mem e hy)
  rw [← dist_eq_norm, ← e.isometry.dist_eq, e.apply_symm_apply, dist_eq_norm]
  exact h

private noncomputable def g : ℝ := Real.sqrt 3

private theorem hg_pos : 0 < g := Real.sqrt_pos.2 (by norm_num)
private theorem hg_sq : g ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private noncomputable def hexNormal (i : Fin 3) : Plane :=
  ![pt 1 0, pt (-1 / 2) (g / 2), pt (-1 / 2) (-g / 2)] i

private theorem hexNormal_norm (i : Fin 3) : ‖hexNormal i‖ = 1 := by
  apply norm_one_coords
  fin_cases i
  · change (1 : ℝ) ^ 2 + 0 ^ 2 = 1
    norm_num
  · change (-1 / 2 : ℝ) ^ 2 + (g / 2) ^ 2 = 1
    linear_combination hg_sq / 4
  · change (-1 / 2 : ℝ) ^ 2 + (-g / 2) ^ 2 = 1
    linear_combination hg_sq / 4

private def hexagon : Set Plane := {p | ∀ i, |⟪hexNormal i, p⟫_ℝ| ≤ 1 / 2}

/-- The sum of the three strip midpoints changes sign after half a turn. At a zero of this sum,
one translation centers all three strips. -/
private theorem exists_image_subset_hexagon {K : Set Plane} (hn : K.Nonempty)
    (hK : PairwiseUnitBound K) (hcomplete : ∀ z, (∀ y ∈ K, ‖z - y‖ ≤ 1) → z ∈ K) :
    ∃ e : Plane ≃ᵢ Plane, e '' K ⊆ hexagon := by
  have hc := compact_complete hn hK hcomplete
  let R (θ : ℝ) := rotate (Real.cos θ) (Real.sin θ)
    (by linarith [Real.sin_sq_add_cos_sq θ])
  let m (θ : ℝ) (i : Fin 3) := support K (R θ (hexNormal i)) - 1 / 2
  let f (θ : ℝ) := ∑ i, m θ i
  have hR i : Continuous fun θ => R θ (hexNormal i) := by
    simp only [R, rotate_apply]
    exact continuous_pt ((Real.continuous_cos.mul_const _).sub
      (Real.continuous_sin.mul_const _))
      ((Real.continuous_sin.mul_const _).add (Real.continuous_cos.mul_const _))
  have hsup : Continuous (support K) :=
    hc.continuous_sSup (f := fun u p : Plane => ⟪u, p⟫_ℝ) continuous_inner
  have hf : Continuous f := continuous_finsetSum _ (fun i _ =>
    (hsup.comp (hR i)).sub continuous_const)
  have h0 (p : Plane) : R 0 p = p := by
    simp only [R, rotate_apply]
    apply plane_ext
    · change Real.cos 0 * p 0 - Real.sin 0 * p 1 = p 0
      simp
    · change Real.sin 0 * p 0 + Real.cos 0 * p 1 = p 1
      simp
  have hpi (p : Plane) : R Real.pi p = -p := by
    simp only [R, rotate_apply]
    apply plane_ext
    · change Real.cos Real.pi * p 0 - Real.sin Real.pi * p 1 = -p 0
      simp
    · change Real.sin Real.pi * p 0 + Real.cos Real.pi * p 1 = -p 1
      simp
  have hsign : f Real.pi = -f 0 := by
    simp only [f, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    dsimp [m]
    rw [hpi, h0, support_neg hc hn hK hcomplete (hexNormal_norm i)]
    ring
  obtain ⟨θ, _, hθ⟩ := intermediate_value_uIcc (a := (0 : ℝ)) (b := Real.pi)
    (f := f) hf.continuousOn (show (0 : ℝ) ∈ uIcc (f 0) (f Real.pi) by
      rw [hsign, Set.mem_uIcc]
      rcases le_total (f 0) 0 with h | h
      · exact Or.inl ⟨h, by linarith⟩
      · exact Or.inr ⟨by linarith, h⟩)
  have hsum : m θ 0 + m θ 1 + m θ 2 = 0 := by
    simpa [f, Fin.sum_univ_three] using hθ
  let t := pt (m θ 0) ((2 * m θ 1 + m θ 0) / g)
  have hshift (i : Fin 3) : ⟪hexNormal i, t⟫_ℝ = m θ i := by
    rw [inner_coords]
    fin_cases i
    · change 1 * m θ 0 + 0 * ((2 * m θ 1 + m θ 0) / g) = m θ 0
      ring
    · change (-1 / 2) * m θ 0 + g / 2 * ((2 * m θ 1 + m θ 0) / g) = m θ 1
      rw [show g / 2 * ((2 * m θ 1 + m θ 0) / g) = (2 * m θ 1 + m θ 0) / 2 by
        field_simp [ne_of_gt hg_pos]]
      ring
    · change (-1 / 2) * m θ 0 + -g / 2 * ((2 * m θ 1 + m θ 0) / g) = m θ 2
      rw [show -g / 2 * ((2 * m θ 1 + m θ 0) / g) = -(2 * m θ 1 + m θ 0) / 2 by
        field_simp [ne_of_gt hg_pos]]
      linarith only [hsum]
  refine ⟨(R θ).symm.toIsometryEquiv.trans (IsometryEquiv.subRight t), ?_⟩
  rintro _ ⟨p, hp, rfl⟩ i
  change |⟪hexNormal i, (R θ).symm p - t⟫_ℝ| ≤ 1 / 2
  rw [inner_sub_right, hshift, ← (R θ).inner_map_map, LinearIsometryEquiv.apply_symm_apply]
  have hu : ‖R θ (hexNormal i)‖ = 1 := by simp [hexNormal_norm]
  obtain ⟨pmax, hpmax, hsupmax, hmax⟩ := support_attained hc hn (R θ (hexNormal i))
  exact abs_le.2 ⟨by dsimp [m]; rw [hsupmax]; linarith [inner_sub_le_one hK hpmax hp hu],
    by dsimp [m]; rw [hsupmax]; linarith [hmax p hp]⟩

/-! ## Truncating the hexagon -/

private noncomputable def rotateSixty : Plane ≃ₗᵢ[ℝ] Plane :=
  rotate (1 / 2) (-g / 2) (by linear_combination hg_sq / 4)

private noncomputable def reflectDE : Plane ≃ₗᵢ[ℝ] Plane :=
  matrixIsometry (-1 / 2) (g / 2) (g / 2) (1 / 2)
    (by linear_combination hg_sq / 4) (by linear_combination hg_sq / 4) (by ring)
    (by linear_combination hg_sq / 4) (by linear_combination hg_sq / 4) (by ring)

private theorem rotateSixty_mem_hexagon {p : Plane} (hp : p ∈ hexagon) :
    rotateSixty p ∈ hexagon := by
  intro i
  have h (j : Fin 3) := hp j
  fin_cases i
  · have he : ⟪hexNormal 0, rotateSixty p⟫_ℝ = -⟪hexNormal 2, p⟫_ℝ := by
      simp only [rotateSixty, rotate_apply, inner_coords]
      change 1 * (1 / 2 * p 0 - (-g / 2) * p 1) + 0 * _ = -((-1 / 2) * p 0 + (-g / 2) * p 1)
      ring
    simpa [he] using h 2
  · have he : ⟪hexNormal 1, rotateSixty p⟫_ℝ = -⟪hexNormal 0, p⟫_ℝ := by
      simp only [rotateSixty, rotate_apply, inner_coords]
      change (-1 / 2) * (1 / 2 * p 0 - (-g / 2) * p 1) +
        (g / 2) * ((-g / 2) * p 0 + 1 / 2 * p 1) = -(1 * p 0 + 0 * p 1)
      linear_combination -p 0 * hg_sq / 4
    simpa [he] using h 0
  · have he : ⟪hexNormal 2, rotateSixty p⟫_ℝ = -⟪hexNormal 1, p⟫_ℝ := by
      simp only [rotateSixty, rotate_apply, inner_coords]
      change (-1 / 2) * (1 / 2 * p 0 - (-g / 2) * p 1) + (-g / 2) * ((-g / 2) * p 0 + 1 / 2 * p 1) =
        -((-1 / 2) * p 0 + (g / 2) * p 1)
      linear_combination p 0 * hg_sq / 4
    simpa [he] using h 1

private theorem reflectDE_apply (p : Plane) :
    reflectDE p = pt ((-1 / 2) * p 0 + (g / 2) * p 1) ((g / 2) * p 0 + (1 / 2) * p 1) := rfl

private theorem reflect_hex {p : Plane} (hp : p ∈ hexagon) : reflectDE p ∈ hexagon := by
  intro i
  have h (j : Fin 3) := hp j
  fin_cases i
  · change |⟪hexNormal 0, reflectDE p⟫_ℝ| ≤ 1 / 2
    have he : ⟪hexNormal 0, reflectDE p⟫_ℝ = ⟪hexNormal 1, p⟫_ℝ := by
      simp only [reflectDE_apply, inner_coords]
      change 1 * ((-1 / 2) * p 0 + (g / 2) * p 1) + 0 * _ = (-1 / 2) * p 0 + (g / 2) * p 1
      ring
    rw [he]
    exact h 1
  · have he : ⟪hexNormal 1, reflectDE p⟫_ℝ = ⟪hexNormal 0, p⟫_ℝ := by
      simp only [reflectDE_apply, inner_coords]
      change (-1 / 2) * ((-1 / 2) * p 0 + (g / 2) * p 1) +
        (g / 2) * ((g / 2) * p 0 + 1 / 2 * p 1) = 1 * p 0 + 0 * p 1
      linear_combination p 0 * hg_sq / 4
    simpa [he] using h 0
  · have he : ⟪hexNormal 2, reflectDE p⟫_ℝ = ⟪hexNormal 2, p⟫_ℝ := by
      simp only [reflectDE_apply, inner_coords]
      change (-1 / 2) * ((-1 / 2) * p 0 + (g / 2) * p 1) +
        (-g / 2) * ((g / 2) * p 0 + 1 / 2 * p 1) = (-1 / 2) * p 0 + (-g / 2) * p 1
      linear_combination -p 0 * hg_sq / 4
    simpa [he] using h 2

-- Sine and cosine of the slant, using the rational half-angle parameter 1 / 88.

private noncomputable def s : ℝ := 176 / 7745
private noncomputable def c : ℝ := 7743 / 7745

private noncomputable def cornerNormal (i : Fin 6) : Plane :=
  ![pt (-s) c, pt ((g * c - s) / 2) ((g * s + c) / 2), pt ((g * c + s) / 2) ((g * s - c) / 2),
    pt s (-c), pt ((-g * c + s) / 2) ((-g * s - c) / 2), pt ((-g * c - s) / 2) ((-g * s + c) / 2)] i

private theorem cornerNorm (i : Fin 6) : ‖cornerNormal i‖ = 1 := by
  apply norm_one_coords
  fin_cases i <;> dsimp [cornerNormal, pt] <;> norm_num [s, c] <;> nlinarith only [hg_sq]

private theorem cornerOpposite (i : Fin 6) :
    cornerNormal (i + 3) = -cornerNormal i := by
  fin_cases i <;> apply plane_ext <;> dsimp [cornerNormal, pt] <;> ring

private theorem inner_cornerNormal_rotateSixty (i : Fin 6) (p : Plane) :
    ⟪cornerNormal i, rotateSixty p⟫_ℝ = ⟪cornerNormal (i + 5), p⟫_ℝ := by
  simp only [inner_coords, rotateSixty, rotate_apply]
  fin_cases i <;> dsimp [cornerNormal, pt]
  · ring
  · linear_combination (-s * p 0 + c * p 1) / 4 * hg_sq
  · linear_combination (-s * p 0 + c * p 1) / 4 * hg_sq
  · ring
  · linear_combination (s * p 0 - c * p 1) / 4 * hg_sq
  · linear_combination (s * p 0 - c * p 1) / 4 * hg_sq

private def insideCorner (K : Set Plane) (i : Fin 6) :=
  ∀ p ∈ K, ⟪cornerNormal i, p⟫_ℝ ≤ 1 / 2

private theorem corner_pair {K : Set Plane} (hK : PairwiseUnitBound K) (i : Fin 6) :
    insideCorner K i ∨ insideCorner K (i + 3) := by
  by_contra! h
  simp only [insideCorner, not_forall, not_le] at h
  obtain ⟨⟨p, hp, hp'⟩, q, hq, hq'⟩ := h
  rw [cornerOpposite, inner_neg_left] at hq'
  linarith [inner_sub_le_one hK hp hq (cornerNorm i)]

private noncomputable def rotateBySteps : ℕ → Plane ≃ₗᵢ[ℝ] Plane
  | 0 => LinearIsometryEquiv.refl ℝ Plane
  | n + 1 => (rotateBySteps n).trans rotateSixty

private theorem rotateBySteps_mem_hexagon (n : ℕ) {p : Plane} (hp : p ∈ hexagon) :
    rotateBySteps n p ∈ hexagon := by
  induction n with
  | zero => exact hp
  | succ n ih => exact rotateSixty_mem_hexagon ih

private def cornerShift : ℕ → Fin 6
  | 0 => 0
  | n + 1 => 5 + cornerShift n

private theorem inner_cornerNormal_rotateBySteps (n : ℕ) (i : Fin 6) (p : Plane) :
    ⟪cornerNormal i, rotateBySteps n p⟫_ℝ = ⟪cornerNormal (i + cornerShift n), p⟫_ℝ := by
  induction n generalizing i with
  | zero => simp [rotateBySteps, cornerShift]
  | succ n ih =>
    rw [rotateBySteps, LinearIsometryEquiv.trans_apply, inner_cornerNormal_rotateSixty, ih,
      cornerShift, add_assoc]

/-- Opposite corners of the slanted hexagon cannot both be entered. Some multiple of a
sixty-degree rotation therefore puts the set outside both of the open corners C and E. -/
private theorem exists_image_subset_truncated {K : Set Plane} (hK : PairwiseUnitBound K)
    (hHex : K ⊆ hexagon) :
    ∃ e : Plane ≃ᵢ Plane, e '' K ⊆ hexagon ∧
      insideCorner (e '' K) 2 ∧ insideCorner (e '' K) 4 := by
  have hA : insideCorner K 0 ∨ insideCorner K 3 := corner_pair hK 0
  have hB : insideCorner K 1 ∨ insideCorner K 4 := corner_pair hK 1
  have hC : insideCorner K 2 ∨ insideCorner K 5 := corner_pair hK 2
  have h : (insideCorner K 2 ∧ insideCorner K 4) ∨ (insideCorner K 1 ∧ insideCorner K 3) ∨
      (insideCorner K 0 ∧ insideCorner K 2) ∨ (insideCorner K 5 ∧ insideCorner K 1) ∨
      (insideCorner K 4 ∧ insideCorner K 0) ∨ (insideCorner K 3 ∧ insideCorner K 5) := by
    tauto
  have hplace (n : ℕ) (h₂ : insideCorner K (2 + cornerShift n))
      (h₄ : insideCorner K (4 + cornerShift n)) :
      ∃ e : Plane ≃ᵢ Plane, e '' K ⊆ hexagon ∧
        insideCorner (e '' K) 2 ∧ insideCorner (e '' K) 4 := by
    refine ⟨(rotateBySteps n).toIsometryEquiv, ?_, ?_, ?_⟩
    · rintro _ ⟨p, hp, rfl⟩
      exact rotateBySteps_mem_hexagon n (hHex hp)
    · rintro _ ⟨p, hp, rfl⟩
      change ⟪cornerNormal 2, rotateBySteps n p⟫_ℝ ≤ 1 / 2
      rw [inner_cornerNormal_rotateBySteps]
      exact h₂ p hp
    · rintro _ ⟨p, hp, rfl⟩
      change ⟪cornerNormal 4, rotateBySteps n p⟫_ℝ ≤ 1 / 2
      rw [inner_cornerNormal_rotateBySteps]
      exact h₄ p hp
  rcases h with ⟨h₂, h₄⟩ | ⟨h₁, h₃⟩ | ⟨h₀, h₂⟩ |
    ⟨h₅, h₁⟩ | ⟨h₄, h₀⟩ | ⟨h₃, h₅⟩
  · exact hplace 0 h₂ h₄
  · exact hplace 1 h₁ h₃
  · exact hplace 2 h₀ h₂
  · exact hplace 3 h₅ h₁
  · exact hplace 4 h₄ h₀
  · exact hplace 5 h₃ h₅

/-! ## The polygonal enclosure -/

private noncomputable def r : ℝ := g / 3
private noncomputable def rlo : ℝ := 0.57735026918
private noncomputable def rhi : ℝ := 0.57735026920

private theorem hr_pos : 0 < r := div_pos hg_pos (by norm_num)
private theorem hgr : g * r = 1 := by
  dsimp [r]
  linear_combination hg_sq / 3

private theorem r_bounds : rlo ≤ r ∧ r ≤ rhi := by
  have hg0 := hg_pos
  have hg2 := hg_sq
  constructor
  · by_contra! h
    have hlt := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 3)).1 h
    have hh : (3 * rlo - g) * (3 * rlo + g) > 0 := by
      apply mul_pos (sub_pos.mpr (by linarith only [hlt]))
      dsimp [rlo]
      linarith
    norm_num [rlo] at hh
    nlinarith only [hh, hg2]
  · by_contra! h
    have hlt := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)).1 h
    have hh : (g - 3 * rhi) * (g + 3 * rhi) > 0 := by
      apply mul_pos (sub_pos.mpr (by linarith only [hlt]))
      dsimp [rhi]
      linarith
    norm_num [rhi] at hh
    nlinarith only [hh, hg2]

private theorem hexCoords {p : Plane} (hp : p ∈ hexagon) :
    |p 0| ≤ 1 / 2 ∧ -r * (1 - p 0) ≤ p 1 ∧ -r * (1 + p 0) ≤ p 1 ∧
      p 1 ≤ r * (1 - p 0) ∧ p 1 ≤ r * (1 + p 0) := by
  have h0 := hp 0
  have h1 := abs_le.mp (hp 1)
  have h2 := abs_le.mp (hp 2)
  rw [inner_coords] at h0 h1 h2
  change |1 * p 0 + 0 * p 1| ≤ 1 / 2 at h0
  change -(1 / 2 : ℝ) ≤ (-1 / 2) * p 0 + (g / 2) * p 1 ∧
    (-1 / 2) * p 0 + (g / 2) * p 1 ≤ 1 / 2 at h1
  change -(1 / 2 : ℝ) ≤ (-1 / 2) * p 0 + (-g / 2) * p 1 ∧
    (-1 / 2) * p 0 + (-g / 2) * p 1 ≤ 1 / 2 at h2
  refine ⟨by simpa using h0, ?_, ?_, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left h1.1 hr_pos.le
    linear_combination 2 * hh + p 1 * hgr
  · have hh := mul_le_mul_of_nonneg_left h2.2 hr_pos.le
    linear_combination 2 * hh + p 1 * hgr
  · have hh := mul_le_mul_of_nonneg_left h2.1 hr_pos.le
    linear_combination 2 * hh - p 1 * hgr
  · have hh := mul_le_mul_of_nonneg_left h1.2 hr_pos.le
    linear_combination 2 * hh - p 1 * hgr

private theorem support_side {K : Set Plane} (hn : K.Nonempty) (hK : PairwiseUnitBound K)
    (hcomplete : ∀ z, (∀ y ∈ K, ‖z - y‖ ≤ 1) → z ∈ K)
    (hhex : K ⊆ hexagon) (i : Fin 3) :
    ∃ p ∈ K, ⟪hexNormal i, p⟫_ℝ = 1 / 2 := by
  obtain ⟨p, hp, hpmax, _⟩ := support_attained (compact_complete hn hK hcomplete) hn (hexNormal i)
  obtain ⟨q, hq, hqmin⟩ :=
    support_lower_attained (compact_complete hn hK hcomplete) hn hK hcomplete (hexNormal_norm i)
  refine ⟨p, hp, ?_⟩
  have h1 := (abs_le.1 (hhex hp i)).2
  have h2 := (abs_le.1 (hhex hq i)).1
  rw [hqmin, hpmax] at h2
  linarith

private theorem support_CD {K : Set Plane} (hn : K.Nonempty) (hK : PairwiseUnitBound K)
    (hcomplete : ∀ z, (∀ y ∈ K, ‖z - y‖ ≤ 1) → z ∈ K)
    (hhex : K ⊆ hexagon) :
    ∃ q ∈ K, q 1 = r * (q 0 - 1) := by
  obtain ⟨p, hp, hpmax, hpbound⟩ :=
    support_attained (compact_complete hn hK hcomplete) hn (hexNormal 1)
  obtain ⟨q, hq, hqmin⟩ :=
    support_lower_attained (compact_complete hn hK hcomplete) hn hK hcomplete (hexNormal_norm 1)
  have h1 := (abs_le.1 (hhex hp 1)).2
  have h2 := (abs_le.1 (hhex hq 1)).1
  have hqeq : ⟪hexNormal 1, q⟫_ℝ = -(1 / 2) := by
    rw [hqmin, hpmax]
    linarith [hqmin, hpmax]
  refine ⟨q, hq, ?_⟩
  rw [inner_coords] at hqeq
  change (-1 / 2) * q 0 + (g / 2) * q 1 = -(1 / 2) at hqeq
  linear_combination 2 * r * hqeq - q 1 * hgr

private theorem support_DE {K : Set Plane} (hn : K.Nonempty) (hK : PairwiseUnitBound K)
    (hcomplete : ∀ z, (∀ y ∈ K, ‖z - y‖ ≤ 1) → z ∈ K)
    (hhex : K ⊆ hexagon) :
    ∃ q ∈ K, q 1 = r * (-q 0 - 1) := by
  obtain ⟨q, hq, hqeq⟩ := support_side hn hK hcomplete hhex 2
  refine ⟨q, hq, ?_⟩
  rw [inner_coords] at hqeq
  change (-1 / 2) * q 0 + (-g / 2) * q 1 = 1 / 2 at hqeq
  linear_combination -2 * r * hqeq - q 1 * hgr

private theorem g_eq : g = 3 * r := by dsimp [r]; ring

-- The paper labels the cut endpoints on CD and DE by O and N. The reflected corner F
-- gives the point L on CD, and M is the midpoint of DE.

private theorem corner_C_CD {q : Plane} (hq : q 1 = r * (q 0 - 1)) :
    ⟪cornerNormal 2, q⟫_ℝ = (r * c + s) * q 0 + (r * c - s) / 2 := by
  rw [inner_coords]
  change (g * c + s) / 2 * q 0 + (g * s - c) / 2 * q 1 = _
  rw [hq]
  linear_combination s * (q 0 - 1) / 2 * hgr + c * q 0 / 2 * g_eq

private theorem corner_E_DE {q : Plane} (hq : q 1 = r * (-q 0 - 1)) :
    ⟪cornerNormal 4, q⟫_ℝ = (-r * c + s) * q 0 + (r * c + s) / 2 := by
  rw [inner_coords]
  change (-g * c + s) / 2 * q 0 + (-g * s - c) / 2 * q 1 = _
  rw [hq]
  linear_combination s * (q 0 + 1) / 2 * hgr - c * q 0 / 2 * g_eq

private theorem corner_reflect_B (q : Plane) :
    ⟪cornerNormal 1, reflectDE q⟫_ℝ = s * q 0 + c * q 1 := by
  rw [reflectDE_apply, inner_coords]
  change (g * c - s) / 2 * ((-1 / 2) * q 0 + g / 2 * q 1) +
    (g * s + c) / 2 * (g / 2 * q 0 + 1 / 2 * q 1) = _
  linear_combination (s * q 0 + c * q 1) / 4 * hg_sq

private theorem corner_reflect_F (q : Plane) :
    ⟪cornerNormal 5, reflectDE q⟫_ℝ = (g * c - s) / 2 * q 0 + (-g * s - c) / 2 * q 1 := by
  rw [reflectDE_apply, inner_coords]
  change (-g * c - s) / 2 * ((-1 / 2) * q 0 + g / 2 * q 1) +
    (-g * s + c) / 2 * (g / 2 * q 0 + 1 / 2 * q 1) = _
  linear_combination (-s * q 0 - c * q 1) / 4 * hg_sq

private theorem corner_F_reflected_CD {q : Plane} (hq : q 1 = r * (q 0 - 1)) :
    ⟪cornerNormal 5, reflectDE q⟫_ℝ = (r * c - s) * q 0 + (r * c + s) / 2 := by
  rw [corner_reflect_F, hq]
  linear_combination -s * (q 0 - 1) / 2 * hgr + c * q 0 / 2 * g_eq

private theorem reflectDE_support {q : Plane} (hq : q 1 = r * (-q 0 - 1)) :
    (reflectDE q) 0 = -q 0 - 1 / 2 ∧
      (reflectDE q) 1 = r * (-(reflectDE q) 0 - 1) := by
  have h₀ : (reflectDE q) 0 = -q 0 - 1 / 2 := by
    rw [reflectDE_apply]
    change (-1 / 2) * q 0 + (g / 2) * q 1 = _
    rw [hq]
    linear_combination (-q 0 - 1) / 2 * hgr
  refine ⟨h₀, ?_⟩
  rw [h₀, reflectDE_apply]
  change (g / 2) * q 0 + (1 / 2) * q 1 = _
  rw [hq]
  dsimp [r]
  ring

private theorem cd_contact_x_le {q : Plane} (hside : q 1 = r * (q 0 - 1))
    (hcut : ⟪cornerNormal 2, q⟫_ℝ ≤ 1 / 2) : q 0 ≤ 0.37131540 := by
  rw [corner_C_CD hside] at hcut
  by_contra! h
  have hp : 0 < r * c + s := by
    have hr := hr_pos
    norm_num [c, s]
    linarith only [hr]
  have hh := mul_lt_mul_of_pos_left h hp
  have hl := r_bounds.1
  norm_num [c, s, rlo] at hh hcut hl
  nlinarith only [hh, hcut, hl]

private theorem de_contact_x_ge {q : Plane} (hside : q 1 = r * (-q 0 - 1))
    (hcut : ⟪cornerNormal 4, q⟫_ℝ ≤ 1 / 2) : -0.36076754 ≤ q 0 := by
  rw [corner_E_DE hside] at hcut
  by_contra! h
  have hl := r_bounds.1
  have hp : 0 < r * c - s := by norm_num [rlo, c, s] at hl ⊢; linarith only [hl]
  have hh := mul_lt_mul_of_pos_left h hp
  norm_num [c, s, rlo] at hh hcut hl
  nlinarith only [hh, hcut, hl]

private theorem cd_contact_x_le_reflected {q : Plane} (hside : q 1 = r * (q 0 - 1))
    (hcut : ⟪cornerNormal 5, reflectDE q⟫_ℝ ≤ 1 / 2) : q 0 ≤ 0.36076754 := by
  rw [corner_F_reflected_CD hside] at hcut
  by_contra! h
  have hl := r_bounds.1
  have hp : 0 < r * c - s := by norm_num [rlo, c, s] at hl ⊢; linarith only [hl]
  have hh := mul_lt_mul_of_pos_left h hp
  norm_num [c, s, rlo] at hh hcut hl
  nlinarith only [hh, hcut, hl]

private noncomputable def slope (t : ℝ) : ℝ := -(2 * t) / (1 - t ^ 2)
private noncomputable def interceptShift (t : ℝ) : ℝ := (1 + t ^ 2) / (1 - t ^ 2)

/-- A diameter bound gives a supporting line of the unit disk about any member of the set.
The parameter `t` gives a unit normal by the rational half-angle formulas. -/
private theorem tangentLine {K : Set Plane} (hK : PairwiseUnitBound K)
    {p q : Plane} (hp : p ∈ K) (hq : q ∈ K) {t : ℝ} (ht : t ^ 2 < 1) :
    p 1 ≤ slope t * p 0 + interceptShift t + q 1 - slope t * q 0 := by
  let b := interceptShift t
  let a := slope t
  have hden : 0 < 1 - t ^ 2 := sub_pos.2 ht
  have hb : 0 < b := div_pos (by positivity) hden
  let u := pt (-a / b) (1 / b)
  have hu : ‖u‖ = 1 := by
    apply norm_one_coords
    change (-a / b) ^ 2 + (1 / b) ^ 2 = 1
    dsimp [a, b, slope, interceptShift]
    have hden' : (1:ℝ) + t ^ 2 ≠ 0 := by positivity
    field_simp [hden.ne', hden']
    ring
  have h := inner_sub_le_one hK hp hq hu
  simp only [inner_coords] at h
  change (-a / b) * p 0 + (1 / b) * p 1 - ((-a / b) * q 0 + (1 / b) * q 1) ≤ 1 at h
  have hEq : (-a / b) * p 0 + (1 / b) * p 1 - ((-a / b) * q 0 + (1 / b) * q 1) =
      (p 1 - q 1 - a * (p 0 - q 0)) / b := by ring
  rw [hEq, div_le_iff₀ hb] at h
  change p 1 ≤ a * p 0 + b + q 1 - a * q 0
  linarith

private theorem tangent_CD {K : Set Plane} (hK : PairwiseUnitBound K)
    {p q : Plane} (hp : p ∈ K) (hq : q ∈ K) {t x₀ B : ℝ} (ht : t ^ 2 < 1)
    (hside : q 1 = r * (q 0 - 1)) (hq₁ : q 0 ≤ 1 / 2) (hq₂ : q 0 ≤ x₀)
    (ha : slope t ≤ rlo)
    (hB : interceptShift t + rlo * (x₀ - 1) - slope t * x₀ ≤ B) :
    p 1 ≤ slope t * p 0 + B := by
  have h := tangentLine hK hp hq ht
  have hq' : q 1 ≤ rlo * (q 0 - 1) := by
    rw [hside]
    exact mul_le_mul_of_nonpos_right r_bounds.1 (by linarith)
  have hx := mul_le_mul_of_nonneg_left hq₂ (sub_nonneg.2 ha)
  linarith only [h, hq', hx, hB]

private theorem tangent_DE {K : Set Plane} (hK : PairwiseUnitBound K)
    {p q : Plane} (hp : p ∈ K) (hq : q ∈ K) {t x₀ B : ℝ} (ht : t ^ 2 < 1)
    (hside : q 1 = r * (-q 0 - 1)) (hq₁ : -(1 / 2) ≤ q 0) (hq₂ : x₀ ≤ q 0)
    (ha : -rlo ≤ slope t)
    (hB : interceptShift t + rlo * (-x₀ - 1) - slope t * x₀ ≤ B) :
    p 1 ≤ slope t * p 0 + B := by
  have h := tangentLine hK hp hq ht
  have hq' : q 1 ≤ rlo * (-q 0 - 1) := by
    rw [hside]
    exact mul_le_mul_of_nonpos_right r_bounds.1 (by linarith)
  have hx := mul_le_mul_of_nonpos_left hq₂ (by linarith : -rlo - slope t ≤ 0)
  linarith only [h, hq', hx, hB]

-- Upper and lower boundary lines are stored as (slope, intercept). The top uses the
-- rounded hexagon edges, four tangents from each contact side, and the final oblique cut.

private noncomputable def upper : Fin 11 → ℝ × ℝ :=
  ![(rhi, rhi),
    (slope (-0.2555), 0.573713897), (slope (-0.243), 0.570754036),
    (slope (-0.2305), 0.568470352), (slope (-0.218), 0.566847991),
    (0.385, 0.56360),
    (slope 0.187, 0.563594955), (slope 0.207, 0.564429335),
    (slope 0.227, 0.566909110), (slope 0.247, 0.571086248), (-rhi, rhi)]

private noncomputable def lower : Fin 4 → ℝ × ℝ :=
  ![(-rhi, -rhi), (rhi, -rhi),
    (-0.854439600 / 0.519550739, -0.500000002 / 0.519550739),
    (0.877163938 / 0.480191030, -0.500000002 / 0.480191030)]

private def cover : Set Plane :=
  {p | |p 0| ≤ 1 / 2 ∧ (∀ i, p 1 ≤ (upper i).1 * p 0 + (upper i).2) ∧
    ∀ i, (lower i).1 * p 0 + (lower i).2 ≤ p 1}

private theorem hex_enclosure {p : Plane} (hp : p ∈ hexagon) :
    |p 0| ≤ 1 / 2 ∧ (lower 0).1 * p 0 + (lower 0).2 ≤ p 1 ∧
      (lower 1).1 * p 0 + (lower 1).2 ≤ p 1 ∧
      p 1 ≤ (upper 0).1 * p 0 + (upper 0).2 ∧ p 1 ≤ (upper 10).1 * p 0 + (upper 10).2 := by
  obtain ⟨h, h₁, h₂, h₃, h₄⟩ := hexCoords hp
  have hPlus : 0 ≤ 1 + p 0 := by linarith [(abs_le.mp h).1]
  have hMinus : 0 ≤ 1 - p 0 := by linarith [(abs_le.mp h).2]
  have hu := mul_le_mul_of_nonneg_right r_bounds.2 hPlus
  have hv := mul_le_mul_of_nonneg_right r_bounds.2 hMinus
  dsimp [upper, lower]
  exact ⟨h, by linarith only [h₂, hu], by linarith only [h₁, hv],
    by linarith only [h₄, hu], by linarith only [h₃, hv]⟩

private theorem rounded_cap {p : Plane} {a b a' b' : ℝ}
    (hx : |p 0| ≤ 1) (hy : |p 1| ≤ 1)
    (ha : |a' - a| ≤ 0.000000001) (hb : |b' - b| ≤ 0.000000001)
    (hc : a * p 0 + b * p 1 ≤ 1 / 2) : a' * p 0 + b' * p 1 ≤ 0.500000002 := by
  have h₁ : (a'-a) * p 0 ≤ 0.000000001 := calc
    _ ≤ |(a'-a) * p 0| := le_abs_self _
    _ = |a'-a| * |p 0| := abs_mul _ _
    _ ≤ 0.000000001 * 1 := mul_le_mul ha hx (abs_nonneg _) (by norm_num)
    _ = _ := by ring
  have h₂ : (b'-b) * p 1 ≤ 0.000000001 := calc
    _ ≤ |(b'-b) * p 1| := le_abs_self _
    _ = |b'-b| * |p 1| := abs_mul _ _
    _ ≤ 0.000000001 * 1 := mul_le_mul hb hy (abs_nonneg _) (by norm_num)
    _ = _ := by ring
  linarith only [h₁, h₂, hc]

private theorem cap_enclosure {p : Plane} (hp : p ∈ hexagon)
    (hC : ⟪cornerNormal 2, p⟫_ℝ ≤ 1 / 2) (hE : ⟪cornerNormal 4, p⟫_ℝ ≤ 1 / 2) :
    (lower 2).1 * p 0 + (lower 2).2 ≤ p 1 ∧ (lower 3).1 * p 0 + (lower 3).2 ≤ p 1 := by
  obtain ⟨hx, hy₁, _, hy₂, _⟩ := hex_enclosure hp
  have hx₁ : |p 0| ≤ 1 := hx.trans (by norm_num)
  have hy₃ : |p 1| ≤ 1 := by
    apply abs_le.2
    constructor
    · norm_num [lower, rhi] at hy₁
      linarith only [hy₁, (abs_le.mp hx).2]
    · norm_num [upper, rhi] at hy₂
      linarith only [hy₂, (abs_le.mp hx).2]
  have hR := r_bounds
  norm_num [rlo, rhi] at hR
  simp only [inner_coords] at hC hE
  change (g * c + s) / 2 * p 0 + (g * s - c) / 2 * p 1 ≤ 1 / 2 at hC
  change (-g * c + s) / 2 * p 0 + (-g * s - c) / 2 * p 1 ≤ 1 / 2 at hE
  have hC' := rounded_cap hx₁ hy₃ (a' := 0.877163938) (b' := -0.480191030)
    (by rw [abs_le, g_eq]; norm_num [s, c]; constructor <;> linarith only [hR.1, hR.2])
    (by rw [abs_le, g_eq]; norm_num [s, c]; constructor <;> linarith only [hR.1, hR.2]) hC
  have hE' := rounded_cap hx₁ hy₃ (a' := -0.854439600) (b' := -0.519550739)
    (by rw [abs_le, g_eq]; norm_num [s, c]; constructor <;> linarith only [hR.1, hR.2])
    (by rw [abs_le, g_eq]; norm_num [s, c]; constructor <;> linarith only [hR.1, hR.2]) hE
  constructor
  · norm_num [lower]
    linarith only [hE']
  · norm_num [lower]
    linarith only [hC']

/-- The four consecutive supporting lines to the circular cut from the side CD. -/
private theorem le_cd_tangents {K : Set Plane} (hK : PairwiseUnitBound K) (hhex : K ⊆ hexagon)
    (hC : insideCorner K 2) {p q : Plane} (hp : p ∈ K) (hq : q ∈ K)
    (hside : q 1 = r * (q 0 - 1)) (j : Fin 4) :
    p 1 ≤ (upper (![(1 : Fin 11), 2, 3, 4] j)).1 * p 0 +
      (upper (![(1 : Fin 11), 2, 3, 4] j)).2 := by
  have hqx := (abs_le.mp (hexCoords (hhex hq)).1).2
  have hqO := cd_contact_x_le hside (hC _ hq)
  fin_cases j <;>
    simp only [upper, Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
    exact tangent_CD hK hp hq (by norm_num) hside hqx hqO
      (by norm_num [slope, rlo]) (by norm_num [slope, interceptShift, rlo])

/-- The four consecutive supporting lines to the circular cut from the side DE. -/
private theorem le_de_tangents {K : Set Plane} (hK : PairwiseUnitBound K) (hhex : K ⊆ hexagon)
    (hE : insideCorner K 4) {p q : Plane} (hp : p ∈ K) (hq : q ∈ K)
    (hside : q 1 = r * (-q 0 - 1)) (j : Fin 4) :
    p 1 ≤ (upper (![(6 : Fin 11), 7, 8, 9] j)).1 * p 0 +
      (upper (![(6 : Fin 11), 7, 8, 9] j)).2 := by
  have hqx := (abs_le.mp (hexCoords (hhex hq)).1).1
  have hqN := de_contact_x_ge hside (hE _ hq)
  fin_cases j <;>
    simp only [upper, Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
    exact tangent_DE hK hp hq (by norm_num) hside hqx hqN
      (by norm_num [slope, rlo]) (by norm_num [slope, interceptShift, rlo])

private theorem final_cut_of_B_reflected {p : Plane}
    (hO : p 1 ≤ slope (-0.218) * p 0 + 0.566847991)
    (hB : ⟪cornerNormal 1, reflectDE p⟫_ℝ ≤ 1 / 2) :
    p 1 ≤ 0.385 * p 0 + 0.56360 := by
  rw [corner_reflect_B] at hB
  norm_num [slope, s, c] at hO hB
  linarith only [hO, hB]

private theorem final_cut_of_F_reflected {K : Set Plane} (hK : PairwiseUnitBound K)
    (hhex : K ⊆ hexagon) {p q : Plane} (hp : p ∈ K) (hq : q ∈ K)
    (hside : q 1 = r * (q 0 - 1))
    (hN : p 1 ≤ slope 0.187 * p 0 + 0.563594955)
    (hF : ⟪cornerNormal 5, reflectDE q⟫_ℝ ≤ 1 / 2) :
    p 1 ≤ 0.385 * p 0 + 0.56360 := by
  have hqx := (abs_le.mp (hexCoords (hhex hq)).1).2
  have hL := tangent_CD hK hp hq (t := -0.187) (by norm_num) hside hqx
    (cd_contact_x_le_reflected hside hF) (by norm_num [slope, rlo])
    (show _ ≤ 0.563594955 by norm_num [slope, interceptShift, rlo])
  norm_num [slope] at hN hL
  linarith only [hN, hL]

private theorem final_cut_of_M {K : Set Plane} (hK : PairwiseUnitBound K)
    (hhex : K ⊆ hexagon) {p q : Plane} (hp : p ∈ K) (hq : q ∈ K)
    (hside : q 1 = r * (-q 0 - 1)) (hqM : -(1 / 4) ≤ q 0)
    (hO : p 1 ≤ slope (-0.218) * p 0 + 0.566847991) : p 1 ≤ 0.385 * p 0 + 0.56360 := by
  have hqx := (abs_le.mp (hexCoords (hhex hq)).1).1
  have hM := tangent_DE hK hp hq (t := 0.103) (by norm_num) hside hqx hqM
    (by norm_num [slope, rlo]) (show _ ≤ 0.536380592 by norm_num [slope, interceptShift, rlo])
  norm_num [slope] at hO hM
  linarith only [hO, hM]

private theorem mem_cover {K : Set Plane} (hK : PairwiseUnitBound K) (hhex : K ⊆ hexagon)
    (hC : insideCorner K 2) (hE : insideCorner K 4) {p q q' : Plane}
    (hp : p ∈ K) (hq : q ∈ K) (hq' : q' ∈ K)
    (hCD : q 1 = r * (q 0 - 1)) (hDE : q' 1 = r * (-q' 0 - 1))
    (hcut : p 1 ≤ 0.385 * p 0 + 0.56360) : p ∈ cover := by
  obtain ⟨hx, h₀, h₁, h₀', h₁'⟩ := hex_enclosure (hhex hp)
  obtain ⟨h₂, h₃⟩ := cap_enclosure (hhex hp) (hC _ hp) (hE _ hp)
  have ho := le_cd_tangents hK hhex hC hp hq hCD
  have hn := le_de_tangents hK hhex hE hp hq' hDE
  refine ⟨hx, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact h₀'
    · exact ho 0
    · exact ho 1
    · exact ho 2
    · exact ho 3
    · exact hcut
    · exact hn 0
    · exact hn 1
    · exact hn 2
    · exact hn 3
    · exact h₁'
  · intro i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
    · exact h₃

/-- Apply the three-way reflection argument from Reduction 3. The final half-space follows
from the missing reflected corner B, the cut from L, or the cut from M. In the last case
reflection lets us choose the side of M on which the contact lies. -/
private theorem exists_image_subset_cover {K : Set Plane} (hn : K.Nonempty)
    (hK : PairwiseUnitBound K) (hcomplete : ∀ z, (∀ y ∈ K, ‖z - y‖ ≤ 1) → z ∈ K)
    (hhex : K ⊆ hexagon) (hC : insideCorner K 2) (hE : insideCorner K 4) :
    ∃ e : Plane ≃ᵢ Plane, e '' K ⊆ cover := by
  obtain ⟨q, hq, hqside⟩ := support_CD hn hK hcomplete hhex
  obtain ⟨q', hq', hq'side⟩ := support_DE hn hK hcomplete hhex
  let e := reflectDE.toIsometryEquiv
  have hrefK := pairwise_image hK e
  have hrefhex : e '' K ⊆ hexagon := by
    rintro _ ⟨p, hp, rfl⟩
    exact reflect_hex (hhex hp)
  have hone (p : Plane) (hp : p ∈ K) : p 1 ≤ slope (-0.218) * p 0 + 0.566847991 :=
    le_cd_tangents hK hhex hC hp hq hqside 3
  have htwo (p : Plane) (hp : p ∈ K) : p 1 ≤ slope 0.187 * p 0 + 0.563594955 :=
    le_de_tangents hK hhex hE hp hq' hq'side 0
  have hidentity (hf : ∀ p ∈ K, p 1 ≤ 0.385 * p 0 + 0.56360) :
      ∃ e : Plane ≃ᵢ Plane, e '' K ⊆ cover := by
    refine ⟨IsometryEquiv.refl _, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact mem_cover hK hhex hC hE hp hq hq' hqside hq'side (hf _ hp)
  by_cases hE' : insideCorner (e '' K) 4
  · by_cases hC' : insideCorner (e '' K) 2
    · by_cases hqM : -(1 / 4) ≤ q' 0
      · exact hidentity fun p hp =>
          final_cut_of_M hK hhex hp hq' hq'side hqM (hone _ hp)
      · push Not at hqM
        refine ⟨e, ?_⟩
        obtain ⟨rq, hrq, hrqside⟩ :=
          support_CD (hn.image e) hrefK (complete_image hcomplete e) hrefhex
        have hrq' : reflectDE q' ∈ e '' K := mem_image_of_mem e hq'
        obtain ⟨hx, hy⟩ := reflectDE_support hq'side
        have hrqM : -(1 / 4) ≤ (reflectDE q') 0 := by linarith only [hx, hqM]
        intro p hp
        apply mem_cover hrefK hrefhex hC' hE' hp hrq hrq' hrqside hy
        exact final_cut_of_M hrefK hrefhex hp hrq' hy hrqM
          (le_cd_tangents hrefK hrefhex hC' hp hrq hrqside 3)
    · have hF' := (corner_pair hrefK 2).resolve_left hC'
      exact hidentity fun p hp => final_cut_of_F_reflected hK hhex hp hq hqside
        (htwo _ hp) (hF' _ (mem_image_of_mem e hq))
  · have hB' := (corner_pair hrefK 1).resolve_right hE'
    exact hidentity fun p hp => final_cut_of_B_reflected (hone _ hp) (hB' _ (mem_image_of_mem e hp))

private theorem zero_mem_cover : (0 : Plane) ∈ cover := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> intro i <;> fin_cases i <;>
    norm_num [upper, lower, slope, rhi]

private theorem convex_cover : Convex ℝ cover := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hpx, hpu, hpl⟩ := hp
  obtain ⟨hqx, hqu, hql⟩ := hq
  refine ⟨?_, ?_, ?_⟩
  · change |a * p 0 + b * q 0| ≤ 1 / 2
    have hp' := abs_le.mp hpx
    have hq' := abs_le.mp hqx
    apply abs_le.2
    refine ⟨?_, ?_⟩
    · have h₁ := mul_le_mul_of_nonneg_left hp'.1 ha
      have h₂ := mul_le_mul_of_nonneg_left hq'.1 hb
      linear_combination h₁ + h₂ + hab / 2
    · have h₁ := mul_le_mul_of_nonneg_left hp'.2 ha
      have h₂ := mul_le_mul_of_nonneg_left hq'.2 hb
      linear_combination h₁ + h₂ + hab / 2
  · intro i
    change a * p 1 + b * q 1 ≤ (upper i).1 * (a * p 0 + b * q 0) + (upper i).2
    have hp' := mul_le_mul_of_nonneg_left (hpu i) ha
    have hq' := mul_le_mul_of_nonneg_left (hqu i) hb
    linear_combination hp' + hq' + (upper i).2 * hab
  · intro i
    change (lower i).1 * (a * p 0 + b * q 0) + (lower i).2 ≤ a * p 1 + b * q 1
    have hp' := mul_le_mul_of_nonneg_left (hpl i) ha
    have hq' := mul_le_mul_of_nonneg_left (hql i) hb
    linear_combination hp' + hq' - (lower i).2 * hab

private theorem universal_cover : IsUniversalConvexCover cover := by
  refine ⟨⟨0, zero_mem_cover⟩, convex_cover, ?_⟩
  rintro K ⟨hkn, _, hdiam⟩
  have hbounded : Bornology.IsBounded K := by
    by_contra h
    exact zero_ne_one ((Metric.diam_eq_zero_of_unbounded h).symm.trans hdiam)
  have hbound : PairwiseUnitBound K := by
    intro p hp q hq
    rw [← dist_eq_norm, ← hdiam]
    exact Metric.dist_le_diam_of_mem hbounded hp hq
  obtain ⟨L, hKL, hL, hcomplete⟩ := exists_complete hbound
  have hLn := hkn.mono hKL
  obtain ⟨e, hhex⟩ := exists_image_subset_hexagon hLn hL hcomplete
  have hLe := pairwise_image hL e
  obtain ⟨f, htrunc, hC, hE⟩ := exists_image_subset_truncated hLe hhex
  obtain ⟨j, hj⟩ := exists_image_subset_cover ((hLn.image e).image f)
    (pairwise_image hLe f) (complete_image (complete_image hcomplete e) f) htrunc hC hE
  refine ⟨(e.trans f).trans j, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact hj (mem_image_of_mem j (mem_image_of_mem f (mem_image_of_mem e (hKL hp))))

/-! ## Certifying the area -/

-- Split the horizontal interval into strips near the changes of active boundary line.
-- Each strip uses one valid lower and one valid upper bound across its entire width.

private noncomputable def breakpoints : Fin 15 → ℝ :=
  ![-0.5, -0.360768, -0.118594, -0.098044, -0.077070, -0.055726, -0.044643, -0.000007,
    0, 0.018549, 0.053754, 0.088067, 0.122216, 0.371315, 0.5]

private def stripSides : Fin 14 → Fin 11 × Fin 4 :=
  ![(0, 2), (0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (6, 1), (7, 1), (8, 1),
    (9, 1), (10, 1), (10, 3)]

-- Enlarge the strip vertically by one unit in the eighth decimal place at each end,
-- so the closed polygon is contained in the union of the open vertical sections.

private noncomputable def stripLo (i : Fin 14) : ℝ × ℝ :=
  let v := lower (stripSides i).2
  (v.1, v.2 - 0.00000001)

private noncomputable def stripHi (i : Fin 14) : ℝ × ℝ :=
  let v := upper (stripSides i).1
  (v.1, v.2 + 0.00000001)

private noncomputable def strip (i : Fin 14) : Set (ℝ × ℝ) :=
  regionBetween (fun x => (stripLo i).1 * x + (stripLo i).2)
    (fun x => (stripHi i).1 * x + (stripHi i).2)
    (Icc (breakpoints i.castSucc) (breakpoints i.succ))

private noncomputable def trapezoidArea (a b : ℝ) (lo hi : ℝ × ℝ) :=
  (b - a) * ((hi.1 - lo.1) * (b + a) / 2 + hi.2 - lo.2)

private theorem affine_le_on_Icc {a b x : ℝ} {lo hi : ℝ × ℝ}
    (hx : x ∈ Icc a b) (ha : lo.1 * a + lo.2 ≤ hi.1 * a + hi.2)
    (hb : lo.1 * b + lo.2 ≤ hi.1 * b + hi.2) : lo.1 * x + lo.2 ≤ hi.1 * x + hi.2 := by
  rcases le_total lo.1 hi.1 with hc | hc
  · have h := mul_le_mul_of_nonneg_left hx.1 (sub_nonneg.2 hc)
    linarith only [ha, h]
  · have h := mul_le_mul_of_nonpos_left hx.2 (sub_nonpos.2 hc)
    linarith only [hb, h]

private theorem volume_trapezoid {a b : ℝ} {lo hi : ℝ × ℝ} (hab : a ≤ b)
    (ha : lo.1 * a + lo.2 ≤ hi.1 * a + hi.2) (hb : lo.1 * b + lo.2 ≤ hi.1 * b + hi.2) :
    volume (regionBetween (fun x => lo.1 * x + lo.2) (fun x => hi.1 * x + hi.2) (Icc a b))
      = ENNReal.ofReal (trapezoidArea a b lo hi) := by
  have hlo : Continuous (fun x : ℝ => lo.1 * x + lo.2) := by fun_prop
  have hhi : Continuous (fun x : ℝ => hi.1 * x + hi.2) := by fun_prop
  change (volume.prod volume) _ = _
  rw [volume_regionBetween_eq_integral hlo.integrableOn_Icc hhi.integrableOn_Icc
    measurableSet_Icc (fun _ hx => affine_le_on_Icc hx ha hb),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  congr 1
  change (∫ x in a..b, (hi.1 * x + hi.2) - (lo.1 * x + lo.2)) = _
  have h : (fun x : ℝ => (hi.1 * x + hi.2) - (lo.1 * x + lo.2)) =
      fun x => (hi.1 - lo.1) * x + (hi.2 - lo.2) := by
    ext x
    ring
  have hlinear : Continuous (fun x : ℝ => (hi.1 - lo.1) * x) := by fun_prop
  have hconst : Continuous (fun _ : ℝ => hi.2 - lo.2) := continuous_const
  rw [h, intervalIntegral.integral_add (hlinear.intervalIntegrable a b)
    (hconst.intervalIntegrable a b), intervalIntegral.integral_const_mul,
    integral_id, intervalIntegral.integral_const]
  simp [trapezoidArea, smul_eq_mul]
  ring

private theorem mem_adjacent_interval {n : ℕ} (f : Fin (n + 2) → ℝ) {x : ℝ}
    (ha : f 0 ≤ x) (hb : x ≤ f (Fin.last (n + 1))) :
    ∃ i : Fin (n + 1), x ∈ Icc (f i.castSucc) (f i.succ) := by
  induction n with
  | zero => exact ⟨0, ha, hb⟩
  | succ n ih =>
    by_cases h : x ≤ f (Fin.last (n + 1)).castSucc
    · obtain ⟨i, hi₁, hi₂⟩ := ih (f := fun j => f j.castSucc) ha h
      exact ⟨i.castSucc, hi₁, by simpa only [Fin.succ_castSucc] using hi₂⟩
    · exact ⟨Fin.last (n + 1), le_of_not_ge h, hb⟩

private def planeCoords : Plane ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

private theorem cover_sub_strips : cover ⊆ planeCoords ⁻¹' (⋃ i, strip i) := by
  intro p hp
  obtain ⟨hpx, hpu, hpl⟩ := hp
  have hfirst : breakpoints 0 = -(1 / 2) := by norm_num [breakpoints]
  have hlast : breakpoints (Fin.last 14) = 1 / 2 := by
    change breakpoints 14 = _
    norm_num [breakpoints]
  obtain ⟨i, hi⟩ := mem_adjacent_interval (n := 13) breakpoints (hfirst ▸ (abs_le.mp hpx).1)
    (hlast ▸ (abs_le.mp hpx).2)
  refine mem_iUnion.2 ⟨i, hi, ?_, ?_⟩
  · change (stripLo i).1 * p 0 + (stripLo i).2 < p 1
    dsimp [stripLo]
    linarith only [hpl (stripSides i).2]
  · change p 1 < (stripHi i).1 * p 0 + (stripHi i).2
    dsimp [stripHi]
    linarith only [hpu (stripSides i).1]

-- Rational upper bounds for the fourteen trapezoid areas, in left-to-right order.

private noncomputable def stripAreaBound : Fin 14 → ℝ :=
  ![0.081233461, 0.212614431, 0.021152311, 0.022071574, 0.022948188,
    0.012105430, 0.049968477, 0.000007987, 0.020997399, 0.038911059,
    0.036693527, 0.035256059, 0.216656422, 0.073512717]

private theorem volume_strip_le (i : Fin 14) :
    volume (strip i) ≤ ENNReal.ofReal (stripAreaBound i) := by
  rw [strip, volume_trapezoid]
  · apply ENNReal.ofReal_le_ofReal
    fin_cases i <;> norm_num [breakpoints, stripLo, stripHi, stripSides, stripAreaBound,
      lower, upper, slope, rhi, trapezoidArea, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]
  all_goals fin_cases i <;> norm_num [breakpoints, stripLo, stripHi, stripSides,
    lower, upper, slope, rhi, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]

private theorem area_cover_le : planarArea cover ≤ ENNReal.ofReal 0.844137708398 := by
  have hmeasure : MeasurePreserving planeCoords volume volume :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).trans
      (volume_preserving_finTwoArrow ℝ)
  have h₀ : planarArea cover ≤ volume (⋃ i, strip i) := by
    rw [← hmeasure.measure_preimage_equiv]
    exact measure_mono cover_sub_strips
  apply h₀.trans ((measure_iUnion_le _).trans ?_)
  rw [tsum_fintype]
  apply (Finset.sum_le_sum (fun i _ => volume_strip_le i)).trans
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
    fin_cases i <;> norm_num [stripAreaBound])]
  apply ENNReal.ofReal_le_ofReal
  norm_num [stripAreaBound, Fin.sum_univ_succ]

@[expose] public noncomputable section

/-- **Statement of Hansen's corrected upper bound.** This proposition states that the Lebesgue
universal covering constant, the infimum of the areas of the nonempty convex sets in the Euclidean
plane that contain a congruent copy of every nonempty convex planar set of diameter $1$, is at most
$0.844137708398$.

This is Hansen's finite-decimal upper bound, as corrected by Baez, Bagdasaryan and Gibbs. -/
def hansen1992CorrectedBBG2015UpperBound : Prop :=
  lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal 0.844137708398

/-- **Hansen's upper bound for Lebesgue's covering problem, as corrected.** The Lebesgue universal
covering constant, the infimum of the areas of the nonempty convex sets in the Euclidean plane that
contain a congruent copy of every nonempty convex planar set of diameter $1$, is at most
$0.844137708398$.

Source: Hansen (1992), corrected in Baez, Bagdasaryan and Gibbs (2015). -/
theorem hansen1992CorrectedBBG2015UpperBound_holds : hansen1992CorrectedBBG2015UpperBound := by
  refine (sInf_le (show planarArea cover ∈ admissibleCoverAreas from
    ⟨cover, universal_cover, rfl⟩)).trans area_cover_le

end

end MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted
