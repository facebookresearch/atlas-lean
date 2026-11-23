/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Disjoint circles are Möbius-equivalent to concentric circles

Two disjoint circles in `ℂ` are mapped onto two concentric circles by a linear fractional
(Möbius) transformation (`Complex.exists_smul_sphere_eq_concentric_of_disjoint`). Möbius
transformations are the elements of `GL (Fin 2) ℂ` acting on the Riemann sphere `OnePoint ℂ`
(`OnePoint.instGLAction`), and a circle of `ℂ` is seen in `OnePoint ℂ` through the coercion
`ℂ → OnePoint ℂ`. The images are equal to the target circles, so "onto", not just "into".

Scope: a circle here is a genuine circle, `Metric.sphere a r` with `0 < r`. Texts that count
straight lines as circles through `∞` when discussing linear transformations would also include
a circle and a disjoint line; that case is not covered by this statement.

The proof finds two points `p ≠ q` on the line of centres that are symmetric with respect to
both circles. With `d = ‖b - a‖`, disjointness gives `4 r² d² < (d² + r² - s²)²`, so
`d² l² - (d² + r² - s²) l + r² = 0` has two distinct real roots `l₁, l₂`, and
`p = a + l₁ (b - a)`, `q = a + l₂ (b - a)`. Each circle is then a circle of Apollonius for `p`
and `q`, so `z ↦ (z - p) / (z - q)` maps it onto a circle centred at `0`. Mathlib has the Möbius
action on `OnePoint ℂ`, but no lemma on images of circles under it, no Apollonius-circle or
symmetric-points lemma, and no statement of this theorem.

Rubric-guided revision of v1 ComplexVariables target 07
(`Lecture6.nonintersecting_circles_concentric` in `v1/Atlas/ComplexVariables/code/Lecture6.lean`
at commit `6191bf1ba03d204784385ef5be2472be88035b93`). The archived formalization worked in a
chapter namespace with project-local `Circle` (shadowing Mathlib's `Circle`),
`GeneralizedCircle` and `MoebiusTransformation` types, stated its conclusion with a pole-skipping
`MapsSetTo` predicate whose agreement with `T(A) = A'` on the Riemann sphere was argued only
informally, and needed `maxHeartbeats 800000` for a long symmetric-points proof. Here circles are
`Metric.sphere`, Möbius maps act through Mathlib's `OnePoint.instGLAction`, the conclusion is
equality of images in `OnePoint ℂ`, and no option is raised. The archived formalization and its
original license/provenance remain in `v1/` (the original license text is `v1/LICENSE`).
-/

set_option autoImplicit false

open Metric
open scoped Pointwise

namespace Complex

/-- If `μ₁ * μ₂ * ‖v‖ ^ 2 = ρ ^ 2` and `μ₁ ≠ μ₂`, then `p = c + μ₁ v` and `q = c + μ₂ v` are
symmetric with respect to the circle of centre `c` and radius `ρ`, and the Möbius transformation
`z ↦ (z - p) / (z - q)` maps this circle onto the circle of centre `0` and radius `√(μ₁ / μ₂)`. -/
private lemma smul_coe_sphere_eq_sphere_zero {g : GL (Fin 2) ℂ} {c v : ℂ} {μ₁ μ₂ ρ : ℝ}
    (h00 : g 0 0 = 1) (h01 : g 0 1 = -(c + μ₁ * v)) (h10 : g 1 0 = 1)
    (h11 : g 1 1 = -(c + μ₂ * v)) (hρ : 0 < ρ) (h : μ₁ * μ₂ * ‖v‖ ^ 2 = ρ ^ 2)
    (hne : μ₁ ≠ μ₂) :
    0 < √(μ₁ / μ₂) ∧
      g • ((↑) '' sphere c ρ : Set (OnePoint ℂ)) =
        ((↑) '' sphere (0 : ℂ) √(μ₁ / μ₂) : Set (OnePoint ℂ)) := by
  have hv : 0 < ‖v‖ ^ 2 := by
    refine (sq_nonneg _).lt_of_ne fun hv ↦ ?_
    rw [← hv, mul_zero] at h
    exact (pow_pos hρ 2).ne h
  have hμ : 0 < μ₁ * μ₂ := by nlinarith
  have hμ₂ : μ₂ ≠ 0 := by rintro rfl; simp at hμ
  have hk : 0 < μ₁ / μ₂ := div_pos_iff.mpr (mul_pos_iff.mp hμ)
  refine ⟨Real.sqrt_pos.mpr hk, ?_⟩
  -- Apollonius: `μ₂ ‖z - p‖² - μ₁ ‖z - q‖² = (μ₂ - μ₁) (‖z - c‖² - ρ²)`.
  have key (z : ℂ) : μ₂ * ‖z - (c + μ₁ * v)‖ ^ 2 - μ₁ * ‖z - (c + μ₂ * v)‖ ^ 2 =
      (μ₂ - μ₁) * (‖z - c‖ ^ 2 - ρ ^ 2) := by
    rw [← h]
    simp only [Complex.sq_norm, normSq_apply, sub_re, add_re, mul_re, ofReal_re, ofReal_im, sub_im,
      add_im, mul_im]
    ring
  have hmem (z : ℂ) (hz : z - (c + μ₂ * v) ≠ 0) :
      ‖(z - (c + μ₁ * v)) / (z - (c + μ₂ * v))‖ = √(μ₁ / μ₂) ↔ ‖z - c‖ = ρ := by
    rw [norm_div, div_eq_iff (norm_ne_zero_iff.mpr hz), ← sq_eq_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)), ← sq_eq_sq₀ (norm_nonneg _) hρ.le,
      mul_pow, Real.sq_sqrt hk.le, div_mul_eq_mul_div, eq_div_iff hμ₂]
    have := key z
    constructor
    · intro h'
      have h'' : (μ₂ - μ₁) * (‖z - c‖ ^ 2 - ρ ^ 2) = 0 := by linear_combination h' - this
      rcases mul_eq_zero.mp h'' with h'' | h''
      · exact absurd (sub_eq_zero.mp h'').symm hne
      · linarith
    · intro h'
      rw [h', sub_self, mul_zero] at this
      linarith
  suffices H : ∀ x : OnePoint ℂ, x ∈ ((↑) '' sphere c ρ : Set (OnePoint ℂ)) ↔
      g • x ∈ ((↑) '' sphere (0 : ℂ) √(μ₁ / μ₂) : Set (OnePoint ℂ)) by
    ext w
    rw [Set.mem_smul_set_iff_inv_smul_mem, H, smul_inv_smul]
  intro x
  cases x with
  | infty =>
    -- `∞` is not on the circle, and its image `1` is not on the image circle.
    rw [OnePoint.smul_infty_eq_ite, h10, h00]
    simp only [one_ne_zero, ↓reduceIte, div_one]
    rw [OnePoint.coe_injective.mem_set_image, mem_sphere_zero_iff_norm, norm_one, eq_comm,
      Real.sqrt_eq_one, div_eq_one_iff_eq hμ₂]
    exact iff_of_false OnePoint.infty_notMem_image_coe hne
  | coe z =>
    rw [OnePoint.smul_some_eq_ite, h00, h01, h10, h11]
    simp only [one_mul, ← sub_eq_add_neg]
    split_ifs with hz
    · -- The pole `q` is not on the circle.
      rw [OnePoint.coe_injective.mem_set_image, mem_sphere_iff_norm]
      refine iff_of_false (fun hzc ↦ ?_) OnePoint.infty_notMem_image_coe
      rw [sub_eq_zero.mp hz, add_sub_cancel_left, norm_mul, norm_real, Real.norm_eq_abs] at hzc
      have h' : μ₂ * ‖v‖ ^ 2 * (μ₁ - μ₂) = 0 := by
        linear_combination h - (|μ₂| * ‖v‖ + ρ) * hzc + ‖v‖ ^ 2 * sq_abs μ₂
      rcases mul_eq_zero.mp h' with h' | h'
      · exact mul_ne_zero hμ₂ hv.ne' h'
      · exact hne (sub_eq_zero.mp h')
    · rw [OnePoint.coe_injective.mem_set_image, OnePoint.coe_injective.mem_set_image,
        mem_sphere_iff_norm, mem_sphere_zero_iff_norm]
      exact (hmem z hz).symm

/-- **Disjoint circles are Möbius-equivalent to concentric circles.** If two circles in `ℂ`
(of positive radius) do not intersect, then some linear fractional transformation, that is, some
element of `GL (Fin 2) ℂ` acting on the Riemann sphere `OnePoint ℂ`, maps them onto two concentric
circles. Both circles are genuine circles; the case of a circle and a disjoint straight line is
not covered. -/
public theorem exists_smul_sphere_eq_concentric_of_disjoint {a b : ℂ} {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) (hab : Disjoint (sphere a r) (sphere b s)) :
    ∃ (g : GL (Fin 2) ℂ) (c : ℂ) (r' s' : ℝ), 0 < r' ∧ 0 < s' ∧
      g • ((↑) '' sphere a r : Set (OnePoint ℂ)) = ((↑) '' sphere c r' : Set (OnePoint ℂ)) ∧
      g • ((↑) '' sphere b s : Set (OnePoint ℂ)) = ((↑) '' sphere c s' : Set (OnePoint ℂ)) := by
  rcases eq_or_ne a b with rfl | hne
  · exact ⟨1, a, r, s, hr, hs, one_smul _ _, one_smul _ _⟩
  obtain ⟨d, hd_def⟩ : ∃ d, ‖b - a‖ = d := ⟨_, rfl⟩
  have hd : 0 < d := hd_def ▸ norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  -- Disjointness: the distance `d` of the centres is not in `[|r - s|, r + s]`.
  have hD : 4 * r ^ 2 * d ^ 2 < (d ^ 2 + r ^ 2 - s ^ 2) ^ 2 := by
    by_contra! hD
    -- Otherwise the circles meet at `a + (x + y i) (b - a) / d`.
    obtain ⟨x, hx⟩ : ∃ x : ℝ, 2 * d * x = d ^ 2 + r ^ 2 - s ^ 2 :=
      ⟨_, mul_div_cancel₀ _ (by positivity)⟩
    have hxr : x ^ 2 ≤ r ^ 2 := by
      have hx2 : 4 * d ^ 2 * x ^ 2 = (d ^ 2 + r ^ 2 - s ^ 2) ^ 2 := by rw [← hx]; ring
      refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < 4 * d ^ 2)
      linarith
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y ^ 2 = r ^ 2 - x ^ 2 :=
      ⟨√(r ^ 2 - x ^ 2), Real.sq_sqrt (by linarith)⟩
    have hd' : (d : ℂ) ≠ 0 := ofReal_ne_zero.mpr hd.ne'
    have he : ‖(b - a) / (d : ℂ)‖ = 1 := by
      rw [norm_div, norm_real, Real.norm_of_nonneg hd.le, hd_def, div_self hd.ne']
    have hde : (d : ℂ) * ((b - a) / d) = b - a := mul_div_cancel₀ _ hd'
    have hzA : a + ((x : ℂ) + y * I) * ((b - a) / d) ∈ sphere a r := by
      rw [mem_sphere_iff_norm, add_sub_cancel_left, norm_mul, he, mul_one, norm_add_mul_I, hy,
        add_sub_cancel, Real.sqrt_sq hr.le]
    have hzB : a + ((x : ℂ) + y * I) * ((b - a) / d) ∈ sphere b s := by
      have hzb : a + ((x : ℂ) + y * I) * ((b - a) / d) - b =
          (((x - d : ℝ) : ℂ) + y * I) * ((b - a) / d) := by
        push_cast
        linear_combination hde
      rw [mem_sphere_iff_norm, hzb, norm_mul, he, mul_one, norm_add_mul_I,
        show (x - d) ^ 2 + y ^ 2 = s ^ 2 by linear_combination hy - hx, Real.sqrt_sq hs.le]
    exact Set.disjoint_left.mp hab hzA hzB
  -- The common symmetric points are `a + lᵢ (b - a)`, where `l₁, l₂` solve
  -- `l₁ l₂ d² = r²` and `(l₁ - 1) (l₂ - 1) d² = s²`.
  obtain ⟨δ, hδ, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ^ 2 = (d ^ 2 + r ^ 2 - s ^ 2) ^ 2 - 4 * r ^ 2 * d ^ 2 :=
    ⟨_, Real.sqrt_pos.mpr (by linarith), Real.sq_sqrt (by linarith)⟩
  obtain ⟨l₁, hl₁⟩ : ∃ l : ℝ, 2 * d ^ 2 * l = d ^ 2 + r ^ 2 - s ^ 2 + δ :=
    ⟨_, mul_div_cancel₀ _ (by positivity)⟩
  obtain ⟨l₂, hl₂⟩ : ∃ l : ℝ, 2 * d ^ 2 * l = d ^ 2 + r ^ 2 - s ^ 2 - δ :=
    ⟨_, mul_div_cancel₀ _ (by positivity)⟩
  have hl : l₁ ≠ l₂ := by
    rintro rfl
    linarith
  have hd4 : (4 * d ^ 2 : ℝ) ≠ 0 := by positivity
  have hA : l₁ * l₂ * ‖b - a‖ ^ 2 = r ^ 2 := by
    rw [hd_def]
    refine mul_left_cancel₀ hd4 ?_
    linear_combination (2 * d ^ 2 * l₂) * hl₁ + (d ^ 2 + r ^ 2 - s ^ 2 + δ) * hl₂ - hδ2
  have hB : (l₁ - 1) * (l₂ - 1) * ‖b - a‖ ^ 2 = s ^ 2 := by
    rw [hd_def]
    refine mul_left_cancel₀ hd4 ?_
    linear_combination (2 * d ^ 2 * l₂ - 2 * d ^ 2) * hl₁ +
      (d ^ 2 + r ^ 2 - s ^ 2 + δ - 2 * d ^ 2) * hl₂ - hδ2
  -- The Möbius transformation `z ↦ (z - p) / (z - q)`.
  have hdet : (!![1, -(a + l₁ * (b - a)); 1, -(a + l₂ * (b - a))] :
      Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of, show (1 : ℂ) * -(a + l₂ * (b - a)) - -(a + l₁ * (b - a)) * 1 =
      ↑(l₁ - l₂) * (b - a) by push_cast; ring]
    exact mul_ne_zero (ofReal_ne_zero.mpr (sub_ne_zero.mpr hl)) (sub_ne_zero.mpr hne.symm)
  set g := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have h00 : g 0 0 = 1 := by simp [g]
  have h01 : g 0 1 = -(a + l₁ * (b - a)) := by simp [g]
  have h10 : g 1 0 = 1 := by simp [g]
  have h11 : g 1 1 = -(a + l₂ * (b - a)) := by simp [g]
  obtain ⟨hrA, hgA⟩ := smul_coe_sphere_eq_sphere_zero h00 h01 h10 h11 hr hA hl
  obtain ⟨hrB, hgB⟩ := smul_coe_sphere_eq_sphere_zero (c := b) (v := b - a) (μ₁ := l₁ - 1)
    (μ₂ := l₂ - 1) h00 (by rw [h01]; push_cast; ring) h10 (by rw [h11]; push_cast; ring) hs hB
    (fun h ↦ hl (by linarith))
  exact ⟨g, 0, _, _, hrA, hrB, hgA, hgB⟩

end Complex
