/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

@[expose] public section

/-!
# Birkhoff–James orthogonality and the duality mapping

In a normed space `E` over `𝕜` (here `𝕜 = ℝ` or `ℂ`), an element `x` is
**Birkhoff–James orthogonal** to `y` if `x` is a shortest vector on the affine
line `x + 𝕜 • y` through `x` in the direction of `y`:
`‖x‖ ≤ ‖x + c • y‖` for every scalar `c`. This is the correct notion of
orthogonality for general normed spaces: it is the one that characterizes
best approximation from one-dimensional subspaces, and the one that appears
in the study of smoothness and strict convexity of the norm.

This is a companion to the Hahn–Banach material of the v1 book
(`v1/Atlas/IntroductionToFunctionalAnalysis/code/HahnBanach.lean`): the book
proves the Hahn–Banach extension theorem and the existence of norming
functionals, but none of its 72 targets states anything about
Birkhoff–James orthogonality or the duality mapping. The results here are
also not in the pinned Mathlib (which has Hahn–Banach and the Fréchet–Riesz
representation, but no Birkhoff–James orthogonality).

Main results:

* `BirkhoffJamesOrthogonal`: the definition.
* `birkhoffJamesOrthogonal_self_iff`: `x` is Birkhoff–James orthogonal to
  itself if and only if `x = 0`.
* `birkhoffJamesOrthogonal_smul_left_right`: Birkhoff–James orthogonality
  is homogeneous in both arguments.
* `birkhoffJamesOrthogonal_iff_exists_norming`: for `x ≠ 0`, `x` is
  Birkhoff–James orthogonal to `y` if and only if there is a norming
  functional `f` of `x` (so `‖f‖ = 1` and `f x = ‖x‖`) with `f y = 0`.
  The proof passes to the quotient `E / 𝕜 ∙ y`, where the quotient norm of
  `x` is exactly `‖x‖` by Birkhoff–James orthogonality, and applies
  Hahn–Banach (`exists_dual_vector`) there.
* `dualityMapping`: the duality set `J(x) = {f | f x = ‖x‖ ^ 2, ‖f‖ = ‖x‖}`,
  with `dualityMapping_nonempty` and
  `birkhoffJamesOrthogonal_iff_exists_dualityMapping`: `x` is
  Birkhoff–James orthogonal to `y` if and only if some `f ∈ J(x)` vanishes
  at `y`.
* `birkhoffJamesOrthogonal_iff_inner_eq_zero`: in an inner product space,
  Birkhoff–James orthogonality is ordinary inner-product orthogonality.

References: G. Birkhoff, "Orthogonality in linear metric spaces"
(Duke Math. J., 1935); R. C. James, "Orthogonality and linear functionals in
normed linear spaces" (Trans. Amer. Math. Soc., 1947).
-/

namespace MathlibExt.Analysis.FunctionalAnalysis.BirkhoffJames

open RCLike Submodule

section Normed

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Birkhoff–James orthogonality**: `x` is Birkhoff–James orthogonal to `y`
if `x` is a shortest vector on the affine line `x + 𝕜 • y`. -/
def BirkhoffJamesOrthogonal (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (x y : E) : Prop :=
  ∀ c : 𝕜, ‖x‖ ≤ ‖x + c • y‖

/-- `0` is Birkhoff–James orthogonal to every vector. -/
theorem birkhoffJamesOrthogonal_zero_left (y : E) :
    BirkhoffJamesOrthogonal 𝕜 (0 : E) y := by
  intro c
  simp

/-- Every vector is Birkhoff–James orthogonal to `0`. -/
theorem birkhoffJamesOrthogonal_zero_right (x : E) :
    BirkhoffJamesOrthogonal 𝕜 x 0 := by
  intro c
  simp

/-- A vector is Birkhoff–James orthogonal to itself if and only if it is `0`. -/
theorem birkhoffJamesOrthogonal_self_iff {x : E} :
    BirkhoffJamesOrthogonal 𝕜 x x ↔ x = 0 := by
  constructor
  · intro h
    have hx := h (-1 : 𝕜)
    rw [neg_one_smul, add_neg_cancel, norm_zero] at hx
    exact norm_le_zero_iff.mp hx
  · intro hx
    subst hx
    exact birkhoffJamesOrthogonal_zero_left 0

/-- Birkhoff–James orthogonality is homogeneous in both arguments. -/
theorem birkhoffJamesOrthogonal_smul_left_right {x y : E} {a b : 𝕜}
    (h : BirkhoffJamesOrthogonal 𝕜 x y) :
    BirkhoffJamesOrthogonal 𝕜 (a • x) (b • y) := by
  intro c
  by_cases ha : a = 0
  · simp [ha]
  · have hmul : a * (c * b / a) = c * b := by field_simp
    calc ‖a • x‖ = ‖a‖ * ‖x‖ := norm_smul a x
      _ ≤ ‖a‖ * ‖x + (c * b / a) • y‖ :=
          mul_le_mul_of_nonneg_left (h _) (norm_nonneg _)
      _ = ‖a • x + c • (b • y)‖ := by
          have heq : a • x + c • (b • y) = a • (x + (c * b / a) • y) := by
            simp only [smul_add, smul_smul]
            rw [hmul]
          rw [heq, norm_smul]

/-- If a norming functional of `x` vanishes at `y`, then `x` is
Birkhoff–James orthogonal to `y`. -/
theorem birkhoffJamesOrthogonal_of_exists_norming {x y : E} {f : E →L[𝕜] 𝕜}
    (hf : ‖f‖ = 1) (hfx : f x = ‖x‖) (hfy : f y = 0) :
    BirkhoffJamesOrthogonal 𝕜 x y := by
  intro c
  have hcalc : f (x + c • y) = ((‖x‖ : ℝ) : 𝕜) := by
    rw [map_add, map_smul, hfx, hfy, smul_zero, add_zero]
  calc ‖x‖ = ‖f (x + c • y)‖ := by
        rw [hcalc, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    _ ≤ ‖f‖ * ‖x + c • y‖ := f.le_opNorm _
    _ = ‖x + c • y‖ := by rw [hf, one_mul]

/-- The converse: if `x ≠ 0` is Birkhoff–James orthogonal to `y`, there is a
norming functional of `x` vanishing at `y`. The proof passes to the quotient
`E / 𝕜 ∙ y`, where the quotient norm of `x` is exactly `‖x‖` by
Birkhoff–James orthogonality, and applies Hahn–Banach there. -/
theorem exists_norming_of_birkhoffJamesOrthogonal {x y : E} (hx : x ≠ 0)
    (h : BirkhoffJamesOrthogonal 𝕜 x y) :
    ∃ f : E →L[𝕜] 𝕜, ‖f‖ = 1 ∧ f x = ‖x‖ ∧ f y = 0 := by
  have hMclosed : IsClosed ((𝕜 ∙ y : Submodule 𝕜 E) : Set E) :=
    Submodule.closed_of_finiteDimensional _
  have hqnorm : ∀ z : E,
      ‖(𝕜 ∙ y : Submodule 𝕜 E).mkQL z‖ ≤ ‖z‖ := by
    intro z
    rw [Submodule.mkQL_apply, Submodule.mkQ_apply]
    exact Submodule.Quotient.norm_mk_le _ z
  have hqnormx : ‖(𝕜 ∙ y : Submodule 𝕜 E).mkQL x‖ = ‖x‖ := by
    apply le_antisymm (hqnorm x)
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨m, hm, hmlt⟩ := Submodule.Quotient.norm_mk_lt
      (S := 𝕜 ∙ y) (Submodule.Quotient.mk x) hε
    have hmem : m - x ∈ (𝕜 ∙ y : Submodule 𝕜 E) :=
      (Submodule.Quotient.eq (𝕜 ∙ y)).mp hm
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hmx : m = c • y + x := sub_eq_iff_eq_add.mp hc.symm
    have hle : ‖x‖ ≤ ‖m‖ := by
      rw [hmx, add_comm]
      exact h c
    have hqx : (𝕜 ∙ y : Submodule 𝕜 E).mkQL x = Submodule.Quotient.mk x := rfl
    rw [hqx]
    linarith [hle, hmlt]
  obtain ⟨g, hg1, hg2⟩ := exists_dual_vector 𝕜 ((𝕜 ∙ y : Submodule 𝕜 E).mkQL x)
    (by rw [hqnormx]; exact norm_ne_zero_iff.mpr hx)
  have hqop : ‖(𝕜 ∙ y : Submodule 𝕜 E).mkQL‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    rw [one_mul]
    exact hqnorm z
  refine ⟨g.comp (𝕜 ∙ y : Submodule 𝕜 E).mkQL, ?_, ?_, ?_⟩
  · apply le_antisymm _ _
    · calc ‖g.comp (𝕜 ∙ y : Submodule 𝕜 E).mkQL‖
          ≤ ‖g‖ * ‖(𝕜 ∙ y : Submodule 𝕜 E).mkQL‖ :=
            ContinuousLinearMap.opNorm_comp_le g _
        _ ≤ 1 * 1 := mul_le_mul hg1.le hqop (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · have hle : ‖(g.comp (𝕜 ∙ y : Submodule 𝕜 E).mkQL) x‖
          ≤ ‖g.comp (𝕜 ∙ y : Submodule 𝕜 E).mkQL‖ * ‖x‖ :=
            (g.comp (𝕜 ∙ y : Submodule 𝕜 E).mkQL).le_opNorm x
      have hgx : (g.comp (𝕜 ∙ y : Submodule 𝕜 E).mkQL) x = ((‖x‖ : ℝ) : 𝕜) := by
        rw [ContinuousLinearMap.comp_apply, hg2, hqnormx]
      have hnormcoe : ‖((‖x‖ : ℝ) : 𝕜)‖ = ‖x‖ := by
        rw [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
      rw [hgx, hnormcoe] at hle
      have hpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
      have hle' : ‖x‖ * 1 ≤ ‖x‖ * ‖g.comp (𝕜 ∙ y : Submodule 𝕜 E).mkQL‖ := by
        rw [mul_one]
        rwa [mul_comm ‖g.comp (𝕜 ∙ y : Submodule 𝕜 E).mkQL‖ ‖x‖] at hle
      exact le_of_mul_le_mul_left hle' hpos
  · rw [ContinuousLinearMap.comp_apply, hg2, hqnormx]
  · have hqy : (𝕜 ∙ y : Submodule 𝕜 E).mkQL y = 0 := by
      have hy : y ∈ (𝕜 ∙ y : Submodule 𝕜 E) :=
        Submodule.mem_span_singleton_self y
      rw [Submodule.mkQL_apply, Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero (𝕜 ∙ y)).mpr hy
    rw [ContinuousLinearMap.comp_apply, hqy, map_zero]

/-- For `x ≠ 0`, Birkhoff–James orthogonality to `y` is equivalent to the
existence of a norming functional of `x` vanishing at `y`. -/
theorem birkhoffJamesOrthogonal_iff_exists_norming {x y : E} (hx : x ≠ 0) :
    BirkhoffJamesOrthogonal 𝕜 x y ↔
      ∃ f : E →L[𝕜] 𝕜, ‖f‖ = 1 ∧ f x = ‖x‖ ∧ f y = 0 :=
  ⟨exists_norming_of_birkhoffJamesOrthogonal hx,
    fun ⟨_f, hf, hfx, hfy⟩ => birkhoffJamesOrthogonal_of_exists_norming hf hfx hfy⟩

/-- The **duality mapping** (duality set) at `x`: the functionals `f` with
`f x = ‖x‖ ^ 2` and `‖f‖ = ‖x‖`. At `x = 0` this is the singleton `{0}`. -/
def dualityMapping (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (x : E) : Set (E →L[𝕜] 𝕜) :=
  {f | f x = ((‖x‖ ^ 2 : ℝ) : 𝕜) ∧ ‖f‖ = ‖x‖}

/-- The duality mapping is nonempty at every point: take a Hahn–Banach norming
functional and scale it by `‖x‖`. -/
theorem dualityMapping_nonempty (x : E) : (dualityMapping 𝕜 x).Nonempty := by
  by_cases hx : x = 0
  · subst hx
    exact ⟨0, by simp [dualityMapping]⟩
  · obtain ⟨g, hg1, hg2⟩ :=
      exists_dual_vector 𝕜 x (norm_ne_zero_iff.mpr hx)
    refine ⟨(‖x‖ : 𝕜) • g, ?_, ?_⟩
    · rw [smul_apply, hg2, smul_eq_mul, ← RCLike.ofReal_mul,
        ← pow_two]
    · rw [norm_smul, hg1, mul_one, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]

/-- Birkhoff–James orthogonality to `y` is equivalent to the existence of a
functional in the duality mapping at `x` that vanishes at `y`. -/
theorem birkhoffJamesOrthogonal_iff_exists_dualityMapping {x y : E} :
    BirkhoffJamesOrthogonal 𝕜 x y ↔ ∃ f ∈ dualityMapping 𝕜 x, f y = 0 := by
  constructor
  · intro h
    by_cases hx : x = 0
    · subst hx
      exact ⟨0, by simp [dualityMapping], by simp⟩
    · obtain ⟨f₀, hf₀1, hf₀x, hf₀y⟩ :=
        exists_norming_of_birkhoffJamesOrthogonal hx h
      refine ⟨(‖x‖ : 𝕜) • f₀, ⟨?_, ?_⟩, ?_⟩
      · rw [smul_apply, hf₀x, smul_eq_mul, ← RCLike.ofReal_mul,
          ← pow_two]
      · rw [norm_smul, hf₀1, mul_one, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
      · rw [smul_apply, hf₀y, smul_zero]
  · rintro ⟨f, hfmem, hfy⟩
    obtain ⟨hfx, hfnorm⟩ := hfmem
    intro c
    by_cases hx : x = 0
    · subst hx
      simp
    · have hfxc : f (x + c • y) = ((‖x‖ ^ 2 : ℝ) : 𝕜) := by
        rw [map_add, map_smul, hfy, smul_zero, add_zero]
        exact hfx
      have hnorm : ‖f (x + c • y)‖ = ‖x‖ ^ 2 := by
        rw [hfxc, RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg _)]
      have hle : ‖x‖ ^ 2 ≤ ‖x‖ * ‖x + c • y‖ := by
        rw [← hnorm, ← hfnorm]
        exact f.le_opNorm _
      have hpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
      have hle' : ‖x‖ * ‖x‖ ≤ ‖x‖ * ‖x + c • y‖ := by
        rw [← sq]
        exact hle
      exact le_of_mul_le_mul_left hle' hpos

end Normed

section InnerProduct

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- In an inner product space, Birkhoff–James orthogonality is ordinary
inner-product orthogonality. -/
theorem birkhoffJamesOrthogonal_iff_inner_eq_zero {x y : E} :
    BirkhoffJamesOrthogonal 𝕜 x y ↔ ⟪x, y⟫ = 0 := by
  constructor
  · intro h
    have key : ∀ {w : E}, BirkhoffJamesOrthogonal 𝕜 x w →
        RCLike.re ⟪x, w⟫ = 0 := by
      intro w hw
      by_contra hB
      have hpos : (0 : ℝ) < ‖w‖ ^ 2 + 1 := by linarith [sq_nonneg ‖w‖]
      have hne : (‖w‖ ^ 2 + 1 : ℝ) ≠ 0 := ne_of_gt hpos
      have hineq :
          (0 : ℝ) ≤ 2 * (-RCLike.re ⟪x, w⟫ / (‖w‖ ^ 2 + 1)) * RCLike.re ⟪x, w⟫
            + (-RCLike.re ⟪x, w⟫ / (‖w‖ ^ 2 + 1)) ^ 2 * ‖w‖ ^ 2 := by
        have hle := hw (((-RCLike.re ⟪x, w⟫ / (‖w‖ ^ 2 + 1) : ℝ) : 𝕜))
        have hsq :
            ‖x‖ ^ 2 ≤ ‖x + ((-RCLike.re ⟪x, w⟫ / (‖w‖ ^ 2 + 1) : ℝ) : 𝕜) • w‖ ^ 2 := by
          rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
          exact hle
        rw [norm_add_sq (𝕜 := 𝕜)] at hsq
        have hinner :
            RCLike.re ⟪x, ((-RCLike.re ⟪x, w⟫ / (‖w‖ ^ 2 + 1) : ℝ) : 𝕜) • w⟫
              = (-RCLike.re ⟪x, w⟫ / (‖w‖ ^ 2 + 1)) * RCLike.re ⟪x, w⟫ := by
          rw [inner_smul_right (𝕜 := 𝕜), RCLike.re_ofReal_mul]
        have hnorm : ‖(((-RCLike.re ⟪x, w⟫ / (‖w‖ ^ 2 + 1) : ℝ) : 𝕜)) • w‖ ^ 2
            = (-RCLike.re ⟪x, w⟫ / (‖w‖ ^ 2 + 1)) ^ 2 * ‖w‖ ^ 2 := by
          rw [norm_smul, RCLike.norm_ofReal, mul_pow, sq_abs]
        rw [hinner, hnorm] at hsq
        linarith [hsq]
      have h2 : (0 : ℝ) ≤ -RCLike.re ⟪x, w⟫ ^ 2 * (‖w‖ ^ 2 + 2) := by
        have hmul := mul_le_mul_of_nonneg_right hineq (sq_nonneg (‖w‖ ^ 2 + 1))
        have heq : (2 * (-RCLike.re ⟪x, w⟫ / (‖w‖ ^ 2 + 1)) * RCLike.re ⟪x, w⟫
            + (-RCLike.re ⟪x, w⟫ / (‖w‖ ^ 2 + 1)) ^ 2 * ‖w‖ ^ 2) * (‖w‖ ^ 2 + 1) ^ 2
            = -RCLike.re ⟪x, w⟫ ^ 2 * (‖w‖ ^ 2 + 2) := by
          field_simp
          ring
        rw [heq, zero_mul] at hmul
        exact hmul
      have hB2 : (0 : ℝ) < RCLike.re ⟪x, w⟫ ^ 2 := sq_pos_of_ne_zero hB
      have hpos2 : (0 : ℝ) < RCLike.re ⟪x, w⟫ ^ 2 * (‖w‖ ^ 2 + 2) :=
        mul_pos hB2 (by linarith [sq_nonneg ‖w‖])
      have hneg : -RCLike.re ⟪x, w⟫ ^ 2 * (‖w‖ ^ 2 + 2) < 0 := by
        linarith [hpos2]
      linarith
    have hre : RCLike.re ⟪x, y⟫ = 0 := key h
    have him : RCLike.im ⟪x, y⟫ = 0 := by
      have hI : BirkhoffJamesOrthogonal 𝕜 x ((RCLike.I : 𝕜) • y) := by
        have hI0 := birkhoffJamesOrthogonal_smul_left_right (a := (1 : 𝕜))
          (b := (RCLike.I : 𝕜)) h
        rwa [one_smul] at hI0
      have hIre := key hI
      rw [inner_smul_right (𝕜 := 𝕜), RCLike.I_mul_re] at hIre
      exact neg_eq_zero.mp hIre
    rw [← RCLike.re_add_im ⟪x, y⟫, hre, him]
    simp
  · intro hz c
    have hsq : ‖x‖ ^ 2 ≤ ‖x + c • y‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := 𝕜)]
      have hinner : RCLike.re ⟪x, c • y⟫ = 0 := by
        rw [inner_smul_right (𝕜 := 𝕜), hz, mul_zero]
        exact map_zero _
      rw [hinner]
      have hnn : (0 : ℝ) ≤ ‖c • y‖ ^ 2 := sq_nonneg _
      linarith
    exact le_of_sq_le_sq hsq (norm_nonneg _)

end InnerProduct

end MathlibExt.Analysis.FunctionalAnalysis.BirkhoffJames
