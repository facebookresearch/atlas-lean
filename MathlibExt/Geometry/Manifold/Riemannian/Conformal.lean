/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Conformal scaling of smooth Riemannian metrics

This module provides conformal scaling of smooth Riemannian metrics on general
vector bundles and the conformal class of a metric on a manifold.

Main definitions:
* `Bundle.ContMDiffRiemannianMetric.ofLE`: the same metric with lower smoothness.
* `Bundle.ContMDiffRiemannianMetric.conformalScale`: scaling by a smooth positive function.
* `Manifold.conformalClass`: metrics pointwise proportional to a given metric.

Main results:
* `Bundle.ContMDiffRiemannianMetric.pos_of_inner_eq_mul`: the factor is positive.
* `Manifold.mem_conformalClass_iff_exp`: membership via an exponential factor.
* `Manifold.self_mem_conformalClass`: every metric lies in its own class.
* `Manifold.conformalScale_mem_conformalClass`: scaled metrics lie in the class.
* `Manifold.mem_conformalClass_symm` and `Manifold.mem_conformalClass_trans`.

Sources:
* Curry and Gover, *An introduction to conformal geometry and tractor calculus*
  (arXiv:1412.7559), Definition 1.1 (the conformal class consists of the metrics `Ω² g`
  with `Ω` smooth and positive)
* Brendle and Marques, *Recent progress on the Yamabe problem* (arXiv:1010.4960), §1
  (metrics `g` and `g₀` are conformal if `g = e^{2w} g₀` with `w` smooth)
* Madani, *Equivariant Yamabe problem and Hebey-Vaugon conjecture*,
  J. Funct. Anal. 258 (2010) (conformal metrics written `e^f g` with `f ∈ C^∞(M)`)
-/

@[expose] public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

namespace Bundle

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n n' : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- The same smooth Riemannian metric, viewed with a lower smoothness index. -/
def ContMDiffRiemannianMetric.ofLE (g : ContMDiffRiemannianMetric IB n F E)
    {m : ℕ∞ω} (h : m ≤ n) : ContMDiffRiemannianMetric IB m F E where
  inner := g.inner
  symm := g.symm
  pos := g.pos
  isVonNBounded := g.isVonNBounded
  contMDiff := g.contMDiff.of_le h

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- The inner product of the lowered metric equals the original inner product. -/
@[simp]
theorem ContMDiffRiemannianMetric.ofLE_inner
    (g : ContMDiffRiemannianMetric IB n F E) {m : ℕ∞ω} (h : m ≤ n) (b : B) :
    (g.ofLE h).inner b = g.inner b :=
  rfl

/-- Conformal scaling of a metric by a smooth positive function `u`. -/
def ContMDiffRiemannianMetric.conformalScale
    (g : ContMDiffRiemannianMetric IB n F E) (u : B → ℝ)
    (hu : ContMDiff IB 𝓘(ℝ) n u) (hpos : ∀ b, 0 < u b) :
    ContMDiffRiemannianMetric IB n F E where
  inner := fun b ↦ u b • g.inner b
  symm := by
    intro b v w
    have h1 : (u b • g.inner b) v w = u b * g.inner b v w := by
      simp [smul_eq_mul]
    have h2 : (u b • g.inner b) w v = u b * g.inner b w v := by
      simp [smul_eq_mul]
    rw [h1, h2, g.symm b v w]
  pos := by
    intro b v hv
    have h1 : (u b • g.inner b) v v = u b * g.inner b v v := by
      simp [smul_eq_mul]
    rw [h1]
    exact mul_pos (hpos b) (g.pos b v hv)
  isVonNBounded := by
    intro b
    have hub : 0 < u b := hpos b
    have hub_ne : u b ≠ 0 := ne_of_gt hub
    have hsqrt_pos : 0 < Real.sqrt (u b) := Real.sqrt_pos.mpr hub
    have hsqrt_ne : Real.sqrt (u b) ≠ 0 := ne_of_gt hsqrt_pos
    have hsqrt_sq : Real.sqrt (u b) ^ 2 = u b := Real.sq_sqrt (le_of_lt hub)
    set c : ℝ := (Real.sqrt (u b))⁻¹ with hc_def
    have hc_ne : c ≠ 0 := by
      rw [hc_def]
      exact inv_ne_zero hsqrt_ne
    have hcc : c * c = (u b)⁻¹ := by
      rw [hc_def, ← mul_inv_rev, ← pow_two, hsqrt_sq]
    have hcu : u b * (c * c) = 1 := by
      rw [hcc, mul_inv_cancel₀ hub_ne]
    have hcinv : c⁻¹ = Real.sqrt (u b) := by
      rw [hc_def, inv_inv]
    have hback : ∀ t : ℝ, c⁻¹ * (c⁻¹ * t) = u b * t := by
      intro t
      rw [hcinv, ← mul_assoc, ← pow_two, hsqrt_sq]
    have hfwd : ∀ t : ℝ, u b * (c * (c * t)) = t := by
      intro t
      have hring : u b * (c * (c * t)) = (u b * (c * c)) * t := by ring
      rw [hring, hcu, one_mul]
    have hscale : ∀ (a : ℝ) (v w : E b),
        g.inner b (a • v) (a • w) = a * (a * g.inner b v w) := by
      intro a v w
      simp [smul_eq_mul]
    have hsmul_inner : ∀ v w : E b,
        (u b • g.inner b) v w = u b * g.inner b v w := by
      intro v w
      simp [smul_eq_mul]
    let L : E b →L[ℝ] E b := c • ContinuousLinearMap.id ℝ (E b)
    have hL_apply : ∀ v : E b, L v = c • v := by
      intro v
      change (c • ContinuousLinearMap.id ℝ (E b)) v = c • v
      simp
    have hLinv : ∀ w : E b, L (c⁻¹ • w) = w := by
      intro w
      rw [hL_apply, smul_smul, mul_inv_cancel₀ hc_ne, one_smul]
    have hset : {v : E b | (u b • g.inner b) v v < 1} =
        L '' {v : E b | g.inner b v v < 1} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · intro hw
        rw [hsmul_inner] at hw
        refine ⟨c⁻¹ • w, ?_, hLinv w⟩
        have hsc : g.inner b (c⁻¹ • w) (c⁻¹ • w) =
            c⁻¹ * (c⁻¹ * g.inner b w w) := hscale c⁻¹ w w
        rw [hsc, hback]
        exact hw
      · intro hw
        obtain ⟨v, hv, hvw⟩ := hw
        subst hvw
        rw [hsmul_inner]
        have hsc : g.inner b (L v) (L v) = c * (c * g.inner b v v) := by
          rw [hL_apply v]
          exact hscale c v v
        rw [hsc, hfwd]
        exact hv
    rw [hset]
    exact Bornology.IsVonNBounded.image (g.isVonNBounded b) L
  contMDiff := ContMDiff.smul_section hu g.contMDiff

omit [∀ b, IsTopologicalAddGroup (E b)] in
/-- The inner product of the conformally scaled metric. -/
@[simp]
theorem ContMDiffRiemannianMetric.conformalScale_inner_apply
    (g : ContMDiffRiemannianMetric IB n F E) (u : B → ℝ)
    (hu : ContMDiff IB 𝓘(ℝ) n u) (hpos : ∀ b, 0 < u b) (b : B)
    (v w : E b) :
    (g.conformalScale u hu hpos).inner b v w = u b * g.inner b v w := by
  change (u b • g.inner b) v w = u b * g.inner b v w
  simp [smul_eq_mul]

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- A scalar factor relating two metrics at a point with a nonzero vector is positive. -/
theorem ContMDiffRiemannianMetric.pos_of_inner_eq_mul
    (g g' : ContMDiffRiemannianMetric IB n F E) {u : B → ℝ} {b : B}
    (h : ∀ v w : E b, g'.inner b v w = u b * g.inner b v w)
    (hb : ∃ v : E b, v ≠ 0) : 0 < u b := by
  obtain ⟨v, hv⟩ := hb
  have hpos1 : 0 < g'.inner b v v := g'.pos b v hv
  have hpos2 : 0 < g.inner b v v := g.pos b v hv
  have hmul : 0 < u b * g.inner b v v := by
    rw [← h v v]
    exact hpos1
  exact pos_of_mul_pos_left hmul (le_of_lt hpos2)

end Bundle

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g g' g'' : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

/-- The conformal class of a `C^∞` metric: metrics pointwise proportional by a smooth
positive factor. -/
def conformalClass
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    Set (ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :=
  {g' |
    ∃ u : M → ℝ,
      ContMDiff I 𝓘(ℝ) ∞ u ∧
        (∀ x, 0 < u x) ∧
          ∀ x (v w : TangentSpace I x), g'.inner x v w = u x * g.inner x v w}

/-- Membership in the conformal class via a smooth exponential factor. -/
theorem mem_conformalClass_iff_exp :
    g' ∈ conformalClass g ↔
      ∃ f : M → ℝ,
        ContMDiff I 𝓘(ℝ) ∞ f ∧
          ∀ x (v w : TangentSpace I x),
            g'.inner x v w = Real.exp (f x) * g.inner x v w := by
  constructor
  · intro hmem
    obtain ⟨u, hu, hpos, hinner⟩ := hmem
    refine ⟨fun x ↦ Real.log (u x), ?_, ?_⟩
    · refine fun x ↦ ?_
      have hu_at : ContMDiffAt I 𝓘(ℝ) ∞ u x := hu.contMDiffAt
      have hlog_at : ContDiffAt ℝ ∞ Real.log (u x) :=
        (Real.contDiffAt_log).mpr (ne_of_gt (hpos x))
      exact hlog_at.comp_contMDiffAt hu_at
    · intro x v w
      change g'.inner x v w = Real.exp (Real.log (u x)) * g.inner x v w
      have hexp : Real.exp (Real.log (u x)) = u x :=
        Real.exp_log (hpos x)
      rw [hexp]
      exact hinner x v w
  · intro hexp
    obtain ⟨f, hf, hinner⟩ := hexp
    have hexp_smooth : ContMDiff I 𝓘(ℝ) ∞ (Real.exp ∘ f) :=
      ContDiff.comp_contMDiff Real.contDiff_exp hf
    refine ⟨fun x ↦ Real.exp (f x), hexp_smooth, fun x ↦ Real.exp_pos _, ?_⟩
    intro x v w
    exact hinner x v w

/-- Every metric lies in its own conformal class. -/
theorem self_mem_conformalClass : g ∈ conformalClass g := by
  refine ⟨fun _ ↦ 1, contMDiff_const, fun _ ↦ zero_lt_one, ?_⟩
  intro x v w
  simp

/-- A conformally scaled metric lies in the conformal class. -/
theorem conformalScale_mem_conformalClass (u : M → ℝ)
    (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hpos : ∀ x, 0 < u x) :
    g.conformalScale u hu hpos ∈ conformalClass g := by
  refine ⟨u, hu, hpos, ?_⟩
  intro x v w
  exact ContMDiffRiemannianMetric.conformalScale_inner_apply g u hu hpos x v w

/-- Symmetry of the conformal relation. -/
theorem mem_conformalClass_symm :
    g' ∈ conformalClass g → g ∈ conformalClass g' := by
  intro hmem
  obtain ⟨u, hu, hpos, hinner⟩ := hmem
  have hne : ∀ x, u x ≠ 0 := fun x ↦ ne_of_gt (hpos x)
  have hu_inv : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ (u x)⁻¹ := hu.inv₀ hne
  refine ⟨fun x ↦ (u x)⁻¹, hu_inv, fun x ↦ inv_pos.mpr (hpos x), ?_⟩
  intro x v w
  change g.inner x v w = (u x)⁻¹ * g'.inner x v w
  have h1 : g'.inner x v w = u x * g.inner x v w := hinner x v w
  have h2 : (u x)⁻¹ * g'.inner x v w = g.inner x v w := by
    rw [h1, ← mul_assoc, inv_mul_cancel₀ (hne x), one_mul]
  exact h2.symm

/-- Transitivity of the conformal relation. -/
theorem mem_conformalClass_trans :
    g' ∈ conformalClass g → g'' ∈ conformalClass g' → g'' ∈ conformalClass g := by
  intro h1mem h2mem
  obtain ⟨u1, hu1, hpos1, hinner1⟩ := h1mem
  obtain ⟨u2, hu2, hpos2, hinner2⟩ := h2mem
  have hu : ContMDiff I 𝓘(ℝ) ∞ (u2 * u1) := hu2.mul hu1
  refine ⟨u2 * u1, hu, fun x ↦ mul_pos (hpos2 x) (hpos1 x), ?_⟩
  intro x v w
  have hshow : (u2 * u1) x = u2 x * u1 x := rfl
  rw [hshow, hinner2 x v w, hinner1 x v w, mul_assoc]

end Manifold
