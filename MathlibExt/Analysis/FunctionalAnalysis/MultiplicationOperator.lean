/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UrysohnsLemma

import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Ring

/-!
# Multiplication operators on `C(X, 𝕜)`

For a compact space `X` and `φ : C(X, 𝕜)`, multiplication sends `f` to `φ * f`.
The operator is Mathlib's `ContinuousLinearMap.mul`. Its spectrum is the range of
`φ`, and it is invertible exactly when `φ` vanishes nowhere. These results use
Mathlib's unit reflection for the left regular representation together with
`ContinuousMap.spectrum_eq_range`.

When `X` is also Hausdorff, `μ` is an eigenvalue exactly when the fiber
`φ ⁻¹' {μ}` has nonempty interior. This criterion uses a nonzero continuous
eigenvector in one direction and a Urysohn bump function in the other.

These are derived supporting results for continuous-function operators. They are
companions to the archived functional-analysis operator/spectrum context, rather
than imports of named v1 multiplication-operator targets. The archived sources
are preserved. No precise external textbook locator is asserted here.

## Main declarations

* `mulCLM` : the multiplication operator `M_φ` on `C(X, 𝕜)`.
* `mulCLM_apply`, `mulCLM_mul`, `mulCLM_one` : its action and the
  homomorphism laws.
* `spectrum_mulCLM` : `spectrum 𝕜 (mulCLM φ) = Set.range φ`.
* `isUnit_mulCLM_iff` : `M_φ` is a unit iff `φ` vanishes nowhere.
* `hasEigenvalue_mulCLM_iff` : `μ` is an eigenvalue of `M_φ` iff
  `interior (φ ⁻¹' {μ})` is nonempty.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.MultiplicationOperator

open Set Filter Topology
open scoped ContinuousMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- **The multiplication operator on continuous functions.** Let $X$ be a compact topological
space, let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $C(X, \mathbb{K})$ be the Banach
algebra of continuous functions $X \to \mathbb{K}$ with the supremum norm. For
$\varphi \in C(X, \mathbb{K})$, the multiplication operator $M_\varphi$ is the bounded linear
operator on $C(X, \mathbb{K})$ given by $M_\varphi f = \varphi f$. -/
noncomputable def mulCLM (φ : C(X, 𝕜)) : C(X, 𝕜) →L[𝕜] C(X, 𝕜) :=
  ContinuousLinearMap.mul 𝕜 C(X, 𝕜) φ

@[simp]
theorem mulCLM_apply (φ f : C(X, 𝕜)) : mulCLM φ f = φ * f :=
  ContinuousLinearMap.mul_apply' 𝕜 C(X, 𝕜) φ f

theorem mulCLM_mul (φ ψ : C(X, 𝕜)) : mulCLM (φ * ψ) = mulCLM φ * mulCLM ψ := by
  ext f
  simp [mulCLM_apply, mul_assoc]

theorem mulCLM_one : mulCLM (1 : C(X, 𝕜)) = 1 := by
  ext f
  simp [mulCLM_apply]

theorem mulCLM_sub (φ ψ : C(X, 𝕜)) : mulCLM (φ - ψ) = mulCLM φ - mulCLM ψ := by
  ext f
  simp [mulCLM_apply, sub_mul]

/-- **Multiplication by a constant on continuous functions.** Let $X$ be a compact topological
space, let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $\mu \in \mathbb{K}$. The
multiplication operator on $C(X, \mathbb{K})$ by the constant function with value $\mu$ equals
$\mu$ times the identity operator. -/
theorem mulCLM_algebraMap (μ : 𝕜) :
    mulCLM (algebraMap 𝕜 C(X, 𝕜) μ) = algebraMap 𝕜 (C(X, 𝕜) →L[𝕜] C(X, 𝕜)) μ := by
  ext f x
  simp [mulCLM_apply, Algebra.algebraMap_eq_smul_one, smul_eq_mul]

/-- The left regular representation reflects units, also as a continuous endomorphism. -/
private theorem isUnit_mulCLM_iff_isUnit (φ : C(X, 𝕜)) :
    IsUnit (mulCLM φ) ↔ IsUnit φ := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
  change IsUnit (Algebra.lmul 𝕜 C(X, 𝕜) φ) ↔ IsUnit φ
  exact Algebra.lmul_isUnit_iff

/-- **Spectrum of a multiplication operator.** Let $X$ be a compact topological space, let
$\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $\varphi \in C(X, \mathbb{K})$. The spectrum
of the multiplication operator $M_\varphi f = \varphi f$, as an element of the algebra of bounded
linear operators on $C(X, \mathbb{K})$, is the range $\varphi(X)$ of $\varphi$. -/
theorem spectrum_mulCLM (φ : C(X, 𝕜)) : spectrum 𝕜 (mulCLM φ) = Set.range φ := by
  rw [← ContinuousMap.spectrum_eq_range φ]
  ext μ
  rw [spectrum.mem_iff, spectrum.mem_iff]
  have hdecomp : algebraMap 𝕜 (C(X, 𝕜) →L[𝕜] C(X, 𝕜)) μ - mulCLM φ =
      mulCLM (algebraMap 𝕜 C(X, 𝕜) μ - φ) := by
    rw [← mulCLM_algebraMap, mulCLM_sub]
  rw [hdecomp, isUnit_mulCLM_iff_isUnit]

/-- **Invertibility of a multiplication operator.** Let $X$ be a compact topological space, let
$\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $\varphi \in C(X, \mathbb{K})$. The
multiplication operator $M_\varphi f = \varphi f$ is invertible in the algebra of bounded linear
operators on $C(X, \mathbb{K})$ if and only if $\varphi(x) \neq 0$ for every $x \in X$. -/
theorem isUnit_mulCLM_iff (φ : C(X, 𝕜)) :
    IsUnit (mulCLM φ) ↔ ∀ x : X, φ x ≠ 0 :=
  (isUnit_mulCLM_iff_isUnit φ).trans (ContinuousMap.isUnit_iff_forall_ne_zero φ)

/-- **Eigenvalues of a multiplication operator.** Let $X$ be a compact Hausdorff space, let
$\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $\varphi \in C(X, \mathbb{K})$ and let
$\mu \in \mathbb{K}$. Then $\mu$ is an eigenvalue of the multiplication operator
$M_\varphi f = \varphi f$ on $C(X, \mathbb{K})$ if and only if the level set
$\varphi^{-1}(\{\mu\})$ has nonempty interior. -/
theorem hasEigenvalue_mulCLM_iff [T2Space X] (φ : C(X, 𝕜)) (μ : 𝕜) :
    Module.End.HasEigenvalue (mulCLM φ : C(X, 𝕜) →ₗ[𝕜] C(X, 𝕜)) μ ↔
      (interior (φ ⁻¹' {μ})).Nonempty := by
  constructor
  · intro hμ
    obtain ⟨v, hv_mem, hv0⟩ := hμ.exists_hasEigenvector
    have hv : mulCLM φ v = μ • v :=
      (Module.End.mem_eigenspace_iff).mp hv_mem
    obtain ⟨x₀, hx₀⟩ : ∃ x : X, v x ≠ 0 := by
      by_contra h
      push Not at h
      exact hv0 (ContinuousMap.ext fun x => by simpa using h x)
    have hsub : {x : X | v x ≠ 0} ⊆ φ ⁻¹' {μ} := by
      intro x hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      have hx2 := ContinuousMap.congr_fun hv x
      simp only [mulCLM_apply, ContinuousMap.mul_apply, ContinuousMap.smul_apply,
        smul_eq_mul] at hx2
      exact mul_right_cancel₀ hx hx2
    have hopen : IsOpen {x : X | v x ≠ 0} :=
      isOpen_compl_singleton.preimage v.continuous
    refine ⟨x₀, ?_⟩
    rw [mem_interior_iff_mem_nhds]
    exact mem_of_superset (hopen.mem_nhds hx₀) hsub
  · intro hInt
    obtain ⟨x₀, hx₀⟩ := hInt
    have hφ : ∀ x ∈ interior (φ ⁻¹' {μ}), φ x = μ := by
      intro x hx
      simpa using interior_subset hx
    have hdisj : Disjoint (interior (φ ⁻¹' {μ}))ᶜ {x₀} := by
      rw [Set.disjoint_singleton_right]
      simp only [Set.mem_compl_iff, not_not]
      exact hx₀
    obtain ⟨g, hg0, hg1, -⟩ :=
      exists_continuous_zero_one_of_isClosed (isClosed_compl_iff.mpr isOpen_interior)
        isClosed_singleton hdisj
    -- Bump function: `g` is `1` at `x₀` and `0` outside the interior.
    let f : C(X, 𝕜) := ⟨fun x => (g x : 𝕜), RCLike.continuous_ofReal.comp g.continuous⟩
    have hf0 : f ≠ 0 := by
      intro h
      have hcon2 : (g x₀ : 𝕜) = 0 := ContinuousMap.congr_fun h x₀
      rw [hg1 (Set.mem_singleton x₀)] at hcon2
      simp at hcon2
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := f) ⟨?_, hf0⟩
    · rw [Module.End.mem_eigenspace_iff]
      change (mulCLM φ) f = μ • f
      apply ContinuousMap.ext
      intro x
      simp only [mulCLM_apply, ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
      by_cases hx : x ∈ interior (φ ⁻¹' {μ})
      · rw [hφ x hx]
      · have hgx : g x = 0 := hg0 hx
        have hfx : f x = 0 := by simp [f, hgx]
        simp [hfx]

end MathlibExt.Analysis.FunctionalAnalysis.MultiplicationOperator
