/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import MathlibExt.Biology.Dynamics.TuringPatterns
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Lyapunov–Schmidt reduction for Turing pattern branches

The steady states of the two-species Turing system `0 = d_u u_xx + f(u, v)`,
`0 = d v_xx + g(u, v)` on `[0, ℓ]` with Neumann boundary conditions near a homogeneous state are the
zeros of a map `F(w, d)` (perturbation `w`, inhibitor diffusion `d`) with trivial branch
`F(0, d) = 0` and state linearization `w ↦ D w_xx + J w`. This file carries out the reduction of
`F(w, d) = 0` near an onset `(0, d₀)` to a scalar equation `G̃(a, d) = 0` in the critical-mode
amplitude `a`, and feeds it to the reduced Crandall–Rabinowitz branch theorem of
`MathlibExt.Biology.Dynamics.TuringBranches` (T55).

## Source receipt

* **Lyapunov–Schmidt reduction**: H. Kielhöfer, *Bifurcation Theory: An Introduction with
  Applications to Partial Differential Equations*, 2nd ed., Springer (2012), §I.2 ("The Method of
  Lyapunov–Schmidt"): for `F(x, λ)` with Fredholm linearization `D_x F(0, λ₀)`, the solutions of
  `F = 0` near `(0, λ₀)` are `x = v + ψ(v, λ)`, `v ∈ ker`, with `Φ(v, λ) = (1 - Q) F(v + ψ(v, λ), λ)
  = 0`, the finite-dimensional bifurcation equation. Here: `lyapunovSchmidt`.
* **Bifurcation from a simple eigenvalue**: M. G. Crandall and P. H. Rabinowitz, *Bifurcation from
  simple eigenvalues*, J. Funct. Anal. 8 (1971) 321–340, Theorem 1.7; the reduced form is T55's
  `exists_patternBranch` (PR #1533), used here only as the explicit hypothesis `hCR`.
* **Turing linearization on Neumann modes**: J. D. Murray, *Mathematical Biology II*, 3rd ed.,
  Springer (2003), ch. 2: `cos(kₙ x) v` with `kₙ = n π / ℓ` is mapped to `cos(kₙ x) (J - kₙ² D) v`.

## Main results

* `lyapunovSchmidt`: for `F : E × Λ → Y` (Banach spaces) strictly differentiable at `(0, p₀)`,
  `F(0, p₀) = 0`, and a Fredholm package of `L = ∂ₓF(0, p₀)` (Mathlib's
  `ContinuousLinearMap.FredholmPackage`: `E = X₁ ⊕ ker L`, `Y = range L ⊕ Y₀`, `X₁ ≃ range L`),
  near `(0, p₀)`: `F(x, p) = 0 ↔ π₁ x = W(π₀ x, p) ∧ g(π₀ x, p) = 0`, where `W = lsSolution` is
  the implicit-function solution of the range equation and `g = lsReduced` the bifurcation map.
* `exists_hasStrictFDerivAt_lsSolution`: `W` is strictly differentiable with `∂_z W(0, p₀) = 0`.
* `eventually_lsSolution_zero`, `eventually_lsScalar_zero`: on the trivial branch `W(0, p) = 0`
  and the reduced maps vanish.
* `lyapunovSchmidt_scalar`: for a simple kernel `ker L = ℝ φ` and `range L = ker ψ` (index zero),
  `F(x, p) = 0 ↔ ∃ a, x = a φ + W(a φ, p) ∧ G̃(a, p) = 0` with `G̃ = lsScalar`.
* `lyapunovSchmidt_patternBranch`: given the reduced branch theorem `hCR` and a factorization
  `G̃(a, d) = a G(a, d)` with `∂_d G(0, d₀) ≠ 0`, the full equation has exactly the trivial
  solutions and one pattern branch `x = a φ + W(a φ, β(a))`, `d = β(a)`, near `(0, d₀)`.
* `modeOperator`, `diffusion_mulVec_deriv_deriv_add`, `deriv_modeField_zero`,
  `deriv_modeField_neumann`: the Turing linearization `D ∂ₓₓ + J` acting on Neumann-mode fields
  `∑ᵢ cos(κᵢ x) wᵢ` is the block-diagonal coefficient operator `wᵢ ↦ (J - κᵢ² D) wᵢ`.
* `modeOperator_eq_zero_iff`, `exists_modeOperator_eq_iff`, `isFredholm_modeOperator`,
  `modeOperator_simpleKernel`: at a critical mode `i₀` (`det (J - κ_{i₀}² D) = 0`) with `f_v ≠ 0`
  and no resonant mode, the coefficient operator is Fredholm with kernel `ℝ · criticalMode` and
  range `ker criticalFunctional`; every Fredholm package of it satisfies the hypotheses of
  `lyapunovSchmidt_scalar`.

## Scope (what is not proved here)

* The Fredholm property of the full PDE operator `D Δ_N + J` (e.g. `C^{2,α} → C^α` or `H²_N → L²`)
  needs elliptic regularity of the Neumann Laplacian, which is in neither Mathlib nor Atlas. The
  Fredholm setup is proved for the linearization on finitely many Neumann modes (a Galerkin
  truncation, `ι` finite); the reduction theorems are stated for an arbitrary Banach-space
  formulation and apply verbatim once such a Fredholm package is available.
* Dividing the scalar map by the amplitude, `G̃(a, d) = a G(a, d)` with `G` strictly
  differentiable, uses `C²` regularity of `F`; it is the hypothesis `hfac`.
* The final branch-existence statement for the Turing system with T55's theorem plugged in
  (`hCR := @exists_patternBranch`) and `G(0, d) =` the critical eigenvalue is deferred until
  PR #1533 merges.
-/

@[expose] public section

open Filter Topology
open ContinuousLinearMap (FredholmPackage)

namespace MathlibExt.Biology.Dynamics.TuringBranchesPDE

section LyapunovSchmidt

variable {E Y Λ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
  {L : E →L[ℝ] Y} (pkg : FredholmPackage L)

/-- The projection of `E` onto the kernel part `X₀ = ker L` of a Fredholm package, along the
essential part `X₁`. -/
noncomputable def kerProj : E →L[ℝ] pkg.decDom.X₀ :=
  pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm

/-- The projection of `Y` onto the cokernel part `Y₀` of a Fredholm package, along the range
`Y₁ = range L`. -/
noncomputable def cokerProj : Y →L[ℝ] pkg.decCodom.X₀ :=
  pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm

/-- `x = π₀ x + π₁ x` for the decomposition `E = X₀ ⊕ X₁`. -/
theorem kerProj_add_proj (x : E) : (kerProj pkg x : E) + (pkg.decDom.proj x : E) = x := by
  rw [add_comm]
  exact Submodule.projectionL_add_projectionL_eq_self pkg.decDom.isTopCompl x

/-- `y = Q y + (1 - Q) y` for the decomposition `Y = Y₁ ⊕ Y₀`. -/
theorem proj_add_cokerProj (y : Y) : (pkg.decCodom.proj y : Y) + (cokerProj pkg y : Y) = y :=
  Submodule.projectionL_add_projectionL_eq_self pkg.decCodom.isTopCompl y

@[simp]
theorem kerProj_coe_X₀ (z : pkg.decDom.X₀) : kerProj pkg (z : E) = z :=
  Submodule.projectionOntoL_apply_left _ z

@[simp]
theorem kerProj_coe_X₁ (w : pkg.decDom.X₁) : kerProj pkg (w : E) = 0 :=
  Submodule.projectionOntoL_apply_right _ w

@[simp]
theorem proj_coe_X₁ (w : pkg.decDom.X₁) : pkg.decDom.proj (w : E) = w :=
  Submodule.projectionOntoL_apply_left _ w

@[simp]
theorem proj_coe_X₀ (z : pkg.decDom.X₀) : pkg.decDom.proj (z : E) = 0 :=
  Submodule.projectionOntoL_apply_right _ z

/-- `L` vanishes on the kernel part `X₀`. -/
theorem apply_coe_X₀ (z : pkg.decDom.X₀) : L z = 0 := by
  have hz : (z : E) ∈ L.ker := by rw [pkg.ker_eq]; exact z.2
  exact hz

/-- On the essential part, `Q ∘ L` is the isomorphism `X₁ ≃ Y₁` of the package. -/
theorem proj_apply_coe_X₁ (w : pkg.decDom.X₁) : pkg.decCodom.proj (L w) = pkg.equiv w := by
  have h : (pkg.equiv w : Y) = L w := by
    have := DFunLike.congr_fun pkg.eq_equiv (w : E)
    simp only [ContinuousLinearMap.comp_apply, proj_coe_X₁] at this
    exact this.symm
  rw [← h]
  exact Submodule.projectionOntoL_apply_left _ _

variable [CompleteSpace E] [CompleteSpace Y] [CompleteSpace Λ]

instance : CompleteSpace pkg.decDom.X₁ := pkg.decDom.isTopCompl.isClosed.completeSpace_coe

instance : CompleteSpace pkg.decCodom.X₁ := pkg.decCodom.isTopCompl.isClosed.completeSpace_coe

instance : CompleteSpace pkg.decDom.X₀ :=
  have := pkg.decDom.finite_X₀
  FiniteDimensional.complete ℝ _

/-- The ansatz `(z, p, w) ↦ (z + w, p)`: a state is a kernel component `z ∈ X₀` plus an essential
component `w ∈ X₁`, together with the parameter `p`. -/
noncomputable def lsEmbed : (pkg.decDom.X₀ × Λ) × pkg.decDom.X₁ →L[ℝ] E × Λ :=
  ((pkg.decDom.X₀.subtypeL ∘L (ContinuousLinearMap.fst ℝ _ _ ∘L ContinuousLinearMap.fst ℝ _ _)) +
      pkg.decDom.X₁.subtypeL ∘L ContinuousLinearMap.snd ℝ _ _).prod
    (ContinuousLinearMap.snd ℝ _ _ ∘L ContinuousLinearMap.fst ℝ _ _)

omit [CompleteSpace E] [CompleteSpace Y] [CompleteSpace Λ] in
@[simp]
theorem lsEmbed_apply (v : (pkg.decDom.X₀ × Λ) × pkg.decDom.X₁) :
    lsEmbed pkg v = ((v.1.1 : E) + v.2, v.1.2) := rfl

/-- The splitting `(x, p) ↦ ((π₀ x, p), π₁ x)`, inverse to `lsEmbed`. -/
noncomputable def lsSplit : E × Λ →L[ℝ] (pkg.decDom.X₀ × Λ) × pkg.decDom.X₁ :=
  ((kerProj pkg ∘L ContinuousLinearMap.fst ℝ _ _).prod (ContinuousLinearMap.snd ℝ _ _)).prod
    (pkg.decDom.proj ∘L ContinuousLinearMap.fst ℝ _ _)

omit [CompleteSpace E] [CompleteSpace Y] [CompleteSpace Λ] in
@[simp]
theorem lsSplit_apply (q : E × Λ) :
    lsSplit pkg q = ((kerProj pkg q.1, q.2), pkg.decDom.proj q.1) := rfl

omit [CompleteSpace E] [CompleteSpace Y] [CompleteSpace Λ] in
theorem lsEmbed_lsSplit (q : E × Λ) : lsEmbed pkg (lsSplit pkg q) = q := by
  change ((kerProj pkg q.1 : E) + (pkg.decDom.proj q.1 : E), q.2) = q
  rw [kerProj_add_proj]

variable {F : E × Λ → Y} {F' : E × Λ →L[ℝ] Y} {p₀ : Λ}

/-- The range equation of the Lyapunov–Schmidt reduction: `Q F(z + w, p)`, where `Q` projects
onto `range L` along the cokernel part. -/
noncomputable def lsRangeMap (F : E × Λ → Y) :
    (pkg.decDom.X₀ × Λ) × pkg.decDom.X₁ → pkg.decCodom.X₁ :=
  fun v => pkg.decCodom.proj (F (lsEmbed pkg v))

omit [CompleteSpace E] [CompleteSpace Y] [CompleteSpace Λ] in
theorem hasStrictFDerivAt_lsRangeMap (hF : HasStrictFDerivAt F F' ((0 : E), p₀)) :
    HasStrictFDerivAt (lsRangeMap pkg F) (pkg.decCodom.proj ∘L F' ∘L lsEmbed pkg)
      (((0 : pkg.decDom.X₀), p₀), (0 : pkg.decDom.X₁)) := by
  have h1 : lsEmbed pkg (((0 : pkg.decDom.X₀), p₀), (0 : pkg.decDom.X₁)) = ((0 : E), p₀) := by
    simp
  have hF' : HasStrictFDerivAt F F'
      (lsEmbed pkg (((0 : pkg.decDom.X₀), p₀), (0 : pkg.decDom.X₁))) := by rwa [h1]
  exact pkg.decCodom.proj.hasStrictFDerivAt.comp _
    (hF'.comp _ (lsEmbed (Λ := Λ) pkg).hasStrictFDerivAt)

omit [CompleteSpace E] [CompleteSpace Y] [CompleteSpace Λ] in
/-- The partial derivative of the range equation in the essential component is the package
isomorphism `X₁ ≃ range L`. -/
theorem lsRangeMap_deriv_inr (hFL : F' ∘L .inl ℝ E Λ = L) :
    (pkg.decCodom.proj ∘L F' ∘L lsEmbed pkg) ∘L .inr ℝ _ _ =
      (pkg.equiv : pkg.decDom.X₁ →L[ℝ] pkg.decCodom.X₁) := by
  ext1 w
  have hw : F' ((w : E), 0) = L w := DFunLike.congr_fun hFL (w : E)
  simp [hw, proj_apply_coe_X₁]

omit [CompleteSpace E] [CompleteSpace Y] [CompleteSpace Λ] in
theorem isInvertible_lsRangeMap_deriv_inr (hFL : F' ∘L .inl ℝ E Λ = L) :
    ((pkg.decCodom.proj ∘L F' ∘L lsEmbed pkg) ∘L .inr ℝ _ _).IsInvertible :=
  ⟨pkg.equiv, (lsRangeMap_deriv_inr pkg hFL).symm⟩

/-- **The Lyapunov–Schmidt solution operator** `W : X₀ × Λ → X₁`: the implicit-function solution
of the range equation `Q F(z + W(z, p), p) = 0` near `(0, p₀)`. -/
noncomputable def lsSolution (hF : HasStrictFDerivAt F F' ((0 : E), p₀))
    (hFL : F' ∘L .inl ℝ E Λ = L) : pkg.decDom.X₀ × Λ → pkg.decDom.X₁ :=
  (hasStrictFDerivAt_lsRangeMap pkg hF).implicitFunctionOfProdDomain
    (isInvertible_lsRangeMap_deriv_inr pkg hFL)

/-- **The reduced (bifurcation) map** `g(z, p) = (1 - Q) F(z + W(z, p), p) ∈ Y₀`, a map between
finite-dimensional spaces. -/
noncomputable def lsReduced (hF : HasStrictFDerivAt F F' ((0 : E), p₀))
    (hFL : F' ∘L .inl ℝ E Λ = L) : pkg.decDom.X₀ × Λ → pkg.decCodom.X₀ :=
  fun q => cokerProj pkg (F ((q.1 : E) + lsSolution pkg hF hFL q, q.2))

/-- Near `((0, p₀), 0)`, the range equation holds exactly on the graph of `W`. -/
theorem eventually_lsRangeMap_eq_zero_iff (hF : HasStrictFDerivAt F F' ((0 : E), p₀))
    (hFL : F' ∘L .inl ℝ E Λ = L) (hF0 : F ((0 : E), p₀) = 0) :
    ∀ᶠ v in 𝓝 (((0 : pkg.decDom.X₀), p₀), (0 : pkg.decDom.X₁)),
      lsRangeMap pkg F v = 0 ↔ lsSolution pkg hF hFL v.1 = v.2 := by
  have h0 : lsRangeMap pkg F (((0 : pkg.decDom.X₀), p₀), (0 : pkg.decDom.X₁)) = 0 := by
    simp [lsRangeMap, hF0]
  have := (hasStrictFDerivAt_lsRangeMap pkg hF).eventually_apply_eq_iff_implicitFunctionOfProdDomain
    (isInvertible_lsRangeMap_deriv_inr pkg hFL)
  rw [h0] at this
  exact this

/-- `W(0, p₀) = 0`. -/
theorem lsSolution_zero (hF : HasStrictFDerivAt F F' ((0 : E), p₀))
    (hFL : F' ∘L .inl ℝ E Λ = L) (hF0 : F ((0 : E), p₀) = 0) :
    lsSolution pkg hF hFL ((0 : pkg.decDom.X₀), p₀) = 0 :=
  ((eventually_lsRangeMap_eq_zero_iff pkg hF hFL hF0).self_of_nhds).1 (by simp [lsRangeMap, hF0])

/-- **Lyapunov–Schmidt reduction.** Let `F : E × Λ → Y` vanish at `(0, p₀)` and be strictly
differentiable there with state derivative `L = ∂ₓF(0, p₀)`, and fix a Fredholm package of `L`
(`E = X₁ ⊕ ker L`, `Y = range L ⊕ Y₀`, `X₁ ≃ range L`). Then near `(0, p₀)`, `F(x, p) = 0` iff the
essential component of `x` is given by the solution operator, `π₁ x = W(π₀ x, p)`, and the kernel
component solves the finite-dimensional bifurcation equation `g(π₀ x, p) = 0`. -/
theorem lyapunovSchmidt (hF : HasStrictFDerivAt F F' ((0 : E), p₀))
    (hFL : F' ∘L .inl ℝ E Λ = L) (hF0 : F ((0 : E), p₀) = 0) :
    ∀ᶠ q in 𝓝 ((0 : E), p₀), F q = 0 ↔
      lsSolution pkg hF hFL (kerProj pkg q.1, q.2) = pkg.decDom.proj q.1 ∧
        lsReduced pkg hF hFL (kerProj pkg q.1, q.2) = 0 := by
  have ht : Tendsto (lsSplit pkg) (𝓝 ((0 : E), p₀))
      (𝓝 (((0 : pkg.decDom.X₀), p₀), (0 : pkg.decDom.X₁))) := by
    have := (lsSplit (Λ := Λ) pkg).continuous.tendsto ((0 : E), p₀)
    simpa using this
  filter_upwards [ht.eventually (eventually_lsRangeMap_eq_zero_iff pkg hF hFL hF0)] with q hq
  have hR : lsRangeMap pkg F (lsSplit pkg q) = pkg.decCodom.proj (F q) := by
    simp only [lsRangeMap, lsEmbed_lsSplit]
  rw [hR] at hq
  simp only [lsSplit_apply] at hq
  constructor
  · intro h0
    have hW := hq.1 (by simp [h0])
    refine ⟨hW, ?_⟩
    simp only [lsReduced, hW, kerProj_add_proj, h0, map_zero]
  · rintro ⟨hW, hG⟩
    have h1 := hq.2 hW
    simp only [lsReduced, hW, kerProj_add_proj] at hG
    rw [← proj_add_cokerProj pkg (F q), h1, hG]
    simp

/-- The solution operator is strictly differentiable at `(0, p₀)` and its derivative vanishes in
the kernel direction: `∂_z W(0, p₀) = 0`, so the branch is tangent to `ker L`. -/
theorem exists_hasStrictFDerivAt_lsSolution (hF : HasStrictFDerivAt F F' ((0 : E), p₀))
    (hFL : F' ∘L .inl ℝ E Λ = L) :
    ∃ W' : pkg.decDom.X₀ × Λ →L[ℝ] pkg.decDom.X₁,
      HasStrictFDerivAt (lsSolution pkg hF hFL) W' ((0 : pkg.decDom.X₀), p₀) ∧
        W' ∘L .inl ℝ _ _ = 0 := by
  refine ⟨_, (hasStrictFDerivAt_lsRangeMap pkg hF).hasStrictFDerivAt_implicitFunctionOfProdDomain
    (isInvertible_lsRangeMap_deriv_inr pkg hFL), ?_⟩
  ext1 z
  have hz : F' ((z : E), 0) = L z := DFunLike.congr_fun hFL (z : E)
  simp [hz, apply_coe_X₀]

/-- **Trivial branch.** If `F(0, p) = 0` for `p` near `p₀`, then `W(0, p) = 0` and the reduced
map vanishes on the trivial branch, `g(0, p) = 0`. -/
theorem eventually_lsSolution_zero (hF : HasStrictFDerivAt F F' ((0 : E), p₀))
    (hFL : F' ∘L .inl ℝ E Λ = L) (htriv : ∀ᶠ p in 𝓝 p₀, F ((0 : E), p) = 0) :
    ∀ᶠ p in 𝓝 p₀, lsSolution pkg hF hFL ((0 : pkg.decDom.X₀), p) = 0 ∧
      lsReduced pkg hF hFL ((0 : pkg.decDom.X₀), p) = 0 := by
  have ht : Tendsto (fun p : Λ => (((0 : pkg.decDom.X₀), p), (0 : pkg.decDom.X₁))) (𝓝 p₀)
      (𝓝 (((0 : pkg.decDom.X₀), p₀), (0 : pkg.decDom.X₁))) :=
    ((continuous_const.prodMk continuous_id).prodMk continuous_const).tendsto p₀
  filter_upwards [ht.eventually (eventually_lsRangeMap_eq_zero_iff pkg hF hFL htriv.self_of_nhds),
    htriv] with p hp h0
  have hW : lsSolution pkg hF hFL ((0 : pkg.decDom.X₀), p) = 0 :=
    hp.1 (by simp [lsRangeMap, h0])
  exact ⟨hW, by simp [lsReduced, hW, h0]⟩

/-! ### Simple kernel: reduction to a scalar equation -/

section SimpleKernel

variable {φ : E} (hφ : φ ∈ pkg.decDom.X₀) (hspan : ∀ z : pkg.decDom.X₀, ∃ a : ℝ, (z : E) = a • φ)
  (ψ : Y →L[ℝ] ℝ)

/-- **The scalar bifurcation function** `G̃(a, p) = ψ(F(a φ + W(a φ, p), p))` of a simple kernel
`ker L = ℝ φ`, with `ψ` a functional whose kernel contains `range L` and which is injective on the
cokernel part. -/
noncomputable def lsScalar (hF : HasStrictFDerivAt F F' ((0 : E), p₀))
    (hFL : F' ∘L .inl ℝ E Λ = L) : ℝ × Λ → ℝ :=
  fun q => ψ (F (q.1 • φ + lsSolution pkg hF hFL (q.1 • ⟨φ, hφ⟩, q.2), q.2))

/-- The scalar bifurcation function has the zeros of the reduced map. -/
theorem lsScalar_eq_zero_iff (hF : HasStrictFDerivAt F F' ((0 : E), p₀))
    (hFL : F' ∘L .inl ℝ E Λ = L) (hψ1 : ∀ y ∈ pkg.decCodom.X₁, ψ y = 0)
    (hψ0 : ∀ y ∈ pkg.decCodom.X₀, ψ y = 0 → y = 0) (q : ℝ × Λ) :
    lsScalar pkg hφ ψ hF hFL q = 0 ↔ lsReduced pkg hF hFL (q.1 • ⟨φ, hφ⟩, q.2) = 0 := by
  set y := F (q.1 • φ + lsSolution pkg hF hFL (q.1 • ⟨φ, hφ⟩, q.2), q.2) with hy
  have hred : lsReduced pkg hF hFL (q.1 • ⟨φ, hφ⟩, q.2) = cokerProj pkg y := rfl
  have hsc : lsScalar pkg hφ ψ hF hFL q = ψ (cokerProj pkg y : Y) := by
    have h := congrArg ψ (proj_add_cokerProj pkg y)
    rw [map_add, hψ1 _ (pkg.decCodom.proj y).2, zero_add] at h
    exact h.symm
  rw [hred, hsc]
  constructor
  · intro h
    exact Subtype.ext (hψ0 _ (cokerProj pkg y).2 h)
  · intro h
    rw [h]
    simp

/-- The coordinate of the kernel component `π₀ x = a φ`. -/
noncomputable def kerCoord (x : E) : ℝ :=
  Classical.choose (hspan (kerProj pkg x))

omit [CompleteSpace E] [CompleteSpace Y] [CompleteSpace Λ] in
theorem coe_kerProj_eq_kerCoord_smul (x : E) :
    (kerProj pkg x : E) = kerCoord pkg hspan x • φ :=
  Classical.choose_spec (hspan (kerProj pkg x))

omit [CompleteSpace E] [CompleteSpace Y] [CompleteSpace Λ] in
theorem kerProj_eq_kerCoord_smul (x : E) :
    kerProj pkg x = kerCoord pkg hspan x • (⟨φ, hφ⟩ : pkg.decDom.X₀) :=
  Subtype.ext (coe_kerProj_eq_kerCoord_smul pkg hspan x)

omit [CompleteSpace E] [CompleteSpace Y] [CompleteSpace Λ] in
theorem kerProj_smul_add (a : ℝ) (w : pkg.decDom.X₁) :
    kerProj pkg (a • φ + w) = a • (⟨φ, hφ⟩ : pkg.decDom.X₀) := by
  have : kerProj pkg φ = ⟨φ, hφ⟩ := kerProj_coe_X₀ pkg ⟨φ, hφ⟩
  rw [map_add, map_smul, this, kerProj_coe_X₁, add_zero]

include hφ in
omit [CompleteSpace E] [CompleteSpace Y] [CompleteSpace Λ] in
theorem proj_smul_add (a : ℝ) (w : pkg.decDom.X₁) :
    pkg.decDom.proj (a • φ + w) = w := by
  have : pkg.decDom.proj φ = 0 := proj_coe_X₀ pkg ⟨φ, hφ⟩
  rw [map_add, map_smul, this, proj_coe_X₁, smul_zero, zero_add]

include hspan in
/-- **Lyapunov–Schmidt reduction to a scalar equation.** For a simple kernel `ker L = ℝ φ` and a
functional `ψ` cutting out `range L` (index zero), near `(0, p₀)` the solutions of `F(x, p) = 0`
are exactly `x = a φ + W(a φ, p)` with `G̃(a, p) = 0`. -/
theorem lyapunovSchmidt_scalar (hF : HasStrictFDerivAt F F' ((0 : E), p₀))
    (hFL : F' ∘L .inl ℝ E Λ = L) (hF0 : F ((0 : E), p₀) = 0)
    (hψ1 : ∀ y ∈ pkg.decCodom.X₁, ψ y = 0) (hψ0 : ∀ y ∈ pkg.decCodom.X₀, ψ y = 0 → y = 0) :
    ∀ᶠ q in 𝓝 ((0 : E), p₀), F q = 0 ↔
      ∃ a : ℝ, q.1 = a • φ + lsSolution pkg hF hFL (a • ⟨φ, hφ⟩, q.2) ∧
        lsScalar pkg hφ ψ hF hFL (a, q.2) = 0 := by
  filter_upwards [lyapunovSchmidt pkg hF hFL hF0] with q hq
  rw [hq]
  constructor
  · rintro ⟨hW, hG⟩
    rw [kerProj_eq_kerCoord_smul pkg hφ hspan] at hW hG
    refine ⟨kerCoord pkg hspan q.1, ?_, (lsScalar_eq_zero_iff pkg hφ ψ hF hFL hψ1 hψ0 _).2 hG⟩
    rw [hW, ← coe_kerProj_eq_kerCoord_smul pkg hspan, kerProj_add_proj]
  · rintro ⟨a, hx, hG⟩
    have hk : kerProj pkg q.1 = a • (⟨φ, hφ⟩ : pkg.decDom.X₀) := by
      rw [hx, kerProj_smul_add pkg hφ]
    have hp : pkg.decDom.proj q.1 = lsSolution pkg hF hFL (a • ⟨φ, hφ⟩, q.2) := by
      rw [hx, proj_smul_add pkg hφ a]
    rw [hk, hp]
    exact ⟨rfl, (lsScalar_eq_zero_iff pkg hφ ψ hF hFL hψ1 hψ0 _).1 hG⟩

/-- On the trivial branch the scalar bifurcation function vanishes: `G̃(0, p) = 0`. -/
theorem eventually_lsScalar_zero (hF : HasStrictFDerivAt F F' ((0 : E), p₀))
    (hFL : F' ∘L .inl ℝ E Λ = L) (htriv : ∀ᶠ p in 𝓝 p₀, F ((0 : E), p) = 0) :
    ∀ᶠ p in 𝓝 p₀, lsScalar pkg hφ ψ hF hFL (0, p) = 0 := by
  filter_upwards [eventually_lsSolution_zero pkg hF hFL htriv, htriv] with p hp h0
  simp [lsScalar, hp.1, h0]

omit [CompleteSpace E] [CompleteSpace Y] [CompleteSpace Λ] in
/-- The kernel coordinate tends to `0` at `x = 0`. -/
theorem tendsto_kerCoord (hφ0 : φ ≠ 0) : Tendsto (kerCoord pkg hspan) (𝓝 0) (𝓝 0) := by
  have h : ∀ x, ‖kerCoord pkg hspan x‖ = ‖kerProj pkg x‖ / ‖φ‖ := by
    intro x
    have hn : ‖φ‖ ≠ 0 := norm_ne_zero_iff.2 hφ0
    rw [eq_div_iff hn, ← norm_smul, ← coe_kerProj_eq_kerCoord_smul pkg hspan]
    rfl
  have hc : Tendsto (fun x => ‖kerProj pkg x‖ / ‖φ‖) (𝓝 (0 : E)) (𝓝 0) := by
    have := ((kerProj pkg).continuous.norm.tendsto (0 : E)).div_const ‖φ‖
    simpa using this
  exact squeeze_zero_norm (fun x => (h x).le) hc

end SimpleKernel

end LyapunovSchmidt

/-! ### Pattern branches from a reduced Crandall–Rabinowitz theorem -/

section PatternBranch

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {L : E →L[ℝ] Y} (pkg : FredholmPackage L)
  {F : E × ℝ → Y} {F' : E × ℝ →L[ℝ] Y} {d₀ : ℝ}

/-- **Pattern branches of the full problem from the reduced branch theorem.** Let `F(x, d)` have
the trivial branch `F(0, d) = 0` near `d₀` and a simple-kernel, index-zero linearization at
`(0, d₀)` (Fredholm package with `ker L = ℝ φ`, `range L = ker ψ`). Assume the scalar
bifurcation function factors as `G̃(a, d) = a G(a, d)` near `(0, d₀)` with `G` strictly
differentiable, `G(0, d₀) = 0` and `∂_d G(0, d₀) ≠ 0`.

The reduced Crandall–Rabinowitz branch theorem for `a G(a, d) = 0` (`exists_patternBranch` of
`MathlibExt.Biology.Dynamics.TuringBranches`, PR #1533, not yet merged) is taken as the explicit
hypothesis `hCR`, stated verbatim. Then the full equation has a unique local pattern branch: a
`d = β(a)` through `(0, d₀)` with slope `-∂_a G / ∂_d G` such that near `(0, d₀)` the solutions
of `F(x, d) = 0` are exactly the trivial ones `x = 0` and the branch
`x = a φ + W(a φ, d)`, `d = β(a)`; every point of the branch solves `F = 0` for small `a`. -/
theorem lyapunovSchmidt_patternBranch (hF : HasStrictFDerivAt F F' ((0 : E), d₀))
    (hFL : F' ∘L .inl ℝ E ℝ = L) (htriv : ∀ᶠ d in 𝓝 d₀, F ((0 : E), d) = 0)
    {φ : E} (hφ : φ ∈ pkg.decDom.X₀) (hφ0 : φ ≠ 0)
    (hspan : ∀ z : pkg.decDom.X₀, ∃ a : ℝ, (z : E) = a • φ)
    (ψ : Y →L[ℝ] ℝ) (hψ1 : ∀ y ∈ pkg.decCodom.X₁, ψ y = 0)
    (hψ0 : ∀ y ∈ pkg.decCodom.X₀, ψ y = 0 → y = 0)
    (hCR : ∀ {G : ℝ × ℝ → ℝ} {G' : ℝ × ℝ →L[ℝ] ℝ} {d₀ : ℝ},
      HasStrictFDerivAt G G' (0, d₀) → G (0, d₀) = 0 → G' (0, 1) ≠ 0 →
        ∃ φ : ℝ → ℝ, φ 0 = d₀ ∧ HasStrictDerivAt φ (-(G' (1, 0) / G' (0, 1))) 0 ∧
          ∀ᶠ p in 𝓝 ((0 : ℝ), d₀), (p.1 * G p = 0 ↔ p.1 = 0 ∨ p.2 = φ p.1))
    {G : ℝ × ℝ → ℝ} {G' : ℝ × ℝ →L[ℝ] ℝ}
    (hfac : ∀ᶠ q in 𝓝 ((0 : ℝ), d₀), lsScalar pkg hφ ψ hF hFL q = q.1 * G q)
    (hG : HasStrictFDerivAt G G' (0, d₀)) (hG0 : G (0, d₀) = 0) (htrans : G' (0, 1) ≠ 0) :
    ∃ β : ℝ → ℝ, β 0 = d₀ ∧ HasStrictDerivAt β (-(G' (1, 0) / G' (0, 1))) 0 ∧
      (∀ᶠ q in 𝓝 ((0 : E), d₀), (F q = 0 ↔ q.1 = 0 ∨
        ∃ a : ℝ, q.1 = a • φ + lsSolution pkg hF hFL (a • ⟨φ, hφ⟩, q.2) ∧ q.2 = β a)) ∧
      ∀ᶠ a in 𝓝 (0 : ℝ),
        F (a • φ + lsSolution pkg hF hFL (a • ⟨φ, hφ⟩, β a), β a) = 0 := by
  obtain ⟨β, hβ0, hβd, hβz⟩ := hCR hG hG0 htrans
  have hF0 : F ((0 : E), d₀) = 0 := htriv.self_of_nhds
  have hfst : Tendsto (fun q : E × ℝ => q.1) (𝓝 ((0 : E), d₀)) (𝓝 0) :=
    continuous_fst.tendsto _
  have hsnd : Tendsto (fun q : E × ℝ => q.2) (𝓝 ((0 : E), d₀)) (𝓝 d₀) :=
    continuous_snd.tendsto _
  have ht : Tendsto (fun q : E × ℝ => (kerCoord pkg hspan q.1, q.2)) (𝓝 ((0 : E), d₀))
      (𝓝 ((0 : ℝ), d₀)) :=
    ((tendsto_kerCoord pkg hspan hφ0).comp hfst).prodMk_nhds hsnd
  have hWtriv : ∀ᶠ q in 𝓝 ((0 : E), d₀),
      lsSolution pkg hF hFL ((0 : pkg.decDom.X₀), q.2) = 0 :=
    (hsnd.eventually (eventually_lsSolution_zero pkg hF hFL htriv)).mono fun _ h => h.1
  have hmain : ∀ᶠ q in 𝓝 ((0 : E), d₀), (F q = 0 ↔ q.1 = 0 ∨
      ∃ a : ℝ, q.1 = a • φ + lsSolution pkg hF hFL (a • ⟨φ, hφ⟩, q.2) ∧ q.2 = β a) := by
    filter_upwards [lyapunovSchmidt pkg hF hFL hF0, ht.eventually hfac, ht.eventually hβz,
      hWtriv] with q hq hfacq hβq hWq
    set c := kerCoord pkg hspan q.1 with hc
    have hk : kerProj pkg q.1 = c • (⟨φ, hφ⟩ : pkg.decDom.X₀) :=
      kerProj_eq_kerCoord_smul pkg hφ hspan q.1
    have hred : lsReduced pkg hF hFL (kerProj pkg q.1, q.2) = 0 ↔ (c = 0 ∨ q.2 = β c) := by
      rw [hk]
      exact (lsScalar_eq_zero_iff pkg hφ ψ hF hFL hψ1 hψ0 (c, q.2)).symm.trans
        ((Eq.congr_left hfacq).trans hβq)
    rw [hq, hred]
    constructor
    · rintro ⟨hW, hc0 | hd⟩
      · left
        rw [← kerProj_add_proj pkg q.1, ← hW, hk, hc0, zero_smul, hWq]
        simp
      · right
        refine ⟨c, ?_, hd⟩
        rw [hk] at hW
        rw [hW, ← coe_kerProj_eq_kerCoord_smul pkg hspan, kerProj_add_proj]
    · rintro (h0 | ⟨a, hx, hd⟩)
      · have hc0 : c = 0 := by
          have h : (kerProj pkg q.1 : E) = c • φ := coe_kerProj_eq_kerCoord_smul pkg hspan q.1
          rw [h0, map_zero] at h
          exact (smul_eq_zero.1 h.symm).resolve_right hφ0
        refine ⟨?_, Or.inl hc0⟩
        rw [hk, hc0, zero_smul, hWq, h0, map_zero]
      · have hk' : kerProj pkg q.1 = a • (⟨φ, hφ⟩ : pkg.decDom.X₀) := by
          rw [hx, kerProj_smul_add pkg hφ]
        have hca : c = a := by
          have h : c • φ = a • φ := by
            have := congrArg (fun z : pkg.decDom.X₀ => (z : E)) (hk.symm.trans hk')
            simpa using this
          exact smul_left_injective ℝ hφ0 h
        refine ⟨?_, Or.inr (hca ▸ hd)⟩
        rw [hk']
        conv_rhs => rw [hx]
        rw [proj_smul_add pkg hφ a]
  refine ⟨β, hβ0, hβd, hmain, ?_⟩
  obtain ⟨W', hW', -⟩ := exists_hasStrictFDerivAt_lsSolution pkg hF hFL
  have hW0 := lsSolution_zero pkg hF hFL hF0
  have hβc : Tendsto β (𝓝 0) (𝓝 d₀) := hβ0 ▸ hβd.hasDerivAt.continuousAt.tendsto
  have h1 : Tendsto (fun a : ℝ => (a • (⟨φ, hφ⟩ : pkg.decDom.X₀), β a)) (𝓝 0)
      (𝓝 ((0 : pkg.decDom.X₀), d₀)) := by
    have h1a : Tendsto (fun a : ℝ => a • (⟨φ, hφ⟩ : pkg.decDom.X₀)) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const (⟨φ, hφ⟩ : pkg.decDom.X₀)
    exact h1a.prodMk_nhds hβc
  have hA : Tendsto (fun a : ℝ => a • φ) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const φ
  have hB : Tendsto (fun a : ℝ => (lsSolution pkg hF hFL (a • ⟨φ, hφ⟩, β a) : E)) (𝓝 0)
      (𝓝 0) := by
    have := (continuous_subtype_val.tendsto _).comp (hW'.continuousAt.tendsto.comp h1)
    rw [hW0, Submodule.coe_zero] at this
    exact this
  have h2 : Tendsto (fun a : ℝ => (a • φ + (lsSolution pkg hF hFL (a • ⟨φ, hφ⟩, β a) : E), β a))
      (𝓝 0) (𝓝 ((0 : E), d₀)) := by
    simpa using (hA.add hB).prodMk_nhds hβc
  filter_upwards [h2.eventually hmain] with a ha
  exact ha.2 (Or.inr ⟨a, rfl, rfl⟩)

end PatternBranch

/-! ### The Turing linearization on Neumann-mode coefficients -/

section TuringModes

open MathlibExt.Biology.Dynamics.TuringPatterns Matrix

/-- A kernel vector `(m₀₁, -m₀₀)` of a singular `2 × 2` matrix. -/
def kerVec (M : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → ℝ := ![M 0 1, -M 0 0]

/-- A singular real `2 × 2` matrix with `m₀₁ ≠ 0` has kernel `ℝ (m₀₁, -m₀₀)`. -/
theorem mulVec_eq_zero_iff_of_det_eq_zero {M : Matrix (Fin 2) (Fin 2) ℝ} (hdet : M.det = 0)
    (h01 : M 0 1 ≠ 0) (w : Fin 2 → ℝ) : M *ᵥ w = 0 ↔ ∃ a : ℝ, w = a • kerVec M := by
  rw [det_fin_two] at hdet
  constructor
  · intro h
    have h0 : M 0 0 * w 0 + M 0 1 * w 1 = 0 := by
      simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 0
    refine ⟨w 0 / M 0 1, funext fun i => ?_⟩
    fin_cases i
    · simp [kerVec]
      field_simp
    · simp [kerVec]
      field_simp
      linarith
  · rintro ⟨a, rfl⟩
    funext i
    fin_cases i
    · simp [kerVec, mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · simp [kerVec, mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination (-a) * hdet

/-- A singular real `2 × 2` matrix with `m₀₁ ≠ 0` has range `{y | m₁₁ y₀ - m₀₁ y₁ = 0}`. -/
theorem exists_mulVec_eq_iff_of_det_eq_zero {M : Matrix (Fin 2) (Fin 2) ℝ} (hdet : M.det = 0)
    (h01 : M 0 1 ≠ 0) (y : Fin 2 → ℝ) :
    (∃ w, M *ᵥ w = y) ↔ M 1 1 * y 0 - M 0 1 * y 1 = 0 := by
  rw [det_fin_two] at hdet
  constructor
  · rintro ⟨w, rfl⟩
    simp only [mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination w 0 * hdet
  · intro h
    refine ⟨![0, y 0 / M 0 1], funext fun i => ?_⟩
    fin_cases i
    · simp [mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
    · simp [mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
      linarith

variable {ι : Type*} [Fintype ι]

/-- **The linearized Turing operator on Neumann-mode coefficients.** On `[0, ℓ]` with Neumann
boundary conditions, a field `u(x) = ∑ₙ cos(kₙ x) wₙ` (`wₙ ∈ ℝ²`) is mapped by the linearization
`u ↦ D u_xx + J u` to `∑ₙ cos(kₙ x) (J - kₙ² D) wₙ`; on the coefficients this is the block-diagonal
operator `wₙ ↦ (J - kₙ² D) wₙ`. Here `ι` indexes a finite set of modes with wavenumbers `κ`
(e.g. `κ n = neumannWavenumber ℓ n`, `n < N`: a Galerkin truncation). -/
noncomputable def modeOperator (J : Matrix (Fin 2) (Fin 2) ℝ) (du d : ℝ) (κ : ι → ℝ) :
    (ι → Fin 2 → ℝ) →L[ℝ] (ι → Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    (LinearMap.pi fun i => Matrix.toLin' (modeMatrix J du d (κ i)) ∘ₗ LinearMap.proj i)

@[simp]
theorem modeOperator_apply (J : Matrix (Fin 2) (Fin 2) ℝ) (du d : ℝ) (κ : ι → ℝ)
    (w : ι → Fin 2 → ℝ) (i : ι) :
    modeOperator J du d κ w i = modeMatrix J du d (κ i) *ᵥ w i := rfl

/-- The off-diagonal entry `m₀₁` of every mode matrix is `f_v = J₀₁` (diffusion is diagonal). -/
@[simp]
theorem modeMatrix_zero_one (J : Matrix (Fin 2) (Fin 2) ℝ) (du d k : ℝ) :
    modeMatrix J du d k 0 1 = J 0 1 := by
  simp [modeMatrix, diffusionMatrix]

/-- The functional cutting out the range: `y ↦ m₁₁ y_{i₀,0} - m₀₁ y_{i₀,1}`, a left null vector of
the critical mode matrix applied to mode `i₀`. -/
noncomputable def criticalFunctional (J : Matrix (Fin 2) (Fin 2) ℝ) (du d : ℝ) (κ : ι → ℝ)
    (i₀ : ι) : (ι → Fin 2 → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => modeMatrix J du d (κ i₀) 1 1 * y i₀ 0 - J 0 1 * y i₀ 1
      map_add' := fun y z => by simp only [Pi.add_apply]; ring
      map_smul' := fun c y => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

@[simp]
theorem criticalFunctional_apply (J : Matrix (Fin 2) (Fin 2) ℝ) (du d : ℝ) (κ : ι → ℝ) (i₀ : ι)
    (y : ι → Fin 2 → ℝ) :
    criticalFunctional J du d κ i₀ y = modeMatrix J du d (κ i₀) 1 1 * y i₀ 0 - J 0 1 * y i₀ 1 :=
  rfl

/-- The Neumann-mode field `u(x) = ∑ᵢ cos(κᵢ x) wᵢ ∈ ℝ²` with coefficients `w`. -/
noncomputable def modeField (κ : ι → ℝ) (w : ι → Fin 2 → ℝ) (x : ℝ) : Fin 2 → ℝ :=
  ∑ i, Real.cos (κ i * x) • w i

theorem hasDerivAt_modeField (κ : ι → ℝ) (w : ι → Fin 2 → ℝ) (x : ℝ) :
    HasDerivAt (modeField κ w) (∑ i, (-(κ i * Real.sin (κ i * x))) • w i) x := by
  have h : ∀ i ∈ (Finset.univ : Finset ι), HasDerivAt (fun y => Real.cos (κ i * y) • w i)
      ((-(κ i * Real.sin (κ i * x))) • w i) x := by
    intro i _
    have hc := ((Real.hasDerivAt_cos (κ i * x)).comp x ((hasDerivAt_id x).const_mul (κ i)))
    exact (hc.smul_const (w i)).congr_deriv (by congr 1; ring)
  exact HasDerivAt.fun_sum h

theorem hasDerivAt_deriv_modeField (κ : ι → ℝ) (w : ι → Fin 2 → ℝ) (x : ℝ) :
    HasDerivAt (deriv (modeField κ w)) (∑ i, (-(κ i ^ 2 * Real.cos (κ i * x))) • w i) x := by
  have hd : deriv (modeField κ w) = fun y => ∑ i, (-(κ i * Real.sin (κ i * y))) • w i :=
    funext fun y => (hasDerivAt_modeField κ w y).deriv
  rw [hd]
  have h : ∀ i ∈ (Finset.univ : Finset ι), HasDerivAt (fun y => (-(κ i * Real.sin (κ i * y))) • w i)
      ((-(κ i ^ 2 * Real.cos (κ i * x))) • w i) x := by
    intro i _
    have hs := (((Real.hasDerivAt_sin (κ i * x)).comp x
      ((hasDerivAt_id x).const_mul (κ i))).const_mul (κ i)).neg
    exact (hs.smul_const (w i)).congr_deriv (by congr 1; ring)
  exact HasDerivAt.fun_sum h

/-- **The coefficient operator is the PDE linearization on mode fields.** For the field
`u = ∑ᵢ cos(κᵢ x) wᵢ`, `D u_xx + J u` is the mode field of `modeOperator J du d κ w`. -/
theorem diffusion_mulVec_deriv_deriv_add (J : Matrix (Fin 2) (Fin 2) ℝ) (du d : ℝ)
    (κ : ι → ℝ) (w : ι → Fin 2 → ℝ) (x : ℝ) :
    diffusionMatrix du d *ᵥ deriv (deriv (modeField κ w)) x + J *ᵥ modeField κ w x =
      modeField κ (modeOperator J du d κ w) x := by
  rw [(hasDerivAt_deriv_modeField κ w x).deriv]
  simp only [modeField, modeOperator_apply, Matrix.mulVec_sum, Matrix.mulVec_smul,
    ← Finset.sum_add_distrib, modeMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  module

/-- Every mode field satisfies the zero-flux condition at `x = 0`. -/
theorem deriv_modeField_zero (κ : ι → ℝ) (w : ι → Fin 2 → ℝ) :
    deriv (modeField κ w) 0 = 0 := by
  simp [(hasDerivAt_modeField κ w 0).deriv]

/-- A field of Neumann modes `kₙ = n π / ℓ` satisfies the zero-flux condition at `x = ℓ`. -/
theorem deriv_modeField_neumann {ℓ : ℝ} (hℓ : ℓ ≠ 0) (m : ι → ℕ) (w : ι → Fin 2 → ℝ) :
    deriv (modeField (fun i => neumannWavenumber ℓ (m i)) w) ℓ = 0 := by
  rw [(hasDerivAt_modeField _ w ℓ).deriv]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : neumannWavenumber ℓ (m i) * ℓ = (m i : ℕ) * Real.pi := by
    simp only [neumannWavenumber]
    field_simp
  simp [this, Real.sin_nat_mul_pi]

variable [DecidableEq ι]

/-- The critical Neumann mode: the coefficient field with the kernel vector of the critical mode
matrix in mode `i₀` and zero elsewhere. -/
def criticalMode (J : Matrix (Fin 2) (Fin 2) ℝ) (du d : ℝ) (κ : ι → ℝ) (i₀ : ι) :
    ι → Fin 2 → ℝ :=
  Pi.single i₀ (kerVec (modeMatrix J du d (κ i₀)))

variable {J : Matrix (Fin 2) (Fin 2) ℝ} {du d : ℝ} {κ : ι → ℝ} {i₀ : ι}

/-- **Kernel of the linearization.** If mode `i₀` is critical (`det (J - k_{i₀}² D) = 0`),
`f_v ≠ 0`, and no other mode is (non-resonance: `det (J - kᵢ² D) ≠ 0` for `i ≠ i₀`), the kernel is
spanned by the critical mode. -/
theorem modeOperator_eq_zero_iff (hcrit : (modeMatrix J du d (κ i₀)).det = 0) (hfv : J 0 1 ≠ 0)
    (hnr : ∀ i, i ≠ i₀ → (modeMatrix J du d (κ i)).det ≠ 0) (w : ι → Fin 2 → ℝ) :
    modeOperator J du d κ w = 0 ↔ ∃ a : ℝ, w = a • criticalMode J du d κ i₀ := by
  have h01 : modeMatrix J du d (κ i₀) 0 1 ≠ 0 := by simpa using hfv
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (mulVec_eq_zero_iff_of_det_eq_zero hcrit h01 (w i₀)).1
      (by simpa using congrFun h i₀)
    refine ⟨a, funext fun i => ?_⟩
    by_cases hi : i = i₀
    · subst hi
      simp [criticalMode, ha]
    · have : modeMatrix J du d (κ i) *ᵥ w i = 0 := by simpa using congrFun h i
      simp [criticalMode, hi, eq_zero_of_mulVec_eq_zero (hnr i hi) this]
  · rintro ⟨a, rfl⟩
    funext i
    by_cases hi : i = i₀
    · subst hi
      have := (mulVec_eq_zero_iff_of_det_eq_zero hcrit h01 (a • kerVec _)).2 ⟨a, rfl⟩
      simpa [criticalMode] using this
    · simp [criticalMode, hi]

omit [DecidableEq ι] in
/-- **Range of the linearization.** Under the same hypotheses, `range L = ker ψ` for the critical
functional `ψ`: the range has codimension one. -/
theorem exists_modeOperator_eq_iff (hcrit : (modeMatrix J du d (κ i₀)).det = 0)
    (hfv : J 0 1 ≠ 0) (hnr : ∀ i, i ≠ i₀ → (modeMatrix J du d (κ i)).det ≠ 0)
    (y : ι → Fin 2 → ℝ) :
    (∃ w, modeOperator J du d κ w = y) ↔ criticalFunctional J du d κ i₀ y = 0 := by
  have h01 : modeMatrix J du d (κ i₀) 0 1 ≠ 0 := by simpa using hfv
  rw [criticalFunctional_apply, ← modeMatrix_zero_one J du d (κ i₀),
    ← exists_mulVec_eq_iff_of_det_eq_zero hcrit h01]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w i₀, rfl⟩
  · rintro ⟨w₀, hw₀⟩
    classical
    refine ⟨fun i => if i = i₀ then w₀ else (modeMatrix J du d (κ i))⁻¹ *ᵥ y i, funext fun i => ?_⟩
    by_cases hi : i = i₀
    · subst hi
      simp [hw₀]
    · have hu : IsUnit (modeMatrix J du d (κ i)).det := (hnr i hi).isUnit
      simp [hi, mulVec_mulVec, mul_nonsing_inv _ hu]

omit [DecidableEq ι] in
/-- **Fredholm setup.** The coefficient linearization is a Fredholm operator (finitely many
modes). -/
theorem isFredholm_modeOperator :
    (modeOperator J du d κ).IsFredholm :=
  ⟨(modeOperator J du d κ).isStrictMap_of_finiteDimensional,
    Submodule.closed_of_finiteDimensional _, inferInstance, Submodule.CoFG.of_finite,
    Submodule.ClosedComplemented.of_finiteDimensional _⟩

/-- **Simple kernel, index zero.** For every Fredholm package of the coefficient linearization at a
critical, non-resonant mode `i₀` with `f_v ≠ 0`, the critical mode spans the kernel part and the
critical functional cuts out the range and is injective on the cokernel part: exactly the
hypotheses of `lyapunovSchmidt_scalar` and `lyapunovSchmidt_patternBranch`. -/
theorem modeOperator_simpleKernel (hcrit : (modeMatrix J du d (κ i₀)).det = 0)
    (hfv : J 0 1 ≠ 0) (hnr : ∀ i, i ≠ i₀ → (modeMatrix J du d (κ i)).det ≠ 0)
    (pkg : FredholmPackage (modeOperator J du d κ)) :
    criticalMode J du d κ i₀ ∈ pkg.decDom.X₀ ∧
      (∀ z : pkg.decDom.X₀, ∃ a : ℝ, (z : ι → Fin 2 → ℝ) = a • criticalMode J du d κ i₀) ∧
      (∀ y ∈ pkg.decCodom.X₁, criticalFunctional J du d κ i₀ y = 0) ∧
      ∀ y ∈ pkg.decCodom.X₀, criticalFunctional J du d κ i₀ y = 0 → y = 0 := by
  have hker : ∀ w, w ∈ pkg.decDom.X₀ ↔ ∃ a : ℝ, w = a • criticalMode J du d κ i₀ := by
    intro w
    rw [← pkg.ker_eq]
    exact modeOperator_eq_zero_iff hcrit hfv hnr w
  have hran : ∀ y, y ∈ pkg.decCodom.X₁ ↔ criticalFunctional J du d κ i₀ y = 0 := by
    intro y
    rw [← pkg.range_eq]
    exact exists_modeOperator_eq_iff hcrit hfv hnr y
  refine ⟨(hker _).2 ⟨1, (one_smul _ _).symm⟩, fun z => (hker z).1 z.2,
    fun y hy => (hran y).1 hy, fun y hy0 hy => ?_⟩
  exact Submodule.disjoint_def.1 pkg.decCodom.isTopCompl.isCompl.disjoint y ((hran y).2 hy) hy0

end TuringModes

end MathlibExt.Biology.Dynamics.TuringBranchesPDE
