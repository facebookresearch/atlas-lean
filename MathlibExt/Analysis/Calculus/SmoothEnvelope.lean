/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Topology.Order.LocalExtr

/-!
# The smooth envelope theorem

If, for parameters near `θ₀`, `xstar θ` maximizes `x ↦ F (x, θ)` over an open choice set, and `F`
and `xstar` are differentiable, then the value function is differentiable at `θ₀` and its
derivative is the partial derivative of `F` in the parameter at the optimizer.

## i. Overview

Maximizers are stated with Mathlib's `IsMaxOn` plus membership in the choice set. At an attained
maximum the value equals the objective at the maximizer (`valueFunction_eq_of_isMaxOn`), so near
`θ₀` the value function is `θ ↦ F (xstar θ, θ)`. The
chain rule gives its derivative, and the choice term vanishes by the interior first-order
condition (`IsLocalMax.hasFDerivAt_eq_zero`). Uniqueness of the maximizer is not needed. No
nonsmooth or parameter-dependent-feasible-set envelope theorem is claimed.

## ii. Main results

* `MathlibExt.Envelope.valueFunction_eq_of_isMaxOn`
* `MathlibExt.Envelope.hasFDerivAt_valueFunction`

## iii. References

* C. P. Simon and L. Blume, *Mathematics for Economists*, Theorem 19.4.
-/

@[expose] public section

open Filter Topology

namespace MathlibExt.Envelope

/-- The value function `V θ = sup {F (x, θ) | x ∈ U}`. As a real supremum it is meaningful when
the supremum is attained (`valueFunction_eq_of_isMaxOn`). -/
noncomputable def valueFunction {E P : Type*} (F : E × P → ℝ) (U : Set E) (θ : P) : ℝ :=
  sSup ((fun x => F (x, θ)) '' U)

/-- At an attained maximum the value is the objective at the maximizer: if `x ∈ U` maximizes
`y ↦ F (y, θ)` on `U` (Mathlib's `IsMaxOn`), then `valueFunction F U θ = F (x, θ)`. -/
theorem valueFunction_eq_of_isMaxOn {E P : Type*} {F : E × P → ℝ} {U : Set E} {θ : P}
    {x : E} (hx : x ∈ U) (h : IsMaxOn (fun y => F (y, θ)) U x) :
    valueFunction F U θ = F (x, θ) := by
  have hmem : F (x, θ) ∈ (fun x => F (x, θ)) '' U := Set.mem_image_of_mem _ hx
  have hub : ∀ b ∈ (fun x => F (x, θ)) '' U, b ≤ F (x, θ) := by
    rintro b ⟨y, hyU, rfl⟩
    exact isMaxOn_iff.mp h y hyU
  exact IsGreatest.csSup_eq (s := (fun x => F (x, θ)) '' U) (a := F (x, θ)) ⟨hmem, hub⟩

/-- **Smooth envelope theorem.** Let `U` be open, let `xstar θ` maximize `F (·, θ)` on `U` for
every `θ` near `θ₀`, and let `F` (jointly, at `(xstar θ₀, θ₀)`) and `xstar` (at `θ₀`) be
differentiable. Then the value function has derivative `F' ∘ inr` at `θ₀`: only the direct
effect of the parameter counts, because the choice derivative vanishes at the interior optimum.
Uniqueness of the maximizer is not needed; it only makes `xstar` the canonical selection. -/
theorem hasFDerivAt_valueFunction {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] {F : E × P → ℝ} {U : Set E} {xstar : P → E}
    {θ₀ : P} {F' : E × P →L[ℝ] ℝ} {xstar' : P →L[ℝ] E} (hU : IsOpen U)
    (hopt : ∀ᶠ θ in 𝓝 θ₀, xstar θ ∈ U ∧ IsMaxOn (fun y => F (y, θ)) U (xstar θ))
    (hF : HasFDerivAt F F' (xstar θ₀, θ₀)) (hx : HasFDerivAt xstar xstar' θ₀) :
    HasFDerivAt (valueFunction F U) (F'.comp (ContinuousLinearMap.inr ℝ E P)) θ₀ := by
  have heq : valueFunction F U =ᶠ[𝓝 θ₀] fun θ => F (xstar θ, θ) :=
    hopt.mono fun θ hθ => valueFunction_eq_of_isMaxOn hθ.1 hθ.2
  have hmax0 : xstar θ₀ ∈ U ∧ IsMaxOn (fun y => F (y, θ₀)) U (xstar θ₀) := hopt.self_of_nhds
  have hloc : IsLocalMax (fun x => F (x, θ₀)) (xstar θ₀) :=
    hmax0.2.isLocalMax (hU.mem_nhds hmax0.1)
  have hpart : HasFDerivAt (fun x => F (x, θ₀))
      (F'.comp (ContinuousLinearMap.inl ℝ E P)) (xstar θ₀) :=
    hF.comp (xstar θ₀) (hasFDerivAt_prodMk_left (xstar θ₀) θ₀)
  have hFOC : F'.comp (ContinuousLinearMap.inl ℝ E P) = 0 :=
    hloc.hasFDerivAt_eq_zero hpart
  have hcongr : F'.comp (xstar'.prod (ContinuousLinearMap.id ℝ P))
      = F'.comp (ContinuousLinearMap.inr ℝ E P) := by
    apply ContinuousLinearMap.ext
    intro p
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.inr_apply]
    show F' (xstar' p, p) = F' ((0 : E), p)
    have h0 : F' (xstar' p, (0 : P)) = 0 := by
      have h := congrArg (fun G : E →L[ℝ] ℝ => G (xstar' p)) hFOC
      simpa using h
    have hsplit : (xstar' p, p) = (xstar' p, (0 : P)) + ((0 : E), p) := by
      rw [Prod.mk_add_mk, add_zero, zero_add]
    calc F' (xstar' p, p)
        = F' ((xstar' p, (0 : P)) + ((0 : E), p)) := by rw [← hsplit]
      _ = F' (xstar' p, (0 : P)) + F' ((0 : E), p) := map_add _ _ _
      _ = F' ((0 : E), p) := by rw [h0, zero_add]
  have hcomp : HasFDerivAt (fun θ => F (xstar θ, θ))
      (F'.comp (xstar'.prod (ContinuousLinearMap.id ℝ P))) θ₀ :=
    HasFDerivAt.comp (f := fun θ => (xstar θ, θ)) θ₀ hF (hx.prodMk (hasFDerivAt_id θ₀))
  rw [hcongr] at hcomp
  exact hcomp.congr_of_eventuallyEq heq

end MathlibExt.Envelope
