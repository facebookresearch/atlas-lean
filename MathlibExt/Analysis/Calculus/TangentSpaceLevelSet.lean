/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Tangent spaces of regular level sets

This file identifies tangent vectors to regular real-valued level sets with the kernel of the
derivative, using curves in the level set as the definition of tangent vectors.
-/

@[expose] public section

namespace MetaMathlibExt

open Filter
open scoped Topology

/-- **Velocities of curves in a level set lie in the kernel of the derivative.** Let $E$ be a
real normed space, $c \in \mathbb{R}$, and $f : E \to \mathbb{R}$ a function differentiable at
$x \in E$. If a curve $\gamma : \mathbb{R} \to E$ satisfies $\gamma(0) = x$, has derivative $v$ at
$0$, and satisfies $f(\gamma(t)) = c$ for all $t \in \mathbb{R}$, then $Df(x)v = 0$.

Proof: Apply the chain rule to `f ∘ γ`, then compare its derivative with that of the constant
function determined by the level-set equation.

Proves `Wanted` entry `levelSet_tangent_vel_of_curve`.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Submanifolds of R^n`, entry `tangent space` (unmapped);
J. M. Lee, Introduction to Smooth Manifolds, 2nd ed., Theorem 5.12;
stable ref https://en.wikipedia.org/wiki/Tangent_space.
-/
theorem levelSet_tangent_vel_of_curve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {c : ℝ} {x v : E}
    (hf : DifferentiableAt ℝ f x)
    {γ : ℝ → E} (hγ0 : γ 0 = x) (hγ : HasDerivAt γ v 0)
    (hmem : ∀ t, f (γ t) = c) :
    fderiv ℝ f x v = 0 := by
  have hcomp : HasDerivAt (fun t => f (γ t)) (fderiv ℝ f x v) 0 := by
    have hf' : HasFDerivAt f (fderiv ℝ f x) (γ 0) := by
      rw [hγ0]
      exact hf.hasFDerivAt
    exact hf'.comp_hasDerivAt 0 hγ
  have hconst : HasDerivAt (fun t => f (γ t)) 0 0 :=
    (hasDerivAt_const 0 c).congr_of_eventuallyEq <| Filter.Eventually.of_forall hmem
  exact hcomp.unique hconst

/-- A vector in the kernel of a surjective strict derivative is the velocity of a local curve in
the corresponding level set. -/
theorem _root_.HasStrictFDerivAt.exists_levelSet_curve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x v : E}
    (hf : HasStrictFDerivAt f f' x) (hsurj : Function.Surjective f')
    (hmem : f' v = 0) :
    ∃ φ : ℝ → E, φ 0 = x ∧ HasDerivAt φ v 0 ∧ ∀ᶠ t in 𝓝 0, f (φ t) = f x := by
  let w : f'.ker := ⟨v, hmem⟩
  have hrange : f'.range = ⊤ := LinearMap.range_eq_top.2 hsurj
  let φ : ℝ → E := fun t => hf.implicitFunction f f' hrange (f x) (t • w)
  refine ⟨φ, ?_, ?_, ?_⟩
  · simp [φ]
  · have hline : HasDerivAt (fun t : ℝ => t • w) w 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
    have hcomp :=
      (hf.to_implicitFunction hrange).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
    simpa [φ, Function.comp_def, w] using hcomp
  · have hline : Tendsto (fun t : ℝ => t • w) (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt, id_eq, zero_smul] using
        ((hasDerivAt_id (0 : ℝ)).smul_const w).continuousAt
    have hpair : Tendsto (fun t : ℝ => (f x, t • w)) (𝓝 0) (𝓝 (f x, 0)) :=
      tendsto_const_nhds.prodMk_nhds hline
    simpa [φ] using hpair.eventually (hf.map_implicitFunction_eq hrange)

private theorem levelSet_exists_reparametrization (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : ℝ → ℝ, ψ 0 = 0 ∧ HasDerivAt ψ 1 0 ∧ ∀ t, dist (ψ t) 0 < ε := by
  let ψ : ℝ → ℝ := fun t => ε / 2 * Real.arctan (2 * t / ε)
  have hψ0 : ψ 0 = 0 := by
    simp [ψ]
  have hψderiv : HasDerivAt ψ 1 0 := by
    have hinner : HasDerivAt (fun t : ℝ => 2 * t / ε) (2 / ε) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).div_const ε
    have harctan := (Real.hasDerivAt_arctan (2 * 0 / ε)).comp 0 hinner
    have hscaled := harctan.const_mul (ε / 2)
    convert hscaled using 1 <;> simp [ψ, hε.ne']
  refine ⟨ψ, hψ0, hψderiv, ?_⟩
  intro t
  have harctan : |Real.arctan (2 * t / ε)| < 2 := by
    rw [abs_lt]
    constructor
    · calc
        -2 < -(Real.pi / 2) := by linarith [Real.pi_lt_four]
        _ < Real.arctan (2 * t / ε) := Real.neg_pi_div_two_lt_arctan _
    · calc
        Real.arctan (2 * t / ε) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
        _ < 2 := by linarith [Real.pi_lt_four]
  simp only [ψ, Real.dist_eq, sub_zero, abs_mul]
  rw [abs_of_pos (by positivity : 0 < ε / 2)]
  calc
    ε / 2 * |Real.arctan (2 * t / ε)| < ε / 2 * 2 :=
      mul_lt_mul_of_pos_left harctan (by positivity)
    _ = ε := by ring

private theorem levelSet_global_curve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {c : ℝ} {x v : E} {φ : ℝ → E}
    (hφ0 : φ 0 = x) (hφ : HasDerivAt φ v 0)
    (hmem : ∀ᶠ t in 𝓝 0, f (φ t) = c) :
    ∃ γ : ℝ → E, γ 0 = x ∧ HasDerivAt γ v 0 ∧ ∀ t, f (γ t) = c := by
  rcases Metric.eventually_nhds_iff.mp hmem with ⟨ε, hε, hlocal⟩
  rcases levelSet_exists_reparametrization ε hε with ⟨ψ, hψ0, hψ, hψmem⟩
  refine ⟨φ ∘ ψ, ?_, ?_, ?_⟩
  · change φ (ψ 0) = x
    rw [hψ0]
    exact hφ0
  · have hφ_at : HasDerivAt φ v (ψ 0) := by
      rw [hψ0]
      exact hφ
    simpa using hφ_at.scomp 0 hψ
  · intro t
    exact hlocal (hψmem t)

/-- **Kernel vectors are velocities of curves in a regular level set.** Let $E$ be a real
Banach space, $f : E \to \mathbb{R}$ a $C^1$ function, $c \in \mathbb{R}$, and $x \in E$ a point
with $f(x) = c$ at which the derivative $Df(x) : E \to \mathbb{R}$ is surjective. Then for every
$v \in E$ with $Df(x)v = 0$ there is a curve $\gamma : \mathbb{R} \to E$ with $\gamma(0) = x$,
$\gamma'(0) = v$ and $f(\gamma(t)) = c$ for all $t \in \mathbb{R}$.

Proof: Use the implicit function theorem to construct a local curve tangent to the kernel vector,
then compose it with a bounded arctangent reparametrization to obtain a curve on all of `ℝ`
(implicit function theorem, Banach space version:
https://en.wikipedia.org/wiki/Implicit_function_theorem).

Proves `Wanted` entry `levelSet_curve_of_tangent_vel`.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Submanifolds of R^n`, entry `tangent space` (unmapped);
J. M. Lee, Introduction to Smooth Manifolds, 2nd ed., Theorem 5.12.
-/
theorem levelSet_curve_of_tangent_vel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {c : ℝ} {x v : E}
    (hf : ContDiff ℝ 1 f) (hx : f x = c)
    (hsurj : Function.Surjective (fderiv ℝ f x))
    (hmem : fderiv ℝ f x v = 0) :
    ∃ γ : ℝ → E, γ 0 = x ∧ HasDerivAt γ v 0 ∧ ∀ t, f (γ t) = c := by
  have hstrict : HasStrictFDerivAt f (fderiv ℝ f x) x :=
    hf.contDiffAt.hasStrictFDerivAt (by norm_num)
  rcases HasStrictFDerivAt.exists_levelSet_curve hstrict hsurj hmem with
    ⟨φ, hφ0, hφ, hφmem⟩
  have hφmemc : ∀ᶠ t in 𝓝 0, f (φ t) = c :=
    hφmem.mono fun _ ht => ht.trans hx
  exact levelSet_global_curve hφ0 hφ hφmemc

end MetaMathlibExt
