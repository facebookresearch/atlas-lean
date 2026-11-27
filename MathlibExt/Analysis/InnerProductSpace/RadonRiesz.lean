/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin

@[expose] public section

/-!
# Radon–Riesz (Kadec–Klee) property in Hilbert spaces

In a Hilbert space, weak convergence together with convergence of the
norms implies convergence in norm: if `u n` converges weakly to `x`
and `‖u n‖ → ‖x‖`, then `u n → x` in norm. The proof is the
parallelogram-law computation
`‖u n - x‖² = ‖u n‖² - 2 re ⟪u n, x⟫ + ‖x‖² → 0`.
No completeness hypothesis is needed: the statement holds in any
inner product space. It is the converse direction to the already-known
fact that norm convergence implies weak convergence, so the two
together give an iff (see `tendsto_iff_tendsto_inner_and_tendsto_norm`).

This is a companion to the weak-convergence material in
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean`
(continuity of the inner product, Bessel's inequality, Parseval's
identity) and to the weak convergence of orthonormal sequences.
It is not one of the 72 v1 targets, and it is in neither the pinned
Mathlib nor base MathlibExt: Mathlib has the ingredients
(`norm_sub_sq`, continuity of the inner product, the weak-space
characterisation of convergence) but not this sequential statement.
See e.g. Brezis, *Functional Analysis, Sobolev Spaces and PDEs*,
Chapter 3, and Rudin, *Functional Analysis*, Chapter 4.
-/

open Set Filter Topology RCLike
open scoped InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.RadonRiesz

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- From convergence of `re ⟪u n, x⟫` and of the norms, deduce norm
convergence, via `‖u n - x‖² = ‖u n‖² - 2 re ⟪u n, x⟫ + ‖x‖²`. -/
private theorem tendsto_of_tendsto_re_inner_and_tendsto_norm {u : ℕ → H} {x : H}
    (hre : Tendsto (fun n => re ⟪u n, x⟫_𝕜) atTop (𝓝 (‖x‖ ^ 2)))
    (hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖x‖)) :
    Tendsto u atTop (𝓝 x) := by
  have hnormSq : Tendsto (fun n => ‖u n‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) := by
    simpa [pow_two] using hnorm.mul hnorm
  have h2 : Tendsto (fun n => 2 * re ⟪u n, x⟫_𝕜) atTop (𝓝 (2 * ‖x‖ ^ 2)) :=
    hre.const_mul 2
  have h3 : Tendsto (fun n => ‖u n‖ ^ 2 - 2 * re ⟪u n, x⟫_𝕜) atTop
      (𝓝 (‖x‖ ^ 2 - 2 * ‖x‖ ^ 2)) :=
    Filter.Tendsto.sub hnormSq h2
  have hcomb : Tendsto (fun n => ‖u n‖ ^ 2 - 2 * re ⟪u n, x⟫_𝕜 + ‖x‖ ^ 2)
      atTop (𝓝 (‖x‖ ^ 2 - 2 * ‖x‖ ^ 2 + ‖x‖ ^ 2)) :=
    Filter.Tendsto.add h3 tendsto_const_nhds
  have hlim : (‖x‖ ^ 2 - 2 * ‖x‖ ^ 2 + ‖x‖ ^ 2 : ℝ) = 0 := by ring
  rw [hlim] at hcomb
  have hsq : Tendsto (fun n => ‖u n - x‖ ^ 2) atTop (𝓝 0) :=
    hcomb.congr fun n => (norm_sub_sq (u n) x).symm
  have hnorm0 : Tendsto (fun n => ‖u n - x‖) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hsq
    have h2 := h.congr fun n => Real.sqrt_sq (norm_nonneg (u n - x))
    simpa using h2
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [dist_eq_norm] using hnorm0

/-- **Radon–Riesz theorem, inner-product form.** Let $H$ be an inner product space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, not necessarily complete, let
$(u_n)_{n \in \mathbb{N}}$ be a sequence in $H$ and let $x \in H$. If
$\langle u_n, y \rangle \to \langle x, y \rangle$ for every $y \in H$ and $\|u_n\| \to \|x\|$,
then $u_n \to x$ in norm. -/
theorem tendsto_of_tendsto_inner_and_tendsto_norm {u : ℕ → H} {x : H}
    (hinner : ∀ y : H, Tendsto (fun n => ⟪u n, y⟫_𝕜) atTop (𝓝 ⟪x, y⟫_𝕜))
    (hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖x‖)) :
    Tendsto u atTop (𝓝 x) := by
  apply tendsto_of_tendsto_re_inner_and_tendsto_norm (𝕜 := 𝕜) _ hnorm
  have h := ((RCLike.continuous_re (K := 𝕜)).tendsto _).comp (hinner x)
  rwa [inner_self_eq_norm_sq] at h

/-- **Radon–Riesz theorem, dual-functionals form.** Let $H$ be an inner product space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, not necessarily complete, let
$(u_n)_{n \in \mathbb{N}}$ be a sequence in $H$ and let $x \in H$. If $f(u_n) \to f(x)$ for
every continuous linear functional $f : H \to \mathbb{K}$ and $\|u_n\| \to \|x\|$, then
$u_n \to x$ in norm. -/
theorem tendsto_of_forall_tendsto_and_tendsto_norm {u : ℕ → H} {x : H}
    (h : ∀ f : StrongDual 𝕜 H, Tendsto (fun n => f (u n)) atTop (𝓝 (f x)))
    (hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖x‖)) :
    Tendsto u atTop (𝓝 x) := by
  apply tendsto_of_tendsto_re_inner_and_tendsto_norm (𝕜 := 𝕜) _ hnorm
  have h := ((RCLike.continuous_re (K := 𝕜)).tendsto _).comp (h (innerSL 𝕜 x))
  -- `innerSL 𝕜 x (u n) = ⟪x, u n⟫`, and `re ⟪x, u n⟫ = re ⟪u n, x⟫`.
  simpa only [Function.comp_def, innerSL_apply_apply, inner_re_symm,
    inner_self_eq_norm_sq] using h

/-- Weak convergence in `toWeakSpace` form implies the all-functionals form. -/
private theorem forall_tendsto_of_tendsto_weakSpace {u : ℕ → H} {x : H}
    (h : Tendsto (fun n => toWeakSpace 𝕜 H (u n)) atTop (𝓝 (toWeakSpace 𝕜 H x))) :
    ∀ f : StrongDual 𝕜 H, Tendsto (fun n => f (u n)) atTop (𝓝 (f x)) := by
  have hinj : Function.Injective (LinearMap.flip (topDualPairing 𝕜 H)) := by
    intro a b hab
    exact SeparatingDual.eq_iff_forall_dual_eq.mpr fun f =>
      congrFun (congrArg DFunLike.coe hab) f
  exact (WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing 𝕜 H).flip hinj).mp h

/-- **Radon–Riesz theorem, weak-topology form.** Let $H$ be an inner product space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, not necessarily complete, let
$(u_n)_{n \in \mathbb{N}}$ be a sequence in $H$ and let $x \in H$. If $u_n \to x$ in the weak
topology of $H$ (the coarsest topology making every continuous linear functional
$H \to \mathbb{K}$ continuous) and $\|u_n\| \to \|x\|$, then $u_n \to x$ in norm. -/
theorem tendsto_of_tendsto_weakSpace_and_tendsto_norm {u : ℕ → H} {x : H}
    (h : Tendsto (fun n => toWeakSpace 𝕜 H (u n)) atTop (𝓝 (toWeakSpace 𝕜 H x)))
    (hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖x‖)) :
    Tendsto u atTop (𝓝 x) :=
  tendsto_of_forall_tendsto_and_tendsto_norm (forall_tendsto_of_tendsto_weakSpace h) hnorm

/-- **Radon–Riesz characterization of norm convergence.** Let $H$ be an inner product space
over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, not necessarily complete, let
$(u_n)_{n \in \mathbb{N}}$ be a sequence in $H$ and let $x \in H$. Then $u_n \to x$ in norm if
and only if $\langle u_n, y \rangle \to \langle x, y \rangle$ for every $y \in H$ and
$\|u_n\| \to \|x\|$. -/
theorem tendsto_iff_tendsto_inner_and_tendsto_norm {u : ℕ → H} {x : H} :
    Tendsto u atTop (𝓝 x) ↔
      (∀ y : H, Tendsto (fun n => ⟪u n, y⟫_𝕜) atTop (𝓝 ⟪x, y⟫_𝕜)) ∧
        Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖x‖) := by
  refine ⟨fun h => ⟨fun y => h.inner tendsto_const_nhds, h.norm⟩, fun h => ?_⟩
  exact tendsto_of_tendsto_inner_and_tendsto_norm h.1 h.2

end MathlibExt.Analysis.InnerProductSpace.RadonRiesz
