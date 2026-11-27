/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Regular level sets as local graphs

This file proves that a level set of a continuously differentiable map is locally a graph at
points where its derivative is surjective.
-/

@[expose] public section

open scoped Topology

noncomputable section

namespace MathlibExt.Geometry.Manifold.LocalGraphWanted

/-- A surjective linear map is the second coordinate of a linear equivalence once the
dimensions match. -/
private theorem localGraph_splitEquiv
    {E G F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →L[ℝ] F) (hA : Function.Surjective A)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ G + Module.finrank ℝ F) :
    ∃ e : E ≃L[ℝ] G × F, ∀ x, (e x).2 = A x := by
  let K := LinearMap.ker (A : E →ₗ[ℝ] F)
  obtain ⟨K', hKK'⟩ := K.exists_isCompl
  let P : E →L[ℝ] K := (K.projectionOnto K' hKK').toContinuousLinearMap
  have hdimK : Module.finrank ℝ K = Module.finrank ℝ G := by
    have h := LinearMap.finrank_range_add_finrank_ker (A : E →ₗ[ℝ] F)
    rw [LinearMap.range_eq_top.mpr hA] at h
    simp only [finrank_top] at h
    change Module.finrank ℝ F + Module.finrank ℝ K = Module.finrank ℝ E at h
    omega
  let i : K ≃L[ℝ] G := ContinuousLinearEquiv.ofFinrankEq hdimK
  let T : E →L[ℝ] G × F := ((i : K →L[ℝ] G).comp P).prod A
  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hAx : A x = 0 := congrArg Prod.snd hx
    have hxK : x ∈ K := by
      change A x = 0
      exact hAx
    have hPzero : P x = 0 := by
      apply i.injective
      simpa [T] using congrArg Prod.fst hx
    have hPid : P x = ⟨x, hxK⟩ := by
      simpa [P] using K.projectionOnto_apply_left hKK' ⟨x, hxK⟩
    rw [hPzero] at hPid
    simpa using congrArg Subtype.val hPid.symm
  have hdim' : Module.finrank ℝ E = Module.finrank ℝ (G × F) := by
    simpa only [Module.finrank_prod] using hdim
  let e :=
    (LinearMap.linearEquivOfInjective (T : E →ₗ[ℝ] G × F) hTinj hdim').toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  intro x
  rfl

/-- **Local graph form of a level set near a regular point.** Let $E$, $G$ and $F$ be
finite-dimensional real normed spaces with $\dim E = \dim G + \dim F$, let $f \colon E \to F$ be
a $C^1$ map and let $x_0 \in E$ be a point at which the derivative $Df(x_0)$ is surjective. Then
there exist a continuous linear isomorphism $e \colon E \to G \times F$, a neighbourhood $U$ in
$G$ of the first component of $e(x_0)$, a map $g \colon G \to F$ that is $C^1$ on $U$, and a
neighbourhood $V$ of $x_0$ such that a point $x \in V$ satisfies $f(x) = f(x_0)$ if and only if
$e(x) = (u, g(u))$ for some $u \in U$. -/
theorem _root_.ContDiff.exists_localGraph_of_surjective_fderiv
    {E G F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ G + Module.finrank ℝ F)
    (f : E → F) (hf : ContDiff ℝ 1 f) (x₀ : E)
    (hreg : Function.Surjective (fderiv ℝ f x₀)) :
    ∃ (e : E ≃L[ℝ] G × F)
      (U : Set G) (_ : U ∈ 𝓝 (e x₀).1) (g : G → F),
      ContDiffOn ℝ 1 g U ∧ ∃ V ∈ 𝓝 x₀, V ∩ f ⁻¹' {f x₀} =
        V ∩ e ⁻¹' {p : G × F | p.1 ∈ U ∧ p.2 = g p.1} := by
  obtain ⟨e, he⟩ := localGraph_splitEquiv (fderiv ℝ f x₀) hreg hdim
  let F' : G × F → F := f ∘ e.symm
  let z₀ : G × F := e x₀
  have hF' : ContDiff ℝ 1 F' := hf.comp e.symm.contDiff
  have hF'At : ContDiffAt ℝ 1 F' z₀ := hF'.contDiffAt
  have hpartial :
      fderiv ℝ F' z₀ ∘L ContinuousLinearMap.inr ℝ G F = ContinuousLinearMap.id ℝ F := by
    ext y
    simpa [F', z₀, ContinuousLinearEquiv.comp_right_fderiv] using
      (he (e.symm (0, y))).symm
  have hInv :
      (fderiv ℝ F' z₀ ∘L ContinuousLinearMap.inr ℝ G F).IsInvertible := by
    rw [hpartial]
    exact ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩
  let g : G → F := hF'At.implicitFunction (by simp) hInv
  have hiff : ∀ᶠ p in 𝓝 z₀, F' p = F' z₀ ↔ g p.1 = p.2 := by
    simpa [g] using hF'At.eventually_apply_eq_iff_implicitFunction (by simp) hInv
  have hgAt : ContDiffAt ℝ 1 g z₀.1 := by
    simpa [g] using hF'At.contDiffAt_implicitFunction (by simp) hInv
  obtain ⟨U, hU, hgU⟩ := hgAt.contDiffOn (m := 1) le_rfl (by simp)
  have hUfst : ∀ᶠ p in 𝓝 z₀, p.1 ∈ U :=
    continuousAt_fst.preimage_mem_nhds hU
  let W := {p : G × F | (F' p = F' z₀ ↔ g p.1 = p.2) ∧ p.1 ∈ U}
  have hW : W ∈ 𝓝 z₀ := by
    exact hiff.and hUfst
  let V := e ⁻¹' W
  have hV : V ∈ 𝓝 x₀ := by
    exact e.continuous.continuousAt.preimage_mem_nhds (by simpa [z₀] using hW)
  refine ⟨e, U, hU, g, hgU, V, hV, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hxV, hfx⟩
    have hxW : (F' (e x) = F' z₀ ↔ g (e x).1 = (e x).2) ∧ (e x).1 ∈ U := by
      simpa [V, W] using hxV
    refine ⟨hxV, hxW.2, ?_⟩
    exact (hxW.1.mp (by simpa [F', z₀] using hfx)).symm
  · rintro ⟨hxV, hxU, hxg⟩
    have hxW : (F' (e x) = F' z₀ ↔ g (e x).1 = (e x).2) ∧ (e x).1 ∈ U := by
      simpa [V, W] using hxV
    refine ⟨hxV, ?_⟩
    simpa [F', z₀] using hxW.1.mpr hxg.symm

/--
**Regular level sets are locally graphs.** Let $f \colon \mathbb{R}^{k+m} \to \mathbb{R}^m$ be a
$C^1$ map and let $x_0 \in \mathbb{R}^{k+m}$ be a point at which the derivative $Df(x_0)$ is
surjective. Then there exist a linear isomorphism
$e \colon \mathbb{R}^{k+m} \to \mathbb{R}^k \times \mathbb{R}^m$, a neighbourhood $U$ in
$\mathbb{R}^k$ of the first component of $e(x_0)$, a map $g \colon \mathbb{R}^k \to \mathbb{R}^m$
that is $C^1$ on $U$, and a neighbourhood $V$ of $x_0$ such that a point $x \in V$ satisfies
$f(x) = f(x_0)$ if and only if $e(x) = (u, g(u))$ for some $u \in U$.

Proves `Wanted` entry `regularLevelSet_localGraph`.

Proof: A projection onto the derivative kernel supplies adapted linear coordinates. The
product-space implicit function theorem then identifies the level set with a local `C¹` graph
(https://en.wikipedia.org/wiki/Implicit_function_theorem).

Sources:
undergrad.yaml `Submanifolds of R^n / local graphs` (missing); J. Lee, Introduction to
Smooth Manifolds, 2nd ed., Ch. 4 (rank theorem).
-/
theorem regularLevelSet_localGraph
    {k m : ℕ}
    (f : EuclideanSpace ℝ (Fin (k + m)) → EuclideanSpace ℝ (Fin m))
    (hf : ContDiff ℝ 1 f) (x₀ : EuclideanSpace ℝ (Fin (k + m)))
    (hreg : Function.Surjective (fderiv ℝ f x₀)) :
    ∃ (e : EuclideanSpace ℝ (Fin (k + m)) ≃L[ℝ]
          (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)))
      (U : Set (EuclideanSpace ℝ (Fin k))) (_ : U ∈ 𝓝 ((e x₀).1))
      (g : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)),
      ContDiffOn ℝ 1 g U ∧ ∃ V ∈ 𝓝 x₀, V ∩ f ⁻¹' {f x₀}
        = V ∩ e ⁻¹' {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) |
          p.1 ∈ U ∧ p.2 = g p.1} := by
  exact ContDiff.exists_localGraph_of_surjective_fderiv
    (by simp only [finrank_euclideanSpace_fin]) f hf x₀ hreg

end MathlibExt.Geometry.Manifold.LocalGraphWanted
