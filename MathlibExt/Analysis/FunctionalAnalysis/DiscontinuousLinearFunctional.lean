/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.DiscontinuousLinearFunctional

/-!
# Discontinuous linear functionals on infinite-dimensional normed spaces

On a finite-dimensional normed space every linear functional is continuous
(`LinearMap.continuous_of_finiteDimensional`). The converse is also true:
an infinite-dimensional normed space always carries a discontinuous linear
functional. The proof fixes a Hamel basis, picks a countably infinite
subfamily of basis vectors, and defines a functional that sends the `n`-th
such basis vector to `n` times its norm; rescaling the `n`-th vector to
unit length shows the functional is unbounded on the unit sphere, hence
discontinuous.

Source: this combines material from
`v1/Atlas/IntroductionToFunctionalAnalysis/code/`: the definition of a Hamel
basis in `HahnBanach.lean` (`HahnBanach.IsHamelBasis`, February 25, 2021
lecture) and the finite-dimensionality theme of the Baire-category material
in `BaireCategory.lean`. Neither v1 statement is ported here; the theorem
is a new consequence of the Hamel-basis definition, proved from scratch.
No completeness hypothesis is used: the statement holds for any normed
space, not only for Banach spaces. It is not in the pinned Mathlib:
Mathlib has the finite-dimensional direction
(`LinearMap.continuous_of_finiteDimensional`) and Hamel bases
(`Module.Basis.ofVectorSpace`), but no lemma producing a discontinuous
linear functional from infinite-dimensionality.
-/

/-- **A discontinuous linear functional on an infinite-dimensional normed space.** Let $E$ be a
normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. If $E$ is not finite-dimensional,
then there exists a linear functional $f \colon E \to \mathbb{K}$ that is not continuous. -/
theorem exists_discontinuous_linearMap_of_not_finiteDimensional
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hE : ¬ FiniteDimensional 𝕜 E) :
    ∃ f : E →ₗ[𝕜] 𝕜, ¬ Continuous f := by
  classical
  -- Fix a Hamel basis of `E`.
  set b : Module.Basis (Module.Basis.ofVectorSpaceIndex 𝕜 E) 𝕜 E :=
    Module.Basis.ofVectorSpace 𝕜 E with hb
  -- Infinite-dimensionality means the basis index type is infinite.
  have hInf : Infinite (Module.Basis.ofVectorSpaceIndex 𝕜 E) := by
    rw [← not_finite_iff_infinite]
    intro hfin
    have hfinI := hfin
    exact hE (Module.Basis.finiteDimensional_of_finite b)
  have hInfI := hInf
  -- Pick a countably infinite subfamily of basis vectors, indexed by `ℕ`.
  set e : ℕ ↪ Module.Basis.ofVectorSpaceIndex 𝕜 E :=
    (Set.Infinite.natEmbedding Set.univ (Set.infinite_univ (α := _))).trans
      (Function.Embedding.subtype (· ∈ (Set.univ : Set _))) with he
  -- The coefficients: the `n`-th chosen basis vector is sent to `n` times its norm.
  set c : Module.Basis.ofVectorSpaceIndex 𝕜 E → 𝕜 :=
    fun i => ((↑(Function.invFun (⇑e) i) * ‖b i‖ : ℝ) : 𝕜) with hc
  set f : E →ₗ[𝕜] 𝕜 := b.constr 𝕜 c with hf
  refine ⟨f, ?_⟩
  intro hcont
  -- A continuous linear map is bounded: `‖f x‖ ≤ C * ‖x‖` for some `C > 0`.
  obtain ⟨C, _hCpos, hC⟩ := SemilinearMapClass.bound_of_continuous f hcont
  obtain ⟨n, hn⟩ := exists_nat_gt C
  -- The test vector: the `n`-th chosen basis vector, rescaled to unit length.
  set v : E := b (e n) with hv
  have hv_ne : v ≠ 0 := b.ne_zero _
  have hnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  set s : 𝕜 := ((‖v‖⁻¹ : ℝ) : 𝕜) with hs
  set x : E := s • v with hx
  have hx_norm : ‖x‖ = 1 := by
    rw [hx, norm_smul, hs, RCLike.norm_ofReal,
      abs_of_pos (inv_pos.mpr hnorm_pos)]
    exact inv_mul_cancel₀ hnorm_pos.ne'
  -- `f` sends the unscaled basis vector to `n` times its norm.
  have hfv : f v = (((n : ℝ) * ‖v‖ : ℝ) : 𝕜) := by
    rw [hv, hf, b.constr_basis 𝕜 c (e n)]
    simp only [hc]
    have hinv : Function.invFun (⇑e) (e n) = n :=
      Function.leftInverse_invFun e.injective n
    rw [← hv, hinv]
  -- Hence `f` sends the rescaled (unit) vector to `n`.
  have hfx : f x = (n : 𝕜) := by
    rw [hx, f.map_smul, hfv, hs, smul_eq_mul]
    calc (((‖v‖⁻¹ : ℝ) : 𝕜) * (((n : ℝ) * ‖v‖ : ℝ) : 𝕜))
        = (((‖v‖⁻¹ : ℝ) * ((n : ℝ) * ‖v‖) : ℝ) : 𝕜) := by
          push_cast
          ring
      _ = (((n : ℝ) : 𝕜)) := by
          congr 1
          calc (‖v‖⁻¹ : ℝ) * ((n : ℝ) * ‖v‖)
              = (n : ℝ) * (‖v‖⁻¹ * ‖v‖) := by ring
            _ = (n : ℝ) * 1 := by rw [inv_mul_cancel₀ hnorm_pos.ne']
            _ = (n : ℝ) := mul_one _
      _ = (n : 𝕜) := by
          push_cast
          ring
  -- But `‖f x‖ = n` contradicts the bound `‖f x‖ ≤ C * ‖x‖ = C < n`.
  have hle := hC x
  rw [hx_norm, mul_one, hfx, norm_natCast] at hle
  exact absurd hle (not_le_of_gt hn)

/-- **Every linear functional is continuous if and only if the space is finite-dimensional.**
Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Every linear
functional $f \colon E \to \mathbb{K}$ is continuous if and only if $E$ is finite-dimensional. -/
theorem forall_linearMap_continuous_iff_finiteDimensional
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    (∀ f : E →ₗ[𝕜] 𝕜, Continuous f) ↔ FiniteDimensional 𝕜 E := by
  constructor
  · intro h
    by_contra hE
    obtain ⟨f, hf⟩ := exists_discontinuous_linearMap_of_not_finiteDimensional hE
    exact hf (h f)
  · intro hfd f
    exact LinearMap.continuous_of_finiteDimensional f

/-- **The algebraic dual is strictly larger than the topological dual.** Let $E$ be a normed
space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. If $E$ is not finite-dimensional, then
there is a linear functional $f \colon E \to \mathbb{K}$ that differs from every continuous
linear functional $g \colon E \to \mathbb{K}$. -/
theorem exists_linearMap_not_continuousLinearMap
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hE : ¬ FiniteDimensional 𝕜 E) :
    ∃ f : E →ₗ[𝕜] 𝕜, ∀ g : E →L[𝕜] 𝕜, f ≠ (g : E →ₗ[𝕜] 𝕜) := by
  obtain ⟨f, hf⟩ := exists_discontinuous_linearMap_of_not_finiteDimensional hE
  refine ⟨f, fun g hg => ?_⟩
  subst hg
  exact hf g.continuous

end MathlibExt.Analysis.FunctionalAnalysis.DiscontinuousLinearFunctional
