/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Distribution.Distribution
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Full derivatives of distributions -/

@[expose] public section

open LineDeriv TopologicalSpace
open scoped Distributions

namespace MathlibExt.Analysis.Distribution.DistributionFderivWanted

-- In finite dimension the joint evaluation is a finite sum of continuous terms.
private theorem fullDerivativeFinite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Ω : Opens E} {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] :
    ∃ D : 𝓓'(Ω, F) →L[ℝ] (E →L[ℝ] 𝓓'(Ω, F)), ∀ T v, D T v = ∂_{v} T := by
  let B := Module.finBasis ℝ E
  let V := 𝓓'(Ω, F)
  let c (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp B.equivFunL.toContinuousLinearMap
  let L (i : Fin (Module.finrank ℝ E)) : V →L[ℝ] V := Distribution.lineDerivCLM (B i)
  let A : V →ₗ[ℝ] (E →L[ℝ] V) :=
    ∑ i, ((c i).smulRightₗ : V →ₗ[ℝ] (E →L[ℝ] V)).comp (L i).toLinearMap
  have hA (T : V) (v : E) : A T v = ∑ i, c i v • L i T := by
    simp only [A, LinearMap.sum_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_smulRightₗ, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_coe, sum_apply]
  have hcont : Continuous A := by
    apply ContinuousLinearMap.continuous_of_continuous_uncurry A
    simp_rw [hA]
    exact continuous_finsetSum _ fun i _ =>
      ((c i).continuous.comp continuous_snd).smul ((L i).continuous.comp continuous_fst)
  refine ⟨⟨A, hcont⟩, fun T v => ?_⟩
  change A T v = ∂_{v} T
  rw [hA]
  have hv : ∑ i, c i v • B i = v := by
    simpa only [c, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearMap.proj_apply, Module.Basis.equivFunL_apply, Module.Basis.equivFun_apply]
      using B.sum_repr v
  conv_rhs => rw [← hv]
  simp only [lineDerivOp_left_sum, lineDerivOp_left_smul,
    Distribution.lineDerivOp_eq_lineDerivCLM, L]

/--
**The full derivative of a distribution.** Let $E$ be a real normed space, $\Omega \subseteq E$
an open set and $F$ a real topological vector space, and let $\mathcal{D}'(\Omega, F)$ be the
space of $F$-valued distributions on $\Omega$ (continuous linear maps from the real-valued test
functions on $\Omega$ to $F$), with the topology of uniform convergence on compact sets of test
functions. For $v \in E$ and $T \in \mathcal{D}'(\Omega, F)$, let $\partial_v T$ be the
directional derivative $\varphi \mapsto -T(\partial_v \varphi)$. Then there is a continuous
linear map $D$ from $\mathcal{D}'(\Omega, F)$ to the space of continuous linear maps
$E \to \mathcal{D}'(\Omega, F)$ (with the topology of uniform convergence on bounded sets) such
that $D(T)(v) = \partial_v T$ for every $T \in \mathcal{D}'(\Omega, F)$ and every $v \in E$.

Sources: Mathlib `docs/undergrad.yaml`, section "Distribution calculus" /
"Distributions on R^d" / entry "derivative of a distribution";
L. Schwartz, *Théorie des distributions*, Ch. II.
-/
public theorem exists_fderiv_distribution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
    {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] :
    ∃ D : 𝓓'(Ω, F) →L[ℝ] (E →L[ℝ] 𝓓'(Ω, F)), ∀ T v, D T v = ∂_{v} T := by
  by_cases hE : FiniteDimensional ℝ E
  · let _ : FiniteDimensional ℝ E := hE
    exact fullDerivativeFinite
  · -- In infinite-dimensional normed spaces every continuous compactly supported test function
  -- is zero. No extra hypothesis is needed on the distribution's value space.
    refine ⟨0, fun T v => ?_⟩
    ext f
    have hf : f = (0 : 𝓓(Ω, ℝ)) := by
      apply DFunLike.coe_injective
      exact (f.hasCompactSupport.eq_zero_or_finiteDimensional ℝ f.continuous).resolve_right hE
    simp [hf]

end MathlibExt.Analysis.Distribution.DistributionFderivWanted
