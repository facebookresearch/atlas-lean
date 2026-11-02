/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

/-!
# Fredholm alternative for compact self-adjoint operators

For a compact self-adjoint operator `T` on a Hilbert space and a nonzero scalar
`μ`, the operator `μ • 1 - T` has closed range, its range is exactly the
orthogonal complement of its kernel, and either it is bijective or its kernel
(the eigenspace of `T` for the eigenvalue `μ`) is nontrivial and
finite-dimensional.

This strengthens Mathlib's Fredholm alternative for compact operators
(`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`), which only gives the
dichotomy "either `μ` is an eigenvalue of `T` or `μ` is in the resolvent set
of `T`": in the eigenvalue case it says nothing about the range or the
kernel, and in the resolvent case it does not spell out the range identity.
The key extra step, proved here, is that in the eigenvalue case the range of
`μ • 1 - T` still equals `(ker (μ • 1 - T))ᗮ`: restrict `T` to the orthogonal
complement of the kernel, where it has no eigenvalue `μ`, apply Mathlib's
Fredholm alternative to the restriction, and lift surjectivity back.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.fredholm_alternative_full`
(Theorem (Fredholm alternative), May 11, 2021). The v1 statement uses
`μ • id - T` with `μ ∈ 𝕜`; the book states it for `A - λ` with
`λ ∈ ℝ ∖ {0\}`. The two forms differ by a sign, so see also
`fredholm_alternative_sub_of_isCompactOperator_isSelfAdjoint` below.
-/

open Function Set Filter Topology
open Module End

namespace MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointFredholmAlternative

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **The kernel of a scalar minus an operator is an eigenspace.** Let $H$ be an inner product
space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $T$ be a bounded linear operator on $H$,
let $I$ be the identity of $H$, and let $\mu \in \mathbb{K}$. Then the kernel of $\mu I - T$
equals the eigenspace $\{x \in H : T x = \mu x\}$ of $T$ for $\mu$. -/
theorem ker_smul_id_sub_eq_eigenspace (T : H →L[𝕜] H) (μ : 𝕜) :
    LinearMap.ker (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap =
      Module.End.eigenspace (T.toLinearMap) μ := by
  ext x
  simp [Module.End.eigenspace, LinearMap.mem_ker, sub_eq_zero]
  exact ⟨Eq.symm, Eq.symm⟩

/-- **Fredholm alternative for compact self-adjoint operators.** Let $H$ be a Hilbert space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $T$ be a compact self-adjoint bounded operator on
$H$, let $I$ be the identity of $H$, and let $\mu \in \mathbb{K}$ with $\mu \neq 0$. Then the range
of $\mu I - T$ equals the orthogonal complement $(\ker(\mu I - T))^\perp$ of its kernel, and either
$\mu I - T$ is bijective, or its kernel is nonzero and finite-dimensional. -/
theorem fredholm_alternative_of_isCompactOperator_isSelfAdjoint
    {T : H →L[𝕜] H} (hT : IsCompactOperator (T : H → H)) (hsa : IsSelfAdjoint T)
    {μ : 𝕜} (hμ : μ ≠ 0) :
    LinearMap.range (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap =
      (LinearMap.ker (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap).orthogonal ∧
    (Function.Bijective (μ • (ContinuousLinearMap.id 𝕜 H) - T) ∨
      (LinearMap.ker (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap ≠ ⊥ ∧
       FiniteDimensional 𝕜
         (LinearMap.ker (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap))) := by
  set S := μ • (ContinuousLinearMap.id 𝕜 H) - T with hSdef
  have hSN : IsStarNormal S := by
    constructor
    have hT' : star T = T := hsa
    simp only [hSdef, star_sub, star_smul, hT', ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_id]
    ext x
    simp only [mul_apply_eq_comp, sub_apply,
      smul_apply, ContinuousLinearMap.id_apply,
      map_sub, map_smul]
    module
  have hort : (LinearMap.range S.toLinearMap).orthogonal = LinearMap.ker S.toLinearMap :=
    ContinuousLinearMap.IsStarNormal.orthogonal_range hSN
  have hKcomplete : CompleteSpace (LinearMap.ker S.toLinearMap)ᗮ :=
    (Submodule.isClosed_orthogonal _).completeSpace_coe
  rcases IsCompactOperator.hasEigenvalue_or_mem_resolventSet hT hμ with heig | hres
  · constructor
    · apply le_antisymm
      · intro y hy
        rw [Submodule.mem_orthogonal']
        intro z hz
        have hz' : z ∈ (LinearMap.range S.toLinearMap).orthogonal := hort ▸ hz
        exact inner_eq_zero_symm.mpr ((Submodule.mem_orthogonal' _ _).mp hz' y hy)
      · intro y hy
        have hTinv : ∀ x ∈ (LinearMap.ker S.toLinearMap)ᗮ,
            T x ∈ (LinearMap.ker S.toLinearMap)ᗮ := by
          intro x hx
          rw [Submodule.mem_orthogonal'] at hx ⊢
          intro z hz
          have hTz : T z = μ • z :=
            (sub_eq_zero.mp (LinearMap.mem_ker.mp hz)).symm
          rw [← ContinuousLinearMap.adjoint_inner_right T x z, hsa.adjoint_eq, hTz,
            inner_smul_right, hx z hz, mul_zero]
        let T' : (LinearMap.ker S.toLinearMap)ᗮ →L[𝕜] (LinearMap.ker S.toLinearMap)ᗮ :=
          { toLinearMap := T.toLinearMap.restrict hTinv
            cont := Continuous.subtype_mk (T.continuous.comp continuous_subtype_val) _ }
        have hT'_compact : IsCompactOperator (T' : _ → _) := hT.restrict' hTinv
        have hT'_no_eig : ¬ HasEigenvalue (T'.toLinearMap : End 𝕜 _) μ := by
          intro h
          rw [hasEigenvalue_iff, Submodule.ne_bot_iff] at h
          obtain ⟨⟨v, hv_mem⟩, hv_eig, hv_ne⟩ := h
          have hTv : T v = μ • v := by
            have h := congr_arg Subtype.val (mem_eigenspace_iff.mp hv_eig)
            simpa [T', LinearMap.restrict_apply] using h
          have hv_ker : (v : H) ∈ LinearMap.ker S.toLinearMap := by
            rw [LinearMap.mem_ker]
            show μ • v - T v = 0
            rw [hTv, sub_self]
          have hmem : v ∈
              (LinearMap.ker S.toLinearMap) ⊓ (LinearMap.ker S.toLinearMap)ᗮ :=
            ⟨hv_ker, hv_mem⟩
          rw [Submodule.inf_orthogonal_eq_bot] at hmem
          exact hv_ne (Subtype.ext ((Submodule.mem_bot 𝕜).mp hmem))
        have hres' := (IsCompactOperator.hasEigenvalue_or_mem_resolventSet hT'_compact hμ)
          |>.resolve_left hT'_no_eig
        have hbij := ContinuousLinearMap.isUnit_iff_bijective.mp
          (spectrum.mem_resolventSet_iff.mp hres')
        obtain ⟨b, hb⟩ := hbij.2 ⟨y, hy⟩
        rw [LinearMap.mem_range]
        refine ⟨(b : H), ?_⟩
        have hT'_val : (T' b : H) = T (b : H) :=
          congr_arg Subtype.val (LinearMap.restrict_apply hTinv b)
        show μ • (b : H) - T (b : H) = y
        rw [Algebra.algebraMap_eq_smul_one] at hb
        have hb_val := congr_arg Subtype.val hb
        simpa [hT'_val] using hb_val
    · right
      rw [ker_smul_id_sub_eq_eigenspace]
      exact ⟨hasEigenvalue_iff.mp heig,
        ContinuousLinearMap.finite_dimensional_eigenspace hT μ hμ⟩
  · rw [spectrum.mem_resolventSet_iff, ContinuousLinearMap.isUnit_iff_bijective] at hres
    have hbij : Function.Bijective (S : H → H) := by convert hres using 1
    exact ⟨by rw [LinearMap.range_eq_top.mpr hbij.2, LinearMap.ker_eq_bot.mpr hbij.1,
        Submodule.bot_orthogonal_eq_top],
      Or.inl hbij⟩

/-- **Closed range for compact self-adjoint perturbations of nonzero scalars.** Let $H$ be a
Hilbert space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $T$ be a compact self-adjoint
bounded operator on $H$, let $I$ be the identity of $H$, and let $\mu \in \mathbb{K}$ with
$\mu \neq 0$. Then the range of $\mu I - T$ is a closed subset of $H$. -/
theorem isClosed_range_smul_id_sub_of_isCompactOperator_isSelfAdjoint
    {T : H →L[𝕜] H} (hT : IsCompactOperator (T : H → H)) (hsa : IsSelfAdjoint T)
    {μ : 𝕜} (hμ : μ ≠ 0) :
    IsClosed (LinearMap.range (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap : Set H) := by
  rw [(fredholm_alternative_of_isCompactOperator_isSelfAdjoint hT hsa hμ).1]
  exact Submodule.isClosed_orthogonal _

/-- **Fredholm alternative for compact self-adjoint operators, operator-minus-scalar form.**
Let $H$ be a Hilbert space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $T$ be a compact
self-adjoint bounded operator on $H$, let $I$ be the identity of $H$, and let $\mu \in \mathbb{K}$
with $\mu \neq 0$. Then the range of $T - \mu I$ equals the orthogonal complement
$(\ker(T - \mu I))^\perp$ of its kernel, and either $T - \mu I$ is bijective, or its kernel is
nonzero and finite-dimensional.

This differs from the $\mu I - T$ form of the Fredholm alternative only by a sign. -/
theorem fredholm_alternative_sub_of_isCompactOperator_isSelfAdjoint
    {T : H →L[𝕜] H} (hT : IsCompactOperator (T : H → H)) (hsa : IsSelfAdjoint T)
    {μ : 𝕜} (hμ : μ ≠ 0) :
    LinearMap.range (T - μ • (ContinuousLinearMap.id 𝕜 H)).toLinearMap =
      (LinearMap.ker (T - μ • (ContinuousLinearMap.id 𝕜 H)).toLinearMap).orthogonal ∧
    (Function.Bijective (T - μ • (ContinuousLinearMap.id 𝕜 H)) ∨
      (LinearMap.ker (T - μ • (ContinuousLinearMap.id 𝕜 H)).toLinearMap ≠ ⊥ ∧
       FiniteDimensional 𝕜
         (LinearMap.ker (T - μ • (ContinuousLinearMap.id 𝕜 H)).toLinearMap))) := by
  have h := fredholm_alternative_of_isCompactOperator_isSelfAdjoint hT hsa hμ
  have hneg : T - μ • (ContinuousLinearMap.id 𝕜 H) =
      -(μ • (ContinuousLinearMap.id 𝕜 H) - T) := by
    rw [neg_sub]
  rw [hneg]
  have hrange : LinearMap.range (-(μ • (ContinuousLinearMap.id 𝕜 H) - T)).toLinearMap =
      LinearMap.range (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap := by
    rw [ContinuousLinearMap.toLinearMap_neg, LinearMap.range_neg]
  have hker : LinearMap.ker (-(μ • (ContinuousLinearMap.id 𝕜 H) - T)).toLinearMap =
      LinearMap.ker (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap := by
    rw [ContinuousLinearMap.toLinearMap_neg, LinearMap.ker_neg]
  have hneg_bij : Function.Bijective (Neg.neg : H → H) := (Equiv.neg H).bijective
  have hbij : Function.Bijective (-(μ • (ContinuousLinearMap.id 𝕜 H) - T)) ↔
      Function.Bijective (μ • (ContinuousLinearMap.id 𝕜 H) - T) := by
    constructor
    · intro hb
      have hcomp : Function.Bijective
          (Neg.neg ∘ (-(μ • (ContinuousLinearMap.id 𝕜 H) - T)) : H → H) :=
        hneg_bij.comp hb
      have heq : (Neg.neg ∘ (-(μ • (ContinuousLinearMap.id 𝕜 H) - T)) : H → H) =
          (μ • (ContinuousLinearMap.id 𝕜 H) - T) := by
        funext x
        simp
      rwa [heq] at hcomp
    · intro hb
      have hcomp : Function.Bijective
          (Neg.neg ∘ (μ • (ContinuousLinearMap.id 𝕜 H) - T) : H → H) :=
        hneg_bij.comp hb
      have heq : (Neg.neg ∘ (μ • (ContinuousLinearMap.id 𝕜 H) - T) : H → H) =
          (-(μ • (ContinuousLinearMap.id 𝕜 H) - T)) := by
        funext x
        simp
      rwa [heq] at hcomp
  rw [hrange, hker, hbij]
  exact h

end MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointFredholmAlternative
