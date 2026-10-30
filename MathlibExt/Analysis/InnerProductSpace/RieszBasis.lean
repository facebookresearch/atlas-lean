/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

@[expose] public section

/-!
# Riesz bases in Hilbert spaces

A family `f : ι → E` in a Hilbert space is a **Riesz basis** (with respect to a
Hilbert basis `b`) if it is the image of `b` under a bounded invertible
operator, `f i = T (b i)`. Riesz bases are the natural "boundedly distorted"
generalization of orthonormal bases: they are no longer orthonormal, but they
keep linear independence, completeness, and a biorthogonal dual family with a
reconstruction formula. See e.g. Christensen, *An Introduction to Frames and
Riesz Bases*, Chapter 3.

This is a companion to the v1 book's Hilbert-space material
(`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`SpectralTheory.lean`): the book treats orthonormal bases (Bessel's inequality,
Parseval's identity, "a separable Hilbert space is isometrically isomorphic to
`ℓ²`"), but none of its 72 targets states anything about Riesz bases. The
Paley–Wiener stability theorem (a Hilbert basis survives a small perturbation)
is in `MathlibExt.Analysis.InnerProductSpace.RieszBasisStability`.

Main results:

* `IsRieszBasis`: `f` is a Riesz basis if `f i = T (b i)` for some
  `T : E ≃L[𝕜] E`.
* `IsRieszBasis.linearIndependent`: a Riesz basis is linearly independent.
* `IsRieszBasis.dense_span`: a Riesz basis has dense span.
* `IsRieszBasis.exists_dual`: a Riesz basis has a biorthogonal dual family
  `g` with `⟪f i, g j⟫ = if i = j then 1 else 0` and the reconstruction
  formula `x = ∑' i, ⟪g i, x⟫ • f i`.
-/

section

open scoped InnerProductSpace

variable {ι 𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace MathlibExt.Analysis.InnerProductSpace.RieszBasis

/-- A family `f : ι → E` is a **Riesz basis** (with respect to the Hilbert basis
`b`) if it is the image of `b` under a bounded invertible operator. -/
def IsRieszBasis (b : HilbertBasis ι 𝕜 E) (f : ι → E) : Prop :=
  ∃ T : E ≃L[𝕜] E, ∀ i, T (b i) = f i

omit [CompleteSpace E] in
/-- A Riesz basis is linearly independent. -/
theorem IsRieszBasis.linearIndependent {b : HilbertBasis ι 𝕜 E} {f : ι → E}
    (h : IsRieszBasis b f) : LinearIndependent 𝕜 f := by
  obtain ⟨T, hT⟩ := h
  have hbi : LinearIndependent 𝕜 b := b.orthonormal.linearIndependent
  have hmap : LinearIndependent 𝕜 (T ∘ ⇑b) :=
    hbi.map' T.toLinearMap (LinearMap.ker_eq_bot.mpr T.toLinearEquiv.injective)
  have hfeq : (T ∘ ⇑b) = f := by
    funext i
    exact hT i
  rw [← hfeq]
  exact hmap

omit [CompleteSpace E] in
/-- A Riesz basis has dense span. -/
theorem IsRieszBasis.dense_span {b : HilbertBasis ι 𝕜 E} {f : ι → E}
    (h : IsRieszBasis b f) : (Submodule.span 𝕜 (Set.range f)).topologicalClosure = ⊤ := by
  obtain ⟨T, hT⟩ := h
  have hrange : Set.range f = (T : E →ₗ[𝕜] E) '' Set.range b := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨b i, ⟨i, rfl⟩, hT i⟩
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hT i).symm⟩
  have hmap : (Submodule.span 𝕜 (Set.range b)).map (T : E →ₗ[𝕜] E)
      = Submodule.span 𝕜 (Set.range f) := by
    rw [Submodule.map_span, hrange]
  have hclosure : ((Submodule.span 𝕜 (Set.range f)).topologicalClosure : Set E)
      = T '' ((Submodule.span 𝕜 (Set.range b)).topologicalClosure : Set E) := by
    rw [← hmap, Submodule.topologicalClosure_coe, Submodule.topologicalClosure_coe,
      Submodule.map_coe]
    exact (T.toHomeomorph.image_closure _).symm
  have hb : ((Submodule.span 𝕜 (Set.range b)).topologicalClosure : Set E)
      = Set.univ := by
    rw [b.dense_span]
    exact Set.eq_univ_of_forall fun _ => Submodule.mem_top
  have hTop : ((Submodule.span 𝕜 (Set.range f)).topologicalClosure : Set E)
      = Set.univ := by
    rw [hclosure, hb, Set.image_univ]
    exact T.surjective.range_eq
  exact SetLike.ext'_iff.mpr hTop

/-- A Riesz basis admits a biorthogonal dual family with a reconstruction
formula: there is `g : ι → E` with `⟪f i, g j⟫ = if i = j then 1 else 0` and
`x = ∑' i, ⟪g i, x⟫ • f i` for every `x`. The dual is `g j = (T⁻¹)† (b j)`
for the operator `T` witnessing that `f` is a Riesz basis. -/
theorem IsRieszBasis.exists_dual {b : HilbertBasis ι 𝕜 E} {f : ι → E}
    [DecidableEq ι] (h : IsRieszBasis b f) :
    ∃ g : ι → E, (∀ i j, ⟪f i, g j⟫_𝕜 = if i = j then 1 else 0) ∧
      ∀ x, HasSum (fun i => ⟪g i, x⟫_𝕜 • f i) x := by
  obtain ⟨T, hT⟩ := h
  refine ⟨fun j => ContinuousLinearMap.adjoint (T.symm : E →L[𝕜] E) (b j), ?_, ?_⟩
  · intro i j
    rw [← hT i, ContinuousLinearMap.adjoint_inner_right]
    have hUT : (T.symm : E →L[𝕜] E) (T (b i)) = b i :=
      ContinuousLinearEquiv.symm_apply_apply T (b i)
    rw [hUT]
    exact orthonormal_iff_ite.mp b.orthonormal i j
  · intro x
    have hsum : HasSum (fun i => ⟪b i, T.symm x⟫_𝕜 • b i) (T.symm x) := by
      refine (b.hasSum_repr (T.symm x)).congr_fun fun i => ?_
      rw [HilbertBasis.repr_apply_apply]
    have hTsum := ((T : E →L[𝕜] E)).hasSum hsum
    have hcoeff : ∀ i, ⟪ContinuousLinearMap.adjoint (T.symm : E →L[𝕜] E) (b i),
        x⟫_𝕜 = ⟪b i, T.symm x⟫_𝕜 := by
      intro i
      exact ContinuousLinearMap.adjoint_inner_left (T.symm : E →L[𝕜] E) x (b i)
    have hval : (T : E →L[𝕜] E) (T.symm x) = x :=
      ContinuousLinearEquiv.apply_symm_apply T x
    rw [hval] at hTsum
    refine hTsum.congr_fun (fun i => ?_)
    have hTi : (T : E →L[𝕜] E) (b i) = f i := hT i
    show ⟪ContinuousLinearMap.adjoint (T.symm : E →L[𝕜] E) (b i), x⟫_𝕜 • f i
        = (T : E →L[𝕜] E) (⟪b i, T.symm x⟫_𝕜 • b i)
    rw [map_smul, hTi, hcoeff]

end MathlibExt.Analysis.InnerProductSpace.RieszBasis

end
