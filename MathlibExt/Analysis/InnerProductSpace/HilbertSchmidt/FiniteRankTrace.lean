/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Module.LinearMap.FiniteRange
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Trace
public import MathlibExt.Analysis.InnerProductSpace.CompactOperator.FiniteRankClosure
public import MathlibExt.Analysis.Normed.Operator.FiniteRank
public import MathlibExt.Analysis.InnerProductSpace.Adjoint.OneSided

/-!
# Finite-rank range trace and Hilbert–Schmidt functions

Let H,K,L be complex normed spaces in independent universes, and let F(H,K) be the submodule
of bounded linear maps H→K with finite-dimensional range. A finite-rank endomorphism T of H
has trace tr(T|range T), taken on its finite-dimensional range. If H is a Hilbert space and K
an inner product space, the finite-rank coefficient functions are I(S,T)=tr(S†∘T) and
N(T)=√Re(I(T,T)), using the complete-source adjoint. These finite-rank and trace formulas
occur in Conway, Functional Analysis VI.3.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ContinuousLinearMap

universe uH uK uL

section NormedSpaces
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {K : Type uK} [NormedAddCommGroup K] [NormedSpace ℂ K]
variable {L : Type uL} [NormedAddCommGroup L] [NormedSpace ℂ L]

/-- **Left composition of a bounded finite-rank map.**

Let H,K,L be complex normed spaces in independent universes, and let F(H,K) be the submodule
of bounded linear maps H→K with finite-dimensional range. For R:K→L bounded linear and
T∈F(H,K), finiteRankComposeLeft R T∈F(H,L) is R∘T.
-/
def finiteRankComposeLeft (R : K →L[ℂ] L) (T : finiteRankOperator (𝕜 := ℂ) (E := H) (F := K)) :
    finiteRankOperator (𝕜 := ℂ) (E := H) (F := L) :=
  ⟨R.comp T.val, by
    apply (mem_finiteRankOperator _).2
    change (R.toLinearMap.comp T.val.toLinearMap).HasFiniteRange
    exact ((mem_finiteRankOperator T.val).1 T.property).comp_left R.toLinearMap⟩

/-- **Bounded map underlying finite-rank left composition.**

Let H,K,L be complex normed spaces in independent universes, and let F(H,K) be the submodule
of bounded linear maps H→K with finite-dimensional range. For R:K→L bounded linear and
T∈F(H,K), the bounded map underlying finiteRankComposeLeft R T is R∘T.
-/
theorem finiteRankComposeLeft_coe (R : K →L[ℂ] L) (T : finiteRankOperator (𝕜 := ℂ) (E := H) (F := K)) :
    (finiteRankComposeLeft R T : H →L[ℂ] L) = R.comp T.val := rfl

/-- **Trace of a finite-rank endomorphism on its range.**

Let H be a complex normed space and T:H→H a bounded finite-rank endomorphism. The scalar
finiteRankRangeTrace T is the finite-dimensional trace of the restriction
T|range(T):range(T)→range(T).
-/
def finiteRankRangeTrace (T : finiteRankOperator (𝕜 := ℂ) (E := H) (F := H)) : ℂ :=
  LinearMap.trace ℂ T.val.range
    (T.val.toLinearMap.rangeRestrict.domRestrict T.val.range)

end NormedSpaces

section HilbertSpaces
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- **Finite-rank maps equal the rank-one span for a complete domain.**

Let H be a complete complex inner product space and K a complex inner product space, possibly
incomplete. For a bounded S:H→K, let S†:K→H be its complete-source adjoint, characterized by
⟪Sx,y⟫=⟪x,S†y⟫. Let F(H,K) denote the bounded finite-rank maps. The submodule F(H,K) equals
span_ℂ{θ_(y,x):y∈K,x∈H}, where θ_(y,x)(z)=⟪x,z⟫•y. Completeness is required for H, while K may
be incomplete.
-/
theorem finiteRankOperator_eq_finiteRankSubmodule :
    finiteRankOperator (𝕜 := ℂ) (E := H) (F := K) =
      InnerProductSpace.finiteRankSubmodule (𝕜 := ℂ) (E := H) (F := K) := by
  classical
  apply le_antisymm
  · intro T hT
    let : IsNoetherian ℂ T.range :=
      ((mem_finiteRankOperator T).1 hT).hasNoetherianRange
    let : FiniteDimensional ℂ T.range := inferInstance
    let b : OrthonormalBasis (Fin (Module.finrank ℂ T.range)) ℂ T.range :=
      stdOrthonormalBasis ℂ T.range
    have hProjection : T.range.starProjection =
        ∑ i, InnerProductSpace.rankOne ℂ (b i : K) (b i : K) :=
      b.starProjection_eq_sum_rankOne
    have hFactor : T.range.starProjection.comp T = T := by
      apply ContinuousLinearMap.ext
      intro x
      exact T.range.starProjection_eq_self_iff.mpr ⟨x, rfl⟩
    have hSum : T = ∑ i, InnerProductSpace.rankOne ℂ (b i : K)
        ((ContinuousLinearMap.adjointOfCompleteSource T) (b i : K)) := by
      calc
        T = T.range.starProjection.comp T := hFactor.symm
        _ = (∑ i, InnerProductSpace.rankOne ℂ (b i : K) (b i : K)).comp T :=
          congrArg (fun P : K →L[ℂ] K => P.comp T) hProjection
        _ = ∑ i, (InnerProductSpace.rankOne ℂ (b i : K) (b i : K)).comp T := by
          ext x
          simp
        _ = ∑ i, InnerProductSpace.rankOne ℂ (b i : K)
            ((ContinuousLinearMap.adjointOfCompleteSource T) (b i : K)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          ext x
          simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply]
          rw [ContinuousLinearMap.adjointOfCompleteSource_inner_left]
    rw [hSum]
    exact Submodule.sum_mem _ fun i _ =>
      InnerProductSpace.rankOne_mem_finiteRankSubmodule (b i : K)
        ((ContinuousLinearMap.adjointOfCompleteSource T) (b i : K))
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    apply (mem_finiteRankOperator _).2
    change (InnerProductSpace.rankOne ℂ x y).toLinearMap.HasFiniteRange
    have hSpan : (ContinuousLinearMap.toSpanSingleton ℂ x).toLinearMap.HasFiniteRange :=
      LinearMap.HasFiniteRange.of_finite_dom
    have hRank : (InnerProductSpace.rankOne ℂ x y).toLinearMap.HasFiniteRange := by
      rw [InnerProductSpace.rankOne_def', ContinuousLinearMap.toLinearMap_comp]
      exact hSpan.comp_right (innerSL ℂ y).toLinearMap
    exact hRank

omit [CompleteSpace K] in
/-- **Finite-rank Hilbert–Schmidt inner function.**

Let H be a complete complex inner product space and K a complex inner product space, possibly
incomplete. For a bounded S:H→K, let S†:K→H be its complete-source adjoint, characterized by
⟪Sx,y⟫=⟪x,S†y⟫. Let F(H,K) denote the bounded finite-rank maps. For S,T∈F(H,K),
finiteRankHilbertSchmidtInner S T=finiteRankRangeTrace(S†∘T), with the trace taken on the
finite-dimensional range of S†∘T.
-/
def finiteRankHilbertSchmidtInner (S T : finiteRankOperator (𝕜 := ℂ) (E := H) (F := K)) : ℂ :=
  finiteRankRangeTrace (finiteRankComposeLeft (ContinuousLinearMap.adjointOfCompleteSource S.val) T)

omit [CompleteSpace K] in
/-- **Square-root finite-rank Hilbert–Schmidt function.**

Let H be a complete complex inner product space and K a complex inner product space, possibly
incomplete. For a bounded S:H→K, let S†:K→H be its complete-source adjoint, characterized by
⟪Sx,y⟫=⟪x,S†y⟫. Let F(H,K) denote the bounded finite-rank maps. For T∈F(H,K),
finiteRankHilbertSchmidtNorm T=√Re(finiteRankHilbertSchmidtInner T T)=√Re(tr(T†∘T)), using the
nonnegative real square root.
-/
def finiteRankHilbertSchmidtNorm (T : finiteRankOperator (𝕜 := ℂ) (E := H) (F := K)) : ℝ :=
  Real.sqrt (finiteRankHilbertSchmidtInner T T).re

omit [CompleteSpace K] in
/-- **Complete-source adjoint trace formula for the inner function.**

Let H be a complete complex inner product space and K a complex inner product space, possibly
incomplete. For a bounded S:H→K, let S†:K→H be its complete-source adjoint, characterized by
⟪Sx,y⟫=⟪x,S†y⟫. Let F(H,K) denote the bounded finite-rank maps. For S,T∈F(H,K),
finiteRankHilbertSchmidtInner S T=finiteRankRangeTrace(finiteRankComposeLeft S† T).
-/
theorem finiteRankHilbertSchmidtInner_def (S T : finiteRankOperator (𝕜 := ℂ) (E := H) (F := K)) :
    finiteRankHilbertSchmidtInner S T =
      finiteRankRangeTrace (finiteRankComposeLeft (ContinuousLinearMap.adjointOfCompleteSource S.val) T) := rfl

/-- **Ordinary adjoint trace formula on two Hilbert spaces.**

Let H,K be complete complex inner product spaces and S,T:H→K bounded finite-rank maps. Then
finiteRankHilbertSchmidtInner S T=finiteRankRangeTrace(S.adjoint∘T), the trace of S†T on its
finite-dimensional range.
-/
theorem finiteRankHilbertSchmidtInner_eq_trace_adjoint
    (S T : finiteRankOperator (𝕜 := ℂ) (E := H) (F := K)) :
    finiteRankHilbertSchmidtInner S T =
      finiteRankRangeTrace (finiteRankComposeLeft S.val.adjoint T) := by
  rw [finiteRankHilbertSchmidtInner_def,
    ContinuousLinearMap.adjointOfCompleteSource_eq_adjoint]

end HilbertSpaces

end ContinuousLinearMap

end
