/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Field.Krasner

/-!
# Closest conjugates and Krasner's lemma

This file defines when an algebraic element is closer to one element than to all of its
other conjugates, and connects this condition to Krasner's lemma.
-/

@[expose] public section

namespace AlgebraicClosure

/-- **Closest conjugate.** Let $K$ be a normed field with algebraic closure $\overline{K}$, and
let $\lVert \cdot \rVert$ be the spectral norm on $\overline{K}$ over $K$. For
$\alpha, \beta \in \overline{K}$, $\alpha$ is the closest conjugate to $\beta$ if
$\lVert \beta - \alpha \rVert < \lVert \beta - \sigma(\alpha) \rVert$ for every $K$-algebra
automorphism $\sigma$ of $\overline{K}$ with $\sigma(\alpha) \ne \alpha$. -/
def IsClosestConjugate (K : Type*) [NormedField K]
    (α β : AlgebraicClosure K) : Prop :=
  ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
    σ α ≠ α →
    spectralNorm K (AlgebraicClosure K) (β - α) <
      spectralNorm K (AlgebraicClosure K) (β - σ α)

/-- **Closest conjugates satisfy Krasner's hypothesis.** Let $K$ be a complete nontrivially
normed field whose norm is ultrametric, with algebraic closure $\overline{K}$, let
$\lVert \cdot \rVert$ be the spectral norm on $\overline{K}$ over $K$, and let
$\alpha, \beta, \alpha' \in \overline{K}$. If $\alpha$ is the closest conjugate to $\beta$ and
$\alpha' \ne \alpha$ is a conjugate of $\alpha$ over $K$, then
$\lVert \alpha - \beta \rVert < \lVert \alpha - \alpha' \rVert$. -/
theorem IsClosestConjugate.lt_spectralNorm_sub_of_isConjRoot
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {α β α' : AlgebraicClosure K} (h : IsClosestConjugate K α β)
    (hconj : IsConjRoot K α α') (hne : α ≠ α') :
    spectralNorm K (AlgebraicClosure K) (α - β) <
      spectralNorm K (AlgebraicClosure K) (α - α') := by
  let _ : NormedField (AlgebraicClosure K) := spectralNorm.normedField K _
  let _ : NormedAlgebra K (AlgebraicClosure K) := spectralNorm.normedAlgebra K _
  have _ : IsUltrametricDist (AlgebraicClosure K) :=
    IsUltrametricDist.of_normedAlgebra K
  rw [isConjRoot_iff_exists_algEquiv] at hconj
  obtain ⟨σ, hσ⟩ := hconj
  have hα' : α' = σ.symm α := by
    rw [← hσ]
    simp
  have hne' : σ.symm α ≠ α := by
    rw [← hα']
    exact hne.symm
  have hclose := h σ.symm hne'
  rw [← NormedAlgebra.norm_eq_spectralNorm K,
      ← NormedAlgebra.norm_eq_spectralNorm K] at hclose ⊢
  subst hα'
  rw [norm_sub_rev α β]
  by_contra hle
  push Not at hle
  have h_ultra : ‖β - σ.symm α‖ ≤ max ‖β - α‖ ‖α - σ.symm α‖ := by
    have : β - σ.symm α = (β - α) + (α - σ.symm α) := by abel
    rw [this]
    exact IsUltrametricDist.norm_add_le_max _ _
  linarith [max_le (le_refl ‖β - α‖) hle]

/-- **Krasner's lemma for closest conjugates.** Let $K$ be a complete nontrivially normed field
whose norm is ultrametric, with algebraic closure $\overline{K}$, and let
$\alpha, \beta \in \overline{K}$. If $\alpha$ is the closest conjugate to $\beta$ and $\alpha$ is
separable over $K$, then $K(\alpha) \subseteq K(\beta)$. -/
theorem IsClosestConjugate.adjoin_le
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {α β : AlgebraicClosure K} (h : IsClosestConjugate K α β)
    (hsep : IsSeparable K α) :
    IntermediateField.adjoin K {α} ≤ IntermediateField.adjoin K {β} := by
  let _ : NormedField (AlgebraicClosure K) := spectralNorm.normedField K _
  let _ : NormedAlgebra K (AlgebraicClosure K) := spectralNorm.normedAlgebra K _
  have _ : IsUltrametricDist (AlgebraicClosure K) :=
    IsUltrametricDist.of_normedAlgebra K
  rw [IntermediateField.adjoin_simple_le_iff]
  apply IsKrasner.krasner hsep
  · exact IsAlgClosed.splits _
  · exact (Algebra.IsAlgebraic.isAlgebraic β).isIntegral
  · intro α' hconj hne
    simpa only [NormedAlgebra.norm_eq_spectralNorm K] using
      h.lt_spectralNorm_sub_of_isConjRoot hconj hne

end AlgebraicClosure
