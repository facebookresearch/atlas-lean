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

public import MathlibExt.Analysis.CStarAlgebra.NonUnitalRepresentation
public import MathlibExt.Analysis.CStarAlgebra.EssentialRepresentation
public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletion

/-!
# Actual nondegenerate Hilbert norm models of nonunital seminorm completions

Compute the same-seminorm separation quotient and ordinary completion. Apply
the existing Gelfand--Naimark construction to its true minimal C-star
unitization, then restrict to the actual essential Hilbert subspace. This
constructs a faithful isometric nondegenerate representation of the completed
algebra. On each canonical source image its operator norm is the original
seminorm, including the zero seminorm.

This supplies the actual Hilbert model needed for covariant norm cofinality.
Coefficient/group operators and the integrated identity remain separate
required constructions; no covariant norm comparison is asserted here.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarSeminorm

universe u

variable {B : Type u} [NonUnitalRing B] [Module ℂ B]
  [IsScalarTower ℂ B B] [SMulCommClass ℂ B B] [StarRing B] [StarModule ℂ B]

/-- **Faithful nondegenerate representation of a C*-seminorm completion.** Let `B` be a nonunital
complex star algebra with scalar-compatible involution and `p` a C*-seminorm. Its separated
C*-completion has an injective isometric star representation `ρ` on a complete complex Hilbert space
in the universe of `B`. For every source element `x`, `‖ρ(ι(x))‖ = p(x)`, and the complex-linear
span of all representation ranges is dense in the Hilbert space. -/
theorem exists_nonUnitalCompletionHilbertNormModel (p : CStarSeminorm B) :
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    ∃ (H : Type u) (_hH1 : NormedAddCommGroup H)
      (_hH2 : InnerProductSpace ℂ H) (_hH3 : CompleteSpace H)
      (ρ : p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      Function.Injective ρ ∧ (∀ y : p.NonUnitalCompletion, ‖ρ y‖ = ‖y‖) ∧
        (∀ x : B, ‖ρ (p.toNonUnitalCompletion x)‖ = p x) ∧
        Dense (Submodule.span ℂ
          (Set.range fun z : p.NonUnitalCompletion × H => ρ z.1 z.2) : Set H) := by
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  dsimp only
  obtain ⟨H, hH1, hH2, hH3, ρ, hρinj, _hρnorm⟩ :=
    MathlibExt.Analysis.CStarAlgebra.NonUnitalRepresentation.exists_isometric_hilbertRepresentation
      p.NonUnitalCompletion
  let _ : NormedAddCommGroup H := hH1
  let _ : InnerProductSpace ℂ H := hH2
  let _ : CompleteSpace H := hH3
  let K : Type u := ρ.essentialSpace
  let σ : p.NonUnitalCompletion →⋆ₙₐ[ℂ] (K →L[ℂ] K) := ρ.essentialRepresentation
  refine ⟨K, inferInstance, inferInstance, inferInstance, σ,
    ρ.injective_essentialRepresentation hρinj, ?_, ?_, ?_⟩
  · intro y
    exact ρ.norm_essentialRepresentation hρinj y
  · intro x
    calc
      ‖σ (p.toNonUnitalCompletion x)‖ = ‖p.toNonUnitalCompletion x‖ :=
        ρ.norm_essentialRepresentation hρinj (p.toNonUnitalCompletion x)
      _ = p x := p.norm_toNonUnitalCompletion x
  · exact ρ.nondegenerate_essentialRepresentation

end CStarSeminorm
