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

public import MathlibExt.Analysis.CStarAlgebra.Landmark
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Isometric Hilbert representations of nonunital C-star algebras

The minimal C-star unitization is a genuine unital C-star algebra. Apply the
existing Gelfand--Naimark construction to that unitization and restrict its
representation along the canonical nonunital inclusion. The inclusion and
the universal representation both preserve the original norm.

No Hilbert model or norm comparison is an input. The representation constructed
here can be degenerate: restriction to its essential Hilbert subspace is a
separate construction. The zero algebra is included.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MathlibExt.Analysis.CStarAlgebra.NonUnitalRepresentation

universe u

/-- **Isometric Hilbert representation of a nonunital C*-algebra.** Let `A` be a nonunital complex
C*-algebra. There is a complete complex Hilbert space `H` and an injective nonunital complex star
homomorphism `ρ : A → B(H)` such that `‖ρ(a)‖ = ‖a‖` for every `a ∈ A`. The Hilbert space may be
chosen in the same universe as `A`. -/
theorem exists_isometric_hilbertRepresentation (A : Type u) [NonUnitalCStarAlgebra A] :
    ∃ (H : Type u) (_hH1 : NormedAddCommGroup H)
      (_hH2 : InnerProductSpace ℂ H) (_hH3 : CompleteSpace H)
      (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      Function.Injective ρ ∧ ∀ a : A, ‖ρ a‖ = ‖a‖ := by
  obtain ⟨H, hH1, hH2, hH3, π, hπinj, hπnorm⟩ :=
    MathlibExt.Analysis.CStarAlgebra.LandmarkWanted.cStarAlgebra_gelfandNaimark
      (Unitization ℂ A)
  let _ : NormedAddCommGroup H := hH1
  let _ : InnerProductSpace ℂ H := hH2
  let _ : CompleteSpace H := hH3
  let ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
    π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  refine ⟨H, hH1, hH2, hH3, ρ, ?_, ?_⟩
  · intro a b hab
    have hunit : (a : Unitization ℂ A) = (b : Unitization ℂ A) := hπinj hab
    exact congrArg (fun z : Unitization ℂ A => z.snd) hunit
  · intro a
    change ‖π (a : Unitization ℂ A)‖ = ‖a‖
    rw [hπnorm, Unitization.norm_inr]

/-- **Faithful Hilbert representation.** Let `A` be a nonunital complex C*-algebra. This consists of a
complete complex Hilbert space `H` in the universe of `A` and an injective nonunital complex star
homomorphism `A → B(H)`. -/
structure FaithfulHilbertRepresentationData (A : Type u) [NonUnitalCStarAlgebra A] where
  /-- The source-sized actual Hilbert carrier. -/
  space : Type u
  /-- Its original normed additive group. -/
  [normed : NormedAddCommGroup space]
  /-- Its original complex Hilbert inner product. -/
  [inner : InnerProductSpace ℂ space]
  /-- Its actual completeness. -/
  [complete : CompleteSpace space]
  /-- The actual nonunital coefficient representation. -/
  representation : A →⋆ₙₐ[ℂ] (space →L[ℂ] space)
  /-- The original representation is faithful. -/
  injective_representation : Function.Injective representation

attribute [instance] FaithfulHilbertRepresentationData.normed
  FaithfulHilbertRepresentationData.inner FaithfulHilbertRepresentationData.complete

/-- **Existence of faithful Hilbert representations.** Let `A` be a nonunital complex C*-algebra. The
collection of faithful representations of `A` on complete complex Hilbert spaces in its universe is
nonempty. -/
theorem faithfulHilbertRepresentationData_nonempty (A : Type u) [NonUnitalCStarAlgebra A] :
    Nonempty (FaithfulHilbertRepresentationData A) := by
  obtain ⟨H, hnorm, hinner, hcomplete, ρ, hρ, _⟩ := exists_isometric_hilbertRepresentation A
  exact ⟨{
    space := H
    normed := hnorm
    inner := hinner
    complete := hcomplete
    representation := ρ
    injective_representation := hρ }⟩

/-- **Chosen faithful Hilbert representation.** Let `A` be a nonunital complex C*-algebra. This chooses
a complete complex Hilbert space in the universe of `A` and a faithful nonunital complex star
representation of `A` on it. -/
noncomputable def faithfulHilbertRepresentationData (A : Type u) [NonUnitalCStarAlgebra A] :
    FaithfulHilbertRepresentationData A := Classical.choice (faithfulHilbertRepresentationData_nonempty A)

/-- **Norm of a faithful Hilbert representation.** Let `A` be a nonunital complex C*-algebra. For every
faithful representation `ρ : A → B(H)` on a complete complex Hilbert space and `a ∈ A`, `‖ρ(a)‖ =
‖a‖`. -/
theorem FaithfulHilbertRepresentationData.norm_representation
    {A : Type u} [NonUnitalCStarAlgebra A] (D : FaithfulHilbertRepresentationData A) (a : A) :
    ‖D.representation a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map D.representation D.injective_representation a

end MathlibExt.Analysis.CStarAlgebra.NonUnitalRepresentation
