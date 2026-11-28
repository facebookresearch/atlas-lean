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

public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletion
public import MathlibExt.Analysis.CStarAlgebra.EssentialRepresentation

/-!
# The dense original-source Gram domain in the actual essential Hilbert space

For the same-seminorm completion, take an actual Hilbert representation and
its computed essential restriction. The original-source operator ranges
span a submodule of that actual Hilbert space. The canonical completion map
has dense range, so continuity of each completed coefficient action puts all
completed operator values in this submodule's closure. Essential-space
nondegeneracy then gives density of the original-source span.

The Gram domain has its inherited Hilbert norm. Its generators retain the
original operator values and their inner product is the original star-product
Gram form. No normed structure on the raw source is assumed or constructed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace CStarAlgebra

namespace CStarSeminorm

noncomputable section

universe uB uH

variable {B : Type uB} [NonUnitalRing B] [Module ℂ B]
  [IsScalarTower ℂ B B] [SMulCommClass ℂ B B] [StarRing B] [StarModule ℂ B]

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm B) (H : Type uH)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Hilbert Gram domain from the source algebra.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution, `p` a C*-seminorm on `B`, `H` a complete complex Hilbert space, and
`ρ` a nonunital star representation of the separated C*-completion of `B` on `H`. Write `Eρ` for its
closed essential subspace and `ι` for the completion map. The Gram domain is the complex-linear span
inside `Eρ` of `{ρ(ι(f))ξ : f ∈ B, ξ ∈ Eρ}`, with the inherited inner product and norm. -/
def rawHilbertGramDomain (ρ : p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    Submodule ℂ ρ.essentialSpace :=
  Submodule.span ℂ (Set.range fun z : B × ρ.essentialSpace =>
    ρ.essentialRepresentation (p.toNonUnitalCompletion z.1) z.2)

/-- **Generator of the Hilbert Gram domain.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution, `p` a C*-seminorm on `B`, `H` a complete complex Hilbert space, and
`ρ` a nonunital star representation of the separated C*-completion of `B` on `H`. Write `Eρ` for its
closed essential subspace and `ι` for the completion map. For `f ∈ B` and `ξ ∈ Eρ`, the vector
`ρ(ι(f))ξ` defines a generator in the Gram domain. -/
def rawHilbertGramGenerator (ρ : p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (f : B) (ξ : ρ.essentialSpace) : p.rawHilbertGramDomain H ρ :=
  ⟨ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ,
    Submodule.subset_span ⟨(f, ξ), rfl⟩⟩

/-- **Ambient vector of a Gram generator.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution, `p` a C*-seminorm on `B`, `H` a complete complex Hilbert space, and
`ρ` a nonunital star representation of the separated C*-completion of `B` on `H`. Write `Eρ` for its
closed essential subspace and `ι` for the completion map. Including the Gram generator for `f ∈ B`
and `ξ ∈ Eρ` back into `H` gives `ρ(ι(f))ξ`. -/
@[simp]
theorem rawHilbertGramGenerator_apply_coe
    (ρ : p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (f : B) (ξ : ρ.essentialSpace) :
    ((p.rawHilbertGramGenerator H ρ f ξ : ρ.essentialSpace) : H) =
      ρ (p.toNonUnitalCompletion f) ξ := rfl

/-- **Inner product of Gram generators.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution, `p` a C*-seminorm on `B`, `H` a complete complex Hilbert space, and
`ρ` a nonunital star representation of the separated C*-completion of `B` on `H`. Write `Eρ` for its
closed essential subspace and `ι` for the completion map. For `f,h ∈ B` and `ξ,η ∈ Eρ`, the inner
product of the generators `ρ(ι(f))ξ` and `ρ(ι(h))η` equals `⟨ξ,ρ(ι(f* h))η⟩`. -/
theorem rawHilbertGramGenerator_inner
    (ρ : p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (f h : B)
    (ξ η : ρ.essentialSpace) :
    ⟪p.rawHilbertGramGenerator H ρ f ξ, p.rawHilbertGramGenerator H ρ h η⟫_ℂ =
      ⟪ξ, ρ.essentialRepresentation (p.toNonUnitalCompletion (star f * h)) η⟫_ℂ := by
  let σ := ρ.essentialRepresentation
  let q : B →⋆ₙₐ[ℂ] p.NonUnitalCompletion := p.toNonUnitalCompletion
  change ⟪σ (p.toNonUnitalCompletion f) ξ, σ (p.toNonUnitalCompletion h) η⟫_ℂ =
    ⟪ξ, σ (p.toNonUnitalCompletion (star f * h)) η⟫_ℂ
  have hproduct : σ (p.toNonUnitalCompletion (star f * h)) =
      star (σ (p.toNonUnitalCompletion f)) * σ (p.toNonUnitalCompletion h) := by
    change σ (q (star f * h)) = star (σ (q f)) * σ (q h)
    rw [_root_.map_mul q (star f) h, _root_.map_mul σ (q (star f)) (q h),
      StarHomClass.map_star q f, StarHomClass.map_star σ (q f)]
  rw [hproduct]
  change ⟪σ (p.toNonUnitalCompletion f) ξ, σ (p.toNonUnitalCompletion h) η⟫_ℂ =
    ⟪ξ, star (σ (p.toNonUnitalCompletion f)) (σ (p.toNonUnitalCompletion h) η)⟫_ℂ
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm

/-- **Density of the source Gram domain.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution, `p` a C*-seminorm on `B`, `H` a complete complex Hilbert space, and
`ρ` a nonunital star representation of the separated C*-completion of `B` on `H`. Write `Eρ` for its
closed essential subspace and `ι` for the completion map. The complex-linear span of the
source-generated vectors is norm-dense in `Eρ`. -/
theorem dense_rawHilbertGramDomain (ρ : p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    Dense (p.rawHilbertGramDomain H ρ : Set ρ.essentialSpace) := by
  let D := p.rawHilbertGramDomain H ρ
  let S : Submodule ℂ ρ.essentialSpace := Submodule.span ℂ
    (Set.range fun z : p.NonUnitalCompletion × ρ.essentialSpace =>
      ρ.essentialRepresentation z.1 z.2)
  have hvalues (a : p.NonUnitalCompletion) (ξ : ρ.essentialSpace) :
      ρ.essentialRepresentation a ξ ∈ D.topologicalClosure := by
    refine p.denseRange_toNonUnitalCompletion.induction ?_ ?_ a
    · rintro _ ⟨f, rfl⟩
      exact D.le_topologicalClosure (Submodule.subset_span ⟨(f, ξ), rfl⟩)
    · have hσ : Continuous
          (ρ.essentialRepresentation : p.NonUnitalCompletion →
            (ρ.essentialSpace →L[ℂ] ρ.essentialSpace)) := by
        exact map_continuous ρ.essentialRepresentation
      exact D.isClosed_topologicalClosure.preimage (hσ.clm_apply continuous_const)
  have hSD : S ≤ D.topologicalClosure := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, ξ⟩, rfl⟩
    exact hvalues a ξ
  have hS : S.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp ρ.nondegenerate_essentialRepresentation
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply le_antisymm le_top
  rw [← hS]
  exact S.topologicalClosure_minimal hSD D.isClosed_topologicalClosure

/-- **Dense range of the Gram-domain inclusion.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution, `p` a C*-seminorm on `B`, `H` a complete complex Hilbert space, and
`ρ` a nonunital star representation of the separated C*-completion of `B` on `H`. Write `Eρ` for its
closed essential subspace and `ι` for the completion map. The complex-linear inclusion of the source
Gram domain into `Eρ` has dense range. -/
theorem denseRange_rawHilbertGramDomain_subtype
    (ρ : p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    DenseRange (p.rawHilbertGramDomain H ρ).subtype := by
  let D := p.rawHilbertGramDomain H ρ
  have hrange : Set.range (D.subtype : D → ρ.essentialSpace) = (D : Set ρ.essentialSpace) := by
    ext ξ
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property
    · intro hξ
      exact ⟨⟨ξ, hξ⟩, rfl⟩
  change Dense (Set.range (D.subtype : D → ρ.essentialSpace))
  rw [hrange]
  exact p.dense_rawHilbertGramDomain H ρ

end

end CStarSeminorm
