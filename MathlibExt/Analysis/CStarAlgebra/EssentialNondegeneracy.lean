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

public import MathlibExt.Analysis.CStarAlgebra.EssentialRepresentation

/-!
# The neutral essential-space condition for nondegeneracy

Use the already defined essential closed span equal to the entire Hilbert
space. Its equivalence with density of the original operator-range span
bridges all source formulations. The actual essential restriction satisfies
this same condition. No second nondegeneracy predicate or supplied support
model is introduced.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace NonUnitalStarAlgHom

noncomputable section

universe uA uH

variable {A : Type uA} [NonUnitalNonAssocSemiring A] [DistribMulAction ℂ A] [Star A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Characterization of the essential space.** Let `H` be a complete complex Hilbert space and let `A`
be a nonunital, possibly nonassociative semiring with a distributive complex scalar action and a
star operation. Let `ρ : A → B(H)` preserve addition, multiplication, complex scalars, and star. The
essential space of `ρ` is all of `H` exactly when the complex-linear span of `{ρ(a)ξ : a ∈ A, ξ ∈
H}` is norm-dense in `H`. -/
theorem essentialSpace_eq_top_iff_dense (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    ρ.essentialSpace = ⊤ ↔
      Dense (Submodule.span ℂ (Set.range fun z : A × H => ρ z.1 z.2) : Set H) := by
  change (Submodule.span ℂ (Set.range fun z : A × H => ρ z.1 z.2)).topologicalClosure = ⊤ ↔ _
  exact (Submodule.dense_iff_topologicalClosure_eq_top :
    Dense (Submodule.span ℂ (Set.range fun z : A × H => ρ z.1 z.2) : Set H) ↔
      (Submodule.span ℂ (Set.range fun z : A × H => ρ z.1 z.2)).topologicalClosure = ⊤).symm

/-- **Essential restriction has full essential space.** Let `H` be a complete complex Hilbert space and
let `A` be a nonunital, possibly nonassociative semiring with a distributive complex scalar action
and a star operation. Let `ρ : A → B(H)` preserve addition, multiplication, complex scalars, and
star. The representation restricted to its closed essential subspace has that whole subspace as its
essential space. -/
theorem essentialRepresentation_essentialSpace_eq_top (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    ρ.essentialRepresentation.essentialSpace = ⊤ :=
  (essentialSpace_eq_top_iff_dense ρ.essentialRepresentation).mpr ρ.nondegenerate_essentialRepresentation

end

end NonUnitalStarAlgHom
