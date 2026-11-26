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

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.InducedCompletion
public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.CompactRangeDense

import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Induced tensor completion and amplification compacts

For a complex Hilbert space `H` and nonunital C-star algebra `A`, let `ρ : A ⊗_ℂ K(H) →
K_A(Space H A)` be the algebraic compact tensor homomorphism and put `p(z) = ‖ρ(z)‖`. The
induced completion `C_p` is the completion of the quotient by the zero-seminorm tensors.

The extension `ρ̄ : C_p → K_A(Space H A)` is isometric and has dense range, so it is bijective
and defines a star-algebra equivalence. For the completion inclusion `j`, its core and inverse
formulas are `ρ̄(j z) = ρ(z)` and `ρ̄⁻¹(ρ(z)) = j z`, and `‖ρ̄ x‖ = ‖x‖` for every completed
element. The seminorm in this construction is the compact-action seminorm `p`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra ComplexOrder RightActions TensorProduct Topology

namespace CStarModule.HilbertAmplification

noncomputable section

universe uH uA

variable (H : Type uH) (A : Type uA)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NonUnitalCStarAlgebra A]

/-- **Density of the completed compact tensor map.** For complex Hilbert `H` and nonunital `A`,
the map from the induced completion for `p(z)=‖algebraicCompactTensorHom H A z‖` to
`CompactAlgebra H A` has dense range. -/
theorem denseRange_compactTensorCompletionToCompacts :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
      compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    DenseRange (compactTensorCompletionToCompacts H A) := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
    compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  have hsubset : Set.range (algebraicCompactTensorHom H A) ⊆
      Set.range (compactTensorCompletionToCompacts H A) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨toCompactTensorCompletion H A z, compactTensorCompletionToCompacts_apply H A z⟩
  exact (denseRange_algebraicCompactTensorHom H A).mono hsubset

/-- **Bijective compact tensor completion map.** The isometric completed map
`compactTensorCompletionToCompacts H A` is bijective onto the amplification compact algebra,
since its complete range is closed and its image is dense. -/
theorem bijective_compactTensorCompletionToCompacts :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
      compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    Function.Bijective (compactTensorCompletionToCompacts H A) := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
    compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  have hi := isometry_compactTensorCompletionToCompacts H A
  have hclosed : IsClosed (Set.range (compactTensorCompletionToCompacts H A)) :=
    hi.isClosedEmbedding.isClosed_range
  have hdense : Dense (Set.range (compactTensorCompletionToCompacts H A)) :=
    denseRange_compactTensorCompletionToCompacts H A
  have hrange : Set.range (compactTensorCompletionToCompacts H A) = Set.univ :=
    hclosed.closure_eq.symm.trans hdense.closure_eq
  refine ⟨hi.injective, ?_⟩
  intro x
  have hx : x ∈ Set.range (compactTensorCompletionToCompacts H A) := by
    rw [hrange]
    trivial
  exact hx

/-- **Equivalence of induced tensor completion and compacts.** For complex Hilbert `H` and
nonunital `A`, this is the star-algebra equivalence `CompactTensorCompletion H A ≃
CompactAlgebra H A` given by the completed compact tensor homomorphism. -/
def compactTensorCompletionEquiv :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
      compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    CompactTensorCompletion H A ≃⋆ₐ[ℂ] CompactAlgebra H A := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
    compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact StarAlgEquiv.ofBijective (compactTensorCompletionToCompacts H A)
    (bijective_compactTensorCompletionToCompacts H A)

/-- **Value of the induced completion equivalence.** For `x : CompactTensorCompletion H A`,
`compactTensorCompletionEquiv H A x = compactTensorCompletionToCompacts H A x`. -/
theorem compactTensorCompletionEquiv_apply (x : CompactTensorCompletion H A) :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
      compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    compactTensorCompletionEquiv H A x = compactTensorCompletionToCompacts H A x := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
    compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  rfl

/-- **Completion equivalence on the algebraic core.** For `z : A ⊗_ℂ K(H)`, the completion
equivalence sends `toCompactTensorCompletion H A z` to `algebraicCompactTensorHom H A z`. -/
theorem compactTensorCompletionEquiv_toCompletion
    (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
      compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    compactTensorCompletionEquiv H A (toCompactTensorCompletion H A z) =
      algebraicCompactTensorHom H A z := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
    compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact compactTensorCompletionToCompacts_apply H A z

/-- **Inverse equivalence on an algebraic compact image.** For `z : A ⊗_ℂ K(H)`,
`(compactTensorCompletionEquiv H A).symm (algebraicCompactTensorHom H A z) =
toCompactTensorCompletion H A z`. -/
theorem compactTensorCompletionEquiv_symm_algebraic
    (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
      compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    (compactTensorCompletionEquiv H A).symm (algebraicCompactTensorHom H A z) =
      toCompactTensorCompletion H A z := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
    compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  have h := (compactTensorCompletionEquiv H A).symm_apply_apply (toCompactTensorCompletion H A z)
  rw [compactTensorCompletionEquiv_toCompletion] at h
  exact h

/-- **Norm of the induced completion equivalence.** For every completed tensor `x`,
`‖compactTensorCompletionEquiv H A x‖ = ‖x‖` with the norm induced by the compact-action
seminorm. -/
theorem norm_compactTensorCompletionEquiv (x : CompactTensorCompletion H A) :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
      compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    ‖compactTensorCompletionEquiv H A x‖ = ‖x‖ := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
    compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact norm_compactTensorCompletionToCompacts H A x

end

end CStarModule.HilbertAmplification
