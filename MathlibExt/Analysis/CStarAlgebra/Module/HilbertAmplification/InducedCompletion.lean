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

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.AlgebraicTensorHom
public import MathlibExt.Analysis.CStarAlgebra.SeminormPullback
public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletionHom

/-!
# Completion for the compact-action seminorm

For complex Hilbert `H` and nonunital C-star `A`, let `ρ : A ⊗_ℂ K(H) → CompactAlgebra H A` be
the compact tensor representation. Its induced C-star seminorm is `p(z) = ‖ρ(z)‖`. Quotient by
the zero-seminorm subspace and complete to obtain `CompactTensorCompletion H A`.

The dense canonical map `j` has `‖j z‖ = p(z)`. The extended star homomorphism satisfies `ρ̄(j
z) = ρ(z)` and `‖ρ̄ x‖ = ‖x‖` on the completion, so it is an isometric map into the compact
algebra.
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

/-- **C-star seminorm of the compact tensor action.** For a complex Hilbert space `H` and a
nonunital C-star algebra `A`, define `compactTensorSeminorm H A z = ‖algebraicCompactTensorHom
H A z‖` on the raw algebraic tensor `A ⊗_ℂ K(H)`. -/
def compactTensorSeminorm : CStarSeminorm (A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) := by
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact CStarSeminorm.ofNonUnitalStarAlgHom (algebraicCompactTensorHom H A)

/-- **Value of the induced tensor seminorm.** For a complex Hilbert space `H` and a nonunital
C-star algebra `A`, `compactTensorSeminorm H A z = ‖algebraicCompactTensorHom H A z‖`. -/
theorem compactTensorSeminorm_apply (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    compactTensorSeminorm H A z = ‖algebraicCompactTensorHom H A z‖ := by
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  rfl

/-- **Induced compact tensor completion.** For a complex Hilbert space `H` and a nonunital C-star
algebra `A`, `CompactTensorCompletion H A` is the completion of `A ⊗_ℂ K(H)` after quotienting
by the zero subspace of `p(z)=‖algebraicCompactTensorHom z‖`. -/
abbrev CompactTensorCompletion := (compactTensorSeminorm H A).NonUnitalCompletion

/-- **C-star structure on the induced completion.** For a complex Hilbert space `H` and a
nonunital C-star algebra `A`, the zero-seminorm quotient completion has its nonunital C-star
algebra structure with the completed seminorm `p`. -/
@[instance_reducible]
def compactTensorCompletionCStarAlgebra : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
  (compactTensorSeminorm H A).nonUnitalCompletionCStarAlgebra

/-- **Canonical algebraic tensor inclusion.** For a complex Hilbert space `H` and a nonunital
C-star algebra `A`, the complex nonunital star homomorphism `j : A ⊗_ℂ K(H) →
CompactTensorCompletion H A` is the separation-quotient map followed by completion. -/
def toCompactTensorCompletion :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier →⋆ₙₐ[ℂ] CompactTensorCompletion H A :=
  (compactTensorSeminorm H A).toNonUnitalCompletion

/-- **Norm of an algebraic completion image.** For a complex Hilbert space `H` and a nonunital
C-star algebra `A`, `‖toCompactTensorCompletion H A z‖ = ‖algebraicCompactTensorHom H A z‖`
for every raw tensor `z`. -/
theorem norm_toCompactTensorCompletion (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    ‖toCompactTensorCompletion H A z‖ = ‖algebraicCompactTensorHom H A z‖ := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact ((compactTensorSeminorm H A).norm_toNonUnitalCompletion z).trans
    (compactTensorSeminorm_apply H A z)

/-- **Density of algebraic completion images.** For a complex Hilbert space `H` and a nonunital
C-star algebra `A`, the canonical map `toCompactTensorCompletion H A` has dense range in the
induced tensor completion. -/
theorem denseRange_toCompactTensorCompletion :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    DenseRange (toCompactTensorCompletion H A) := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  exact (compactTensorSeminorm H A).denseRange_toNonUnitalCompletion

/-- **Extended compact tensor homomorphism.** For a complex Hilbert space `H` and a nonunital
C-star algebra `A`, extend `ρ = algebraicCompactTensorHom H A` to the complex nonunital star
homomorphism `ρ̄ : CompactTensorCompletion H A → CompactAlgebra H A`, characterized by `ρ̄(j
z) = ρ(z)`. -/
def compactTensorCompletionToCompacts :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    CompactTensorCompletion H A →⋆ₙₐ[ℂ] CompactAlgebra H A := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact (compactTensorSeminorm H A).fromNonUnitalCompletion (algebraicCompactTensorHom H A)
    (fun z => (compactTensorSeminorm_apply H A z).ge)

/-- **Extended representation on the algebraic core.** For a complex Hilbert space `H` and a
nonunital C-star algebra `A`, `compactTensorCompletionToCompacts H A
(toCompactTensorCompletion H A z) = algebraicCompactTensorHom H A z`. -/
theorem compactTensorCompletionToCompacts_apply (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    compactTensorCompletionToCompacts H A (toCompactTensorCompletion H A z) =
      algebraicCompactTensorHom H A z := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact (compactTensorSeminorm H A).fromNonUnitalCompletion_apply (algebraicCompactTensorHom H A)
    (fun z => (compactTensorSeminorm_apply H A z).ge) z

/-- **Continuity of the induced representation.** For a complex Hilbert space `H` and a nonunital
C-star algebra `A`, the map `compactTensorCompletionToCompacts H A` is continuous for the
induced completion norm and compact-operator norm. -/
theorem continuous_compactTensorCompletionToCompacts :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    Continuous (compactTensorCompletionToCompacts H A) := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact (compactTensorSeminorm H A).continuous_fromNonUnitalCompletion
    (algebraicCompactTensorHom H A) (fun z => (compactTensorSeminorm_apply H A z).ge)

/-- **Norm preservation of the induced representation.** For a complex Hilbert space `H` and a
nonunital C-star algebra `A`, `‖compactTensorCompletionToCompacts H A x‖ = ‖x‖` for every
induced completed tensor `x`. -/
theorem norm_compactTensorCompletionToCompacts (x : CompactTensorCompletion H A) :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    ‖compactTensorCompletionToCompacts H A x‖ = ‖x‖ := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  refine (denseRange_toCompactTensorCompletion H A).induction_on x
    (isClosed_eq (continuous_compactTensorCompletionToCompacts H A).norm continuous_norm) ?_
  intro z
  rw [compactTensorCompletionToCompacts_apply, norm_toCompactTensorCompletion]

/-- **Isometry of the induced representation.** For a complex Hilbert space `H` and a nonunital
C-star algebra `A`, the completed compact tensor homomorphism is an isometry between the
induced completion and the compact algebra. -/
theorem isometry_compactTensorCompletionToCompacts :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    Isometry (compactTensorCompletionToCompacts H A) := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact AddMonoidHomClass.isometry_of_norm (compactTensorCompletionToCompacts H A)
    (norm_compactTensorCompletionToCompacts H A)

end

end CStarModule.HilbertAmplification
