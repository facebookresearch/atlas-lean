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
# The actual onto comparison for the induced compact tensor completion

The original algebraic tensor images are dense in actual compacts and are
values of the existing completed homomorphism on its canonical core. That
completed map is already an actual isometry, so its complete source gives
closed range. Density and closedness therefore give surjectivity, and the
stock bijective star-hom constructor yields an actual star-algebra equivalence.

Its original core values, inverse core values and norms are retained. This
compares the actually induced seminorm completion with its actual compact
module presentation. Raw injectivity and equality with the original least
C-star cross norm remain separate required minimum bridges; no terminal
Takai or minimum faithfulness proof is inferred.
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

/-- The original dense algebraic compact images lie in the actually constructed completion-map range. -/
theorem denseRange_compactTensorCompletionToCompacts :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    DenseRange (compactTensorCompletionToCompacts H A) := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  have hsubset : Set.range (algebraicCompactTensorHom H A) ⊆
      Set.range (compactTensorCompletionToCompacts H A) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨toCompactTensorCompletion H A z, compactTensorCompletionToCompacts_apply H A z⟩
  exact (denseRange_algebraicCompactTensorHom H A).mono hsubset

/-- Actual isometry, completeness and dense image make the existing completed star hom bijective. -/
theorem bijective_compactTensorCompletionToCompacts :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    Function.Bijective (compactTensorCompletionToCompacts H A) := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
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

/-- The genuine bijective completed star hom as an actual equivalence of the original two carriers. -/
def compactTensorCompletionEquiv :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    CompactTensorCompletion H A ≃⋆ₐ[ℂ] CompactAlgebra H A := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact StarAlgEquiv.ofBijective (compactTensorCompletionToCompacts H A)
    (bijective_compactTensorCompletionToCompacts H A)

/-- The equivalence retains the same actual completed homomorphism value on every element. -/
theorem compactTensorCompletionEquiv_apply (x : CompactTensorCompletion H A) :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    compactTensorCompletionEquiv H A x = compactTensorCompletionToCompacts H A x := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  rfl

/-- Every original canonical raw image has its unchanged actual compact tensor value. -/
theorem compactTensorCompletionEquiv_toCompletion (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    compactTensorCompletionEquiv H A (toCompactTensorCompletion H A z) =
      algebraicCompactTensorHom H A z := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact compactTensorCompletionToCompacts_apply H A z

/-- The actual inverse sends each original algebraic compact image back to its canonical completion image. -/
theorem compactTensorCompletionEquiv_symm_algebraic (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    (compactTensorCompletionEquiv H A).symm (algebraicCompactTensorHom H A z) =
      toCompactTensorCompletion H A z := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  have h := (compactTensorCompletionEquiv H A).symm_apply_apply (toCompactTensorCompletion H A z)
  rw [compactTensorCompletionEquiv_toCompletion] at h
  exact h

/-- The actual equivalence preserves the norm computed from the same original compact-action seminorm. -/
theorem norm_compactTensorCompletionEquiv (x : CompactTensorCompletion H A) :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    ‖compactTensorCompletionEquiv H A x‖ = ‖x‖ := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact norm_compactTensorCompletionToCompacts H A x

end

end CStarModule.HilbertAmplification
