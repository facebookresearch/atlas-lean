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
# The actual completion induced by the original compact tensor action

Pull back the actual CompactAlgebra H A norm along the verified original
algebraic tensor homomorphism. Reuse the existing same-seminorm nonunital
separation/completion engine for its carrier, dictionaries and canonical map.
The same actual homomorphism extends into the original compact algebra; its
completed norm equality follows from the dense original canonical images.

This computes strict carrier/hom/norm prerequisites of the original spatial
minimum target in Blackadar10.1.2. It does not identify the induced seminorm
with the source's least cross norm, select a supplied minimal tensor model,
or prove raw faithfulness, compact range density or the terminal Takai theorem.
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

/-- The original compact-action norm as a genuine C-star seminorm on the same raw tensor. -/
def compactTensorSeminorm : CStarSeminorm (A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) := by
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact CStarSeminorm.ofNonUnitalStarAlgHom (algebraicCompactTensorHom H A)

/-- Every induced seminorm value is exactly the original algebraic compact-action norm. -/
theorem compactTensorSeminorm_apply (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    compactTensorSeminorm H A z = ‖algebraicCompactTensorHom H A z‖ := by
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  rfl

/-- The existing literal same-seminorm separation quotient followed by ordinary completion. -/
abbrev CompactTensorCompletion := (compactTensorSeminorm H A).NonUnitalCompletion

/-- The existing same-seminorm completion dictionary on this actual carrier. -/
@[instance_reducible]
def compactTensorCompletionCStarAlgebra : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
  (compactTensorSeminorm H A).nonUnitalCompletionCStarAlgebra

/-- The canonical raw-tensor map is the existing separation/completion map for this actual gauge. -/
def toCompactTensorCompletion :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier →⋆ₙₐ[ℂ] CompactTensorCompletion H A :=
  (compactTensorSeminorm H A).toNonUnitalCompletion

/-- The canonical completed source norm is the original compact-action norm on every raw tensor. -/
theorem norm_toCompactTensorCompletion (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    ‖toCompactTensorCompletion H A z‖ = ‖algebraicCompactTensorHom H A z‖ := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact ((compactTensorSeminorm H A).norm_toNonUnitalCompletion z).trans
    (compactTensorSeminorm_apply H A z)

/-- The original canonical raw-tensor images are dense in the constructed same-gauge completion. -/
theorem denseRange_toCompactTensorCompletion :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    DenseRange (toCompactTensorCompletion H A) := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  exact (compactTensorSeminorm H A).denseRange_toNonUnitalCompletion

/-- Extend the same original compact-action hom through its actually induced completion. -/
def compactTensorCompletionToCompacts :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    CompactTensorCompletion H A →⋆ₙₐ[ℂ] CompactAlgebra H A := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact (compactTensorSeminorm H A).fromNonUnitalCompletion (algebraicCompactTensorHom H A)
    (fun z => (compactTensorSeminorm_apply H A z).ge)

/-- Every original completed canonical image has its unchanged original compact-action value. -/
theorem compactTensorCompletionToCompacts_apply (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    compactTensorCompletionToCompacts H A (toCompactTensorCompletion H A z) =
      algebraicCompactTensorHom H A z := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact (compactTensorSeminorm H A).fromNonUnitalCompletion_apply (algebraicCompactTensorHom H A)
    (fun z => (compactTensorSeminorm_apply H A z).ge) z

/-- The existing extended star hom is continuous on this actual same-seminorm completion. -/
theorem continuous_compactTensorCompletionToCompacts :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    Continuous (compactTensorCompletionToCompacts H A) := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact (compactTensorSeminorm H A).continuous_fromNonUnitalCompletion
    (algebraicCompactTensorHom H A) (fun z => (compactTensorSeminorm_apply H A z).ge)

/-- The actually induced completed map is isometric in norm, derived from its dense raw images. -/
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

/-- The completion comparison embeds its actual same-gauge carrier isometrically into original compacts. -/
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
