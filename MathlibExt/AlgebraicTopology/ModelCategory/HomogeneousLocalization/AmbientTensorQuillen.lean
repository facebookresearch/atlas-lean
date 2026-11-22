/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.HomogeneousLocalization.AmbientTensorHom
public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer

/-!
# The actual ambient tensor-Hom Quillen adjunction for associative modules

The original monoid axiom, actual I/J and their free-family source smallness
construct the full ordinary module model for the original associative A.
The literal underlying internal Hom preserves its exact created fibrations
and trivial fibrations for cofibrant U.  This proves the actual ambient
adjunction Quillen without coefficient commutativity or cofibrancy.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w

open CategoryTheory Limits MorphismProperty MonoidalCategory
open CategoryTheory.HomogeneousLocalization
open CategoryTheory.SmallObject
open scoped CategoryTheory.MonObj

namespace HomotopicalAlgebra.HomogeneousAmbientTensorQuillen

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C] [MonoidAxiom.{w} C]
  [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C] [LocallySmall.{w} C]
  (A : Mon C) (U : C) [IsCofibrant U]
  (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
  (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
  (sI : UniformRelativeSourceSmallness.{w} (ModuleTransfer.leftGenerators A I))
  (sJ : UniformRelativeSourceSmallness.{w} (ModuleTransfer.leftGenerators A J))

/-- The actual associative module model is the original full source transfer. -/
def transfer :
    RightTransfer.FullModelTransfer (Mod.free A.X) (Mod.forget (D := C) A.X) I J sI sJ :=
  ModuleTransfer.fullLeftModuleModelTransfer A I J hI hJ sI sJ

/-- The original underlying Hom functor preserves all actual created module fibrations. -/
theorem preservesFibrations :
    letI := (transfer A I J hI hJ sI sJ).model
    PreservesFibrations (AmbientTensorHom.rightFunctor A.X U) := by
  let t := transfer A I J hI hJ sI sJ
  let _ := t.model
  intro M N f hf
  rw [t.fibrations_eq] at hf ⊢
  exact (ihomAdjunction_isQuillenAdjunction_of_isCofibrant U).preservesFibrations f.hom hf

/-- The same literal Hom map preserves every actual created trivial fibration. -/
theorem preservesTrivialFibrations :
    letI := (transfer A I J hI hJ sI sJ).model
    PreservesTrivialFibrations (AmbientTensorHom.rightFunctor A.X U) := by
  let t := transfer A I J hI hJ sI sJ
  let _ := t.model
  intro M N f hf
  rw [t.trivialFibrations_eq] at hf ⊢
  exact (ihomAdjunction_isQuillenAdjunction_of_isCofibrant U).preservesTrivialFibrations f.hom hf

/-- The literal ambient tensor/internal-Hom adjunction is Quillen in the original constructed model. -/
theorem isQuillenAdjunction :
    letI := (transfer A I J hI hJ sI sJ).model
    (AmbientTensorHom.adjunction A.X U).IsQuillenAdjunction := by
  let t := transfer A I J hI hJ sI sJ
  let _ := t.model
  exact Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations (adj := AmbientTensorHom.adjunction A.X U)
    (preservesFibrations A U I J hI hJ sI sJ) (preservesTrivialFibrations A U I J hI hJ sI sJ)

end HomotopicalAlgebra.HomogeneousAmbientTensorQuillen
