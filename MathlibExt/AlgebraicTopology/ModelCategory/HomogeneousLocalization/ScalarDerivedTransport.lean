/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.HomogeneousLocalization.ScalarTensorMate
import MathlibExt.AlgebraicTopology.ModelCategory.HomogeneousLocalization.AmbientTensorQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.ScalarChange
import MathlibExt.AlgebraicTopology.ModelCategory.DerivedFunctorCoherence

/-!
# The actual chosen derived scalar/ambient-tensor comparison

The original full transfers retain both actual module models, source ranks
and chosen Q/R factories. The original ambient Quillen and balanced scalar
adjunctions derive those same functors. The proved original scalar/tensor
mate and actual derived composition maps give the whole derived comparison.

The source entry point constructs both full transfers from the original
monoid axiom, I/J and free-family source smallness. No localized model,
relative derived tensor, external derived unit coherence or localization
equivalence is supplied as an input premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v uD vD wA wB

open CategoryTheory Limits MorphismProperty MonoidalCategory
open CategoryTheory.HomogeneousLocalization
open CategoryTheory.SmallObject
open scoped CategoryTheory.MonObj

namespace HomotopicalAlgebra.HomogeneousScalarDerivedTransport

section ChosenIso

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {L L' : C ⥤ D} {H H' : D ⥤ C}
  (a : L ⊣ H) (a' : L' ⊣ H') [a.IsQuillenAdjunction] [a'.IsQuillenAdjunction]
  (q : GeneratedFunctorialReplacements.Data (C := C)) (e : L ≅ L')

/-- The original natural isomorphism derives through the same complete source Q and weak projection. -/
def leftNatIso : DerivedFunctorCoherence.left a q ≅ DerivedFunctorCoherence.left a' q := by
  letI : Localization.Lifting (DerivedFunctorCoherence.projection C) (weakEquivalences C)
      (DerivedFunctorCoherence.leftRaw (L := L) q) (DerivedFunctorCoherence.left a q) :=
    ⟨eqToIso (DerivedFunctorCoherence.left_projection a q)⟩
  letI : Localization.Lifting (DerivedFunctorCoherence.projection C) (weakEquivalences C)
      (DerivedFunctorCoherence.leftRaw (L := L') q) (DerivedFunctorCoherence.left a' q) :=
    ⟨eqToIso (DerivedFunctorCoherence.left_projection a' q)⟩
  exact Localization.liftNatIso (DerivedFunctorCoherence.projection C) (weakEquivalences C) _ _ _ _
    (Functor.isoWhiskerLeft q.Q (Functor.isoWhiskerRight e (DerivedFunctorCoherence.projection D)))

/-- Every represented component is the original source-Q image of the original point-set isomorphism. -/
theorem leftNatIso_hom_app (X : C) :
    (leftNatIso a a' q e).hom.app ((DerivedFunctorCoherence.projection C).obj X) =
      (DerivedFunctorCoherence.projection D).map (e.hom.app (q.Q.obj X)) := by
  simp only [leftNatIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change eqToHom rfl ≫ (DerivedFunctorCoherence.projection D).map (e.hom.app (q.Q.obj X)) ≫
    eqToHom rfl = _
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end ChosenIso

section Transfers

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]
  {A B : C} [MonObj A] [MonObj B]
  {IA JA IB JB : MorphismProperty C}
  {sIA : UniformRelativeSourceSmallness.{wA} (IA.strictMap (Mod.free A))}
  {sJA : UniformRelativeSourceSmallness.{wA} (JA.strictMap (Mod.free A))}
  {sIB : UniformRelativeSourceSmallness.{wB} (IB.strictMap (Mod.free B))}
  {sJB : UniformRelativeSourceSmallness.{wB} (JB.strictMap (Mod.free B))}
  (tA : RightTransfer.FullModelTransfer (Mod.free A) (Mod.forget (D := C) A) IA JA sIA sJA)
  (tB : RightTransfer.FullModelTransfer (Mod.free B) (Mod.forget (D := C) B) IB JB sIB sJB)
  (U : C) [IsCofibrant U]

/-- The literal ambient adjunction is Quillen in each actual original full-transfer model. -/
theorem ambientIsQuillenOfTransfer :
    letI := tA.model
    (AmbientTensorHom.adjunction A U).IsQuillenAdjunction := by
  let _ := tA.model
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro M N f hf
    rw [tA.fibrations_eq] at hf ⊢
    exact (ihomAdjunction_isQuillenAdjunction_of_isCofibrant U).preservesFibrations f.hom hf
  · intro M N f hf
    rw [tA.trivialFibrations_eq] at hf ⊢
    exact (ihomAdjunction_isQuillenAdjunction_of_isCofibrant U).preservesTrivialFibrations f.hom hf

/-- The actual ambient derived tensor uses the same original module-transfer Q factory. -/
def ambientDerivedLeft :
    letI := tA.model
    (weakEquivalences (Mod C A)).Localization ⥤ (weakEquivalences (Mod C A)).Localization := by
  letI := tA.model
  letI := ambientIsQuillenOfTransfer tA U
  exact DerivedFunctorCoherence.left (AmbientTensorHom.adjunction A U)
    (ModuleTransfer.ScalarChange.replacementsOfTransfer tA)

variable (p : A ⟶ B) [IsMonHom p]

/-- The original balanced scalar adjunction derives with the same actual source transfer and Q. -/
def scalarDerivedLeft :
    letI := tA.model
    letI := tB.model
    (weakEquivalences (Mod C A)).Localization ⥤ (weakEquivalences (Mod C B)).Localization := by
  letI := tA.model
  letI := tB.model
  letI := tB.cocomplete
  exact (ModuleTransfer.ScalarChange.derivedAdjunctionOfTransfers tA tB p).leftDerived

/-- Both complete derived routes retain the original scalar/tensor mate and both actual transfer Q factories. -/
def tensorIsoOfTransfers :
    letI := tA.model
    letI := tB.model
    ambientDerivedLeft tA U ⋙ scalarDerivedLeft tA tB p ≅
      scalarDerivedLeft tA tB p ⋙ ambientDerivedLeft tB U := by
  letI := tA.model
  letI := tB.model
  letI := tB.cocomplete
  letI : HasColimitsOfSize.{0, 0} (Mod C B) := hasColimitsOfSizeShrink.{0, 0, wB, wB} (Mod C B)
  letI := ambientIsQuillenOfTransfer tA U
  letI := ambientIsQuillenOfTransfer tB U
  letI := ModuleTransfer.ScalarChange.isQuillenOfTransfers tA tB p
  let qA := ModuleTransfer.ScalarChange.replacementsOfTransfer tA
  let qB := ModuleTransfer.ScalarChange.replacementsOfTransfer tB
  exact DerivedFunctorCoherence.leftCompositionIso (AmbientTensorHom.adjunction A U)
      (CategoryTheory.Mod.ExtensionOfScalars.adjunction p) qA qA ≪≫
    leftNatIso
      ((AmbientTensorHom.adjunction A U).comp (CategoryTheory.Mod.ExtensionOfScalars.adjunction p))
      ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).comp (AmbientTensorHom.adjunction B U)) qA
      (ScalarActionTransport.inductionTensorIso p U) ≪≫
    (DerivedFunctorCoherence.leftCompositionIso (CategoryTheory.Mod.ExtensionOfScalars.adjunction p)
      (AmbientTensorHom.adjunction B U) qA qB).symm

end Transfers

section OriginalSource

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]
  [axA : MonoidAxiom.{wA} C] [axB : MonoidAxiom.{wB} C]
  [coA : HasColimitsOfSize.{wA, wA} C] [liA : HasLimitsOfSize.{wA, wA} C] [lsA : LocallySmall.{wA} C]
  [coB : HasColimitsOfSize.{wB, wB} C] [liB : HasLimitsOfSize.{wB, wB} C] [lsB : LocallySmall.{wB} C]
  (A B : Mon C) (U : C) [IsCofibrant U]
  (I J : MorphismProperty C) [smallIA : I.IsSmall.{wA}] [smallJA : J.IsSmall.{wA}]
  [smallIB : I.IsSmall.{wB}] [smallJB : J.IsSmall.{wB}]
  (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
  (sIA : UniformRelativeSourceSmallness.{wA} (ModuleTransfer.leftGenerators A I))
  (sJA : UniformRelativeSourceSmallness.{wA} (ModuleTransfer.leftGenerators A J))
  (sIB : UniformRelativeSourceSmallness.{wB} (ModuleTransfer.leftGenerators B I))
  (sJB : UniformRelativeSourceSmallness.{wB} (ModuleTransfer.leftGenerators B J))
  (p : A.X ⟶ B.X) [IsMonHom p]

/-- Original monoid-axiom and source-rank data construct the actual full derived scalar/tensor comparison. -/
def tensorIsoFromSource :
    let tA : RightTransfer.FullModelTransfer (Mod.free A.X) (Mod.forget A.X) I J sIA sJA := by
      letI := axA
      letI := coA
      letI := liA
      letI := lsA
      letI := smallIA
      letI := smallJA
      exact ModuleTransfer.fullLeftModuleModelTransfer A I J hI hJ sIA sJA
    let tB : RightTransfer.FullModelTransfer (Mod.free B.X) (Mod.forget B.X) I J sIB sJB := by
      letI := axB
      letI := coB
      letI := liB
      letI := lsB
      letI := smallIB
      letI := smallJB
      exact ModuleTransfer.fullLeftModuleModelTransfer B I J hI hJ sIB sJB
    letI := tA.model
    letI := tB.model
    ambientDerivedLeft tA U ⋙ scalarDerivedLeft tA tB p ≅
      scalarDerivedLeft tA tB p ⋙ ambientDerivedLeft tB U := by
  let tA : RightTransfer.FullModelTransfer (Mod.free A.X) (Mod.forget A.X) I J sIA sJA := by
    letI := axA
    letI := coA
    letI := liA
    letI := lsA
    letI := smallIA
    letI := smallJA
    exact ModuleTransfer.fullLeftModuleModelTransfer A I J hI hJ sIA sJA
  let tB : RightTransfer.FullModelTransfer (Mod.free B.X) (Mod.forget B.X) I J sIB sJB := by
    letI := axB
    letI := coB
    letI := liB
    letI := lsB
    letI := smallIB
    letI := smallJB
    exact ModuleTransfer.fullLeftModuleModelTransfer B I J hI hJ sIB sJB
  letI := tA.model
  letI := tB.model
  exact tensorIsoOfTransfers tA tB U p

end OriginalSource

end HomotopicalAlgebra.HomogeneousScalarDerivedTransport
