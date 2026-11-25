/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.AmbientPushoutProduct
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
public import MathlibExt.AlgebraicTopology.ModelCategory.WeakEquivalenceFunctor
public import MathlibExt.AlgebraicTopology.ModelCategory.InternalHomSourceWeakEquivalence
public import MathlibExt.CategoryTheory.Limits.Shapes.Pullback.LeibnizPushoutInitial

/-!
# Actual ambient tensor weak preservation on associative modules

The fixed-coefficient tensor/cotensor adjunction is the original one.
In the coefficient variable, the full ambient pushout-product law against
the initial module map gives trivial-cofibration preservation. Brown's
original factorization then gives weak preservation at cofibrant coefficient
objects. No missing adjunction, scalar cofibrancy or flatness result is used.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty HomotopicalAlgebra Opposite
open scoped CategoryTheory.MonObj MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer.AmbientBrown

variable {C : Type u} [Category.{v} C] [ModelCategory C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C]
  {A : C} [MonObj A] [ModelCategory (Mod C A)]

open CategoryTheory.HomogeneousLocalization.AmbientTensorHom
open CategoryTheory.HomogeneousLocalization

/-- The module forgetful functor creates the limits used by the cotensor weak-map proof. -/
local instance forgetCreatesLimits : CreatesLimitsOfSize.{0, 0} (Mod.forget (D := C) A) :=
  Mod.forgetCreatesLimits.{0} A

/-- The actual ambient coefficient functor is the flip of the existing tensor bifunctor. -/
def coefficientFunctor (M : Mod C A) : C ⥤ Mod C A := (leftBifunctor A).flip.obj M

/-- The actual ambient initial-module pushout product retains the original coefficient map. -/
def initialModulePushoutProductIso {U V : C} (f : U ⟶ V) (M : Mod C A) :
    ((ambientPushoutProduct A).obj (Arrow.mk f)).obj (Arrow.mk (initial.to M)) ≅
      Arrow.mk ((coefficientFunctor M).map f) := by
  simp only [ambientPushoutProduct, Functor.leibnizPushout_obj_obj, Arrow.mk_hom]
  let : PreservesColimitsOfSize.{0, 0} (Mod.AmbientTensor.functor A U) :=
    (adjunction A U).leftAdjoint_preservesColimits
  let : PreservesColimitsOfSize.{0, 0} (Mod.AmbientTensor.functor A V) :=
    (adjunction A V).leftAdjoint_preservesColimits
  let : PreservesColimitsOfShape (Discrete PEmpty.{1}) ((leftBifunctor A).obj U) := by
    change PreservesColimitsOfShape (Discrete PEmpty.{1}) (Mod.AmbientTensor.functor A U)
    infer_instance
  let : PreservesColimitsOfShape (Discrete PEmpty.{1}) ((leftBifunctor A).obj V) := by
    change PreservesColimitsOfShape (Discrete PEmpty.{1}) (Mod.AmbientTensor.functor A V)
    infer_instance
  exact (leftBifunctor A).leibnizPushoutIsInitialRightIso f initialIsInitial M

/-- The original coefficient functor preserves all trivial cofibrations for a cofibrant module. -/
theorem coefficient_trivialCofibrations
    (hW : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    (M : Mod C A) [IsCofibrant M] :
    trivialCofibrations C ≤ (trivialCofibrations (Mod C A)).inverseImage (coefficientFunctor M) := by
  intro U V f hf
  have h := AmbientPushoutProduct.trivial_coefficient hW hF f (initial.to M) hf
    (mem_cofibrations (initial.to M))
  exact ((trivialCofibrations (Mod C A)).arrow_mk_iso_iff (initialModulePushoutProductIso f M)).mp h

/-- Both original cofibrant coefficient endpoints retain weak maps under the actual ambient module action. -/
theorem coefficient_weak_of_cofibrant
    (hW : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    (M : Mod C A) [IsCofibrant M] {U V : C} (f : U ⟶ V) [IsCofibrant U] [IsCofibrant V]
    (hf : weakEquivalences C f) : weakEquivalences (Mod C A) ((coefficientFunctor M).map f) := by
  let : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  exact ((coefficientFunctor M).map_weakEquivalence_of_cofibrant
    (fun X Y i hi => (coefficient_trivialCofibrations hW hF M i hi).2) f).mem

/-- A cofibrant ambient coefficient gives the actual tensor/cotensor Quillen adjunction in created classes. -/
theorem fixedAdjunction_isQuillen
    (hW : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    (U : C) [IsCofibrant U] : (adjunction A U).IsQuillenAdjunction := by
  let : (ihom.adjunction U).IsQuillenAdjunction := ihomAdjunction_isQuillenAdjunction_of_isCofibrant U
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro M N p hp
    rw [hF] at hp ⊢
    change fibrations C ((ihom U).map p.hom)
    exact Adjunction.IsQuillenAdjunction.preservesFibrations (adj := ihom.adjunction U) p.hom hp
  · intro M N p hp
    change (fibrations (Mod C A) ⊓ weakEquivalences (Mod C A)) _
    change (fibrations (Mod C A) ⊓ weakEquivalences (Mod C A)) p at hp
    rw [hF, hW] at hp ⊢
    change trivialFibrations C ((ihom U).map p.hom)
    exact Adjunction.IsQuillenAdjunction.preservesTrivialFibrations (adj := ihom.adjunction U) p.hom hp

/-- The actual fixed-coefficient ambient tensor preserves weak maps of cofibrant modules. -/
theorem module_weak_of_cofibrant
    (hW : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    (U : C) [IsCofibrant U] {M N : Mod C A} (p : M ⟶ N) [IsCofibrant M] [IsCofibrant N]
    (hp : weakEquivalences (Mod C A) p) : weakEquivalences (Mod C A) ((Mod.AmbientTensor.functor A U).map p) := by
  let : (adjunction A U).IsQuillenAdjunction := fixedAdjunction_isQuillen hW hF U
  let : WeakEquivalence p := (weakEquivalence_iff _).mpr hp
  exact (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := adjunction A U) p).mem

/-- The original cotensor preserves weak maps on fibrant module targets. -/
theorem target_weak_of_fibrant
    (hW : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    (U : C) [IsCofibrant U] {M N : Mod C A} (p : M ⟶ N) [IsFibrant M] [IsFibrant N]
    (hp : weakEquivalences (Mod C A) p) : weakEquivalences (Mod C A) ((rightFunctor A U).map p) := by
  let : (adjunction A U).IsQuillenAdjunction := fixedAdjunction_isQuillen hW hF U
  let : WeakEquivalence p := (weakEquivalence_iff _).mpr hp
  exact (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adjunction A U) p).mem

/-- The original coefficient cotensor pre-map is weak into every original fibrant module target. -/
theorem preMap_weak_of_cofibrant
    (hW : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    {U V : C} (f : U ⟶ V) [IsCofibrant U] [IsCofibrant V] (M : Mod C A) [IsFibrant M]
    (hf : weakEquivalences C f) : weakEquivalences (Mod C A) (preMap A f M) := by
  let : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  have hM : fibrations C (Mod.forget (D := C) A |>.map (terminal.from M)) := by
    exact hF.le (terminal.from M) (mem_fibrations (terminal.from M))
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) (Mod.forget (D := C) A) := inferInstance
  let : Fibration ((Mod.forget (D := C) A).map (terminal.from M)) := (fibration_iff _).mpr hM
  let : IsFibrant M.X :=
    (isFibrant_iff_of_isTerminal ((Mod.forget (D := C) A).map (terminal.from M))
      (terminalIsTerminal.isTerminalObj (Mod.forget (D := C) A))).mpr inferInstance
  rw [hW]
  change weakEquivalences C ((MonoidalClosed.pre f).app M.X)
  exact (weakEquivalence_pre_app_of_cofibrant f (inferInstance : WeakEquivalence f)).mem

end HomotopicalAlgebra.ModuleTransfer.AmbientBrown
