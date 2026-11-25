/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.RightForgetCofibrations
public import MathlibExt.CategoryTheory.Monoidal.Mod.RightLeftTensorPullback
public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedAdjunctionCoherence
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

/-!
# Quillen laws for the actual noncommutative relative tensor

The fixed-coefficient adjunction is the existing balanced tensor-Hom
adjunction. For the full two-variable laws, forgetting the entire actual
Hom pullback identifies its Arrow with the base pullback-Hom. The original
parametrized lifting equivalence then proves the three pushout-product
laws. Original transferred right-I cells earn the necessary underlying
cofibration image; it is not supplied as a module outcome premise.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v wR wL

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty CategoryTheory.SmallObject HomotopicalAlgebra
open CategoryTheory.MonoidalOpposite
open scoped CategoryTheory.MonObj MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer.RightLeftTensorQuillen

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [ModelCategory C] [IsClosedSymmetricMonoidalModelCategory C]
  {A : C} [MonObj A] [HasColimitsOfSize.{0, 0} C]

open CategoryTheory.Mod.RightLeftTensor

section CreatedLeftModel

variable [ModelCategory (Mod C A)]

/-- The actual balanced tensor-Hom adjunction is Quillen for a cofibrant underlying right coefficient. -/
theorem tensorHom_isQuillen
    (hW : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    (N : RightModuleFree.Carrier A) [IsCofibrant N.X] :
    (tensorHomAdjunction N).IsQuillenAdjunction := by
  let : (ihom.adjunction N.X).IsQuillenAdjunction :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant N.X
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y f hf
    rw [hF]
    change fibrations C ((ihom N.X).map f)
    exact Adjunction.IsQuillenAdjunction.preservesFibrations (adj := ihom.adjunction N.X) f hf
  · intro X Y f hf
    change (fibrations (Mod C A) ⊓ weakEquivalences (Mod C A)) _
    rw [hF, hW]
    change trivialFibrations C ((ihom N.X).map f)
    exact Adjunction.IsQuillenAdjunction.preservesTrivialFibrations (adj := ihom.adjunction N.X) f hf

/-- The actual selected replacement factories derive this same tensor-Hom adjunction. -/
def chosenDerivedTensorHom
    (hW : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    (N : RightModuleFree.Carrier A) [IsCofibrant N.X]
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A))
    (rC : GeneratedFunctorialReplacements.Data (C := C)) :
    QuillenDerivedAdjunctionData (tensorHomAdjunction N) := by
  letI : (tensorHomAdjunction N).IsQuillenAdjunction := tensorHom_isQuillen hW hF N
  exact DerivedAdjunctionCoherence.chosenDerivedAdjunctionData (tensorHomAdjunction N) qA rC

omit [HasColimitsOfSize.{0, 0} C] in
private theorem basePullbackHom_trivialFibration {N N' X Y : C} (f : N ⟶ N') (p : X ⟶ Y)
    (hf : cofibrations C f) (hp : trivialFibrations C p) :
    trivialFibrations C (((Opposite.op (Arrow.mk f)) ⋔ Arrow.mk p).hom) := by
  have h : PushoutProductLe (cofibrations C) (cofibrations C) (trivialFibrations C).llp := by
    rw [trivialFibrations_llp]
    exact IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct
  simpa only [cofibrations_rlp] using
    (pushoutProduct_le_llp_iff_pullbackHom_le_rlp
      (cofibrations C) (cofibrations C) (trivialFibrations C)).mp h f p hf hp

omit [HasColimitsOfSize.{0, 0} C] in
private theorem basePullbackHom_fibration {N N' X Y : C} (f : N ⟶ N') (p : X ⟶ Y)
    (hf : cofibrations C f) (hp : fibrations C p) :
    fibrations C (((Opposite.op (Arrow.mk f)) ⋔ Arrow.mk p).hom) := by
  have h : PushoutProductLe (cofibrations C) (trivialCofibrations C) (fibrations C).llp := by
    rw [fibrations_llp]
    exact IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right
  simpa only [trivialCofibrations_rlp] using
    (pushoutProduct_le_llp_iff_pullbackHom_le_rlp
      (cofibrations C) (trivialCofibrations C) (fibrations C)).mp h f p hf hp

omit [HasColimitsOfSize.{0, 0} C] in
private theorem basePullbackHom_trivial_of_trivialCofibration
    {N N' X Y : C} (f : N ⟶ N') (p : X ⟶ Y)
    (hf : trivialCofibrations C f) (hp : fibrations C p) :
    trivialFibrations C (((Opposite.op (Arrow.mk f)) ⋔ Arrow.mk p).hom) := by
  have h : PushoutProductLe (trivialCofibrations C) (cofibrations C) (fibrations C).llp := by
    rw [fibrations_llp]
    exact IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
  simpa only [cofibrations_rlp] using
    (pushoutProduct_le_llp_iff_pullbackHom_le_rlp
      (trivialCofibrations C) (cofibrations C) (fibrations C)).mp h f p hf hp

omit [HasColimitsOfSize.{0, 0} C] in
/-- The whole actual module Hom pullback is a trivial fibration for a cofibration and trivial fibration. -/
theorem pullbackHom_trivialFibration
    (hW : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') {X Y : C} (p : X ⟶ Y)
    (R : (homContravariant (A := A)).PullbackObjObj f p)
    (hf : cofibrations C f.hom) (hp : trivialFibrations C p) :
    trivialFibrations (Mod C A) R.π := by
  change (fibrations (Mod C A) ⊓ weakEquivalences (Mod C A)) R.π
  rw [hF, hW]
  change trivialFibrations C R.π.hom
  exact ((trivialFibrations C).arrow_mk_iso_iff (forgetPullbackPacketIso f p R)).mpr
    (basePullbackHom_trivialFibration f.hom p hf hp)

omit [HasColimitsOfSize.{0, 0} C] in
/-- Created fibrations transport the complete actual pullback square. -/
theorem pullbackHom_fibration
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') {X Y : C} (p : X ⟶ Y)
    (R : (homContravariant (A := A)).PullbackObjObj f p)
    (hf : cofibrations C f.hom) (hp : fibrations C p) :
    fibrations (Mod C A) R.π := by
  rw [hF]
  change fibrations C R.π.hom
  exact ((fibrations C).arrow_mk_iso_iff (forgetPullbackPacketIso f p R)).mpr
    (basePullbackHom_fibration f.hom p hf hp)

omit [HasColimitsOfSize.{0, 0} C] in
/-- A trivial coefficient cofibration gives a trivial fibration of the actual module Hom pullback. -/
theorem pullbackHom_trivial_of_trivialCofibration
    (hW : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') {X Y : C} (p : X ⟶ Y)
    (R : (homContravariant (A := A)).PullbackObjObj f p)
    (hf : trivialCofibrations C f.hom) (hp : fibrations C p) :
    trivialFibrations (Mod C A) R.π := by
  change (fibrations (Mod C A) ⊓ weakEquivalences (Mod C A)) R.π
  rw [hF, hW]
  change trivialFibrations C R.π.hom
  exact ((trivialFibrations C).arrow_mk_iso_iff (forgetPullbackPacketIso f p R)).mpr
    (basePullbackHom_trivial_of_trivialCofibration f.hom p hf hp)

/-- The original relative pushout product is a cofibration by the actual parametrized lifting equivalence. -/
theorem relativePushoutProduct_cofibration
    (hW : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') {M M' : Mod C A} (g : M ⟶ M')
    (hf : cofibrations C f.hom) (hg : cofibrations (Mod C A) g) :
    cofibrations C (((relativePushoutProduct (A := A)).obj (Arrow.mk f)).obj (Arrow.mk g)).hom := by
  let R := Functor.PushoutObjObj.ofHasPushout (tensorCurried (A := A)) f g
  change cofibrations C R.ι
  rw [← trivialFibrations_llp]
  intro X Y p hp
  let S := Functor.PullbackObjObj.ofHasPullback (homContravariant (A := A)) f p
  apply (tensorHomParametrized.hasLiftingProperty_iff R S).mpr
  have hS := pullbackHom_trivialFibration hW hF f p S hf hp
  rw [← trivialFibrations_llp] at hg
  exact hg S.π hS

/-- A trivial left-module map gives a trivial relative pushout product, with arbitrary original endpoints. -/
theorem relativePushoutProduct_trivial_right
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') {M M' : Mod C A} (g : M ⟶ M')
    (hf : cofibrations C f.hom) (hg : trivialCofibrations (Mod C A) g) :
    trivialCofibrations C (((relativePushoutProduct (A := A)).obj (Arrow.mk f)).obj (Arrow.mk g)).hom := by
  let R := Functor.PushoutObjObj.ofHasPushout (tensorCurried (A := A)) f g
  change trivialCofibrations C R.ι
  rw [← fibrations_llp]
  intro X Y p hp
  let S := Functor.PullbackObjObj.ofHasPullback (homContravariant (A := A)) f p
  apply (tensorHomParametrized.hasLiftingProperty_iff R S).mpr
  have hS := pullbackHom_fibration hF f p S hf hp
  rw [← fibrations_llp] at hg
  exact hg S.π hS

/-- A trivial right coefficient cofibration gives the other trivial relative pushout-product law. -/
theorem relativePushoutProduct_trivial_left
    (hW : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') {M M' : Mod C A} (g : M ⟶ M')
    (hf : trivialCofibrations C f.hom) (hg : cofibrations (Mod C A) g) :
    trivialCofibrations C (((relativePushoutProduct (A := A)).obj (Arrow.mk f)).obj (Arrow.mk g)).hom := by
  let R := Functor.PushoutObjObj.ofHasPushout (tensorCurried (A := A)) f g
  change trivialCofibrations C R.ι
  rw [← fibrations_llp]
  intro X Y p hp
  let S := Functor.PullbackObjObj.ofHasPullback (homContravariant (A := A)) f p
  apply (tensorHomParametrized.hasLiftingProperty_iff R S).mpr
  have hS := pullbackHom_trivial_of_trivialCofibration hW hF f p S hf hp
  rw [← trivialFibrations_llp] at hg
  exact hg S.π hS

end CreatedLeftModel

section Transfers

variable [IsCofibrant A] [HasColimitsOfSize.{wR, wR} C]
  {IR JR IL JL : MorphismProperty C}
  {sIR : UniformRelativeSourceSmallness.{wR} (IR.strictMap (RightModuleFree.functor A))}
  {sJR : UniformRelativeSourceSmallness.{wR} (JR.strictMap (RightModuleFree.functor A))}
  {sIL : UniformRelativeSourceSmallness.{wL} (IL.strictMap (Mod.free A))}
  {sJL : UniformRelativeSourceSmallness.{wL} (JL.strictMap (Mod.free A))}
  (tR : RightTransfer.FullModelTransfer (RightModuleFree.functor A)
    (Mod.forget (D := C) (mop A)) IR JR sIR sJR)
  (tL : RightTransfer.FullModelTransfer (Mod.free A) (Mod.forget (D := C) A) IL JL sIL sJL)

/-- Both original full transfers earn the actual fixed-coefficient Quillen adjunction. -/
theorem tensorHom_isQuillen_of_transfers (hIR : IR.rlp = trivialFibrations C)
    (N : RightModuleFree.Carrier A) :
    letI : ModelCategory (RightModuleFree.Carrier A) := tR.model
    letI : ModelCategory (Mod C A) := tL.model
    IsCofibrant N → (tensorHomAdjunction N).IsQuillenAdjunction := by
  let : ModelCategory (RightModuleFree.Carrier A) := tR.model
  let : ModelCategory (Mod C A) := tL.model
  intro hN
  let : IsCofibrant N.X := RightForgetCofibrations.cofibrant_underlying_of_transfer tR hIR N hN
  exact tensorHom_isQuillen tL.weak_eq tL.fibrations_eq N

/-- The full generated module models satisfy the original relative cofibration pushout-product law. -/
theorem relativePushoutProduct_cofibration_of_transfers (hIR : IR.rlp = trivialFibrations C)
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') {M M' : Mod C A} (g : M ⟶ M') :
    letI : ModelCategory (RightModuleFree.Carrier A) := tR.model
    letI : ModelCategory (Mod C A) := tL.model
    cofibrations (RightModuleFree.Carrier A) f → cofibrations (Mod C A) g →
      cofibrations C (((relativePushoutProduct (A := A)).obj (Arrow.mk f)).obj (Arrow.mk g)).hom := by
  let : ModelCategory (RightModuleFree.Carrier A) := tR.model
  let : ModelCategory (Mod C A) := tL.model
  intro hf hg
  exact relativePushoutProduct_cofibration tL.weak_eq tL.fibrations_eq f g
    (RightForgetCofibrations.cofibrations_underlying_of_transfer tR hIR f hf) hg

/-- The same original module models satisfy the trivial law in the left-module variable. -/
theorem relativePushoutProduct_trivial_right_of_transfers (hIR : IR.rlp = trivialFibrations C)
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') {M M' : Mod C A} (g : M ⟶ M') :
    letI : ModelCategory (RightModuleFree.Carrier A) := tR.model
    letI : ModelCategory (Mod C A) := tL.model
    cofibrations (RightModuleFree.Carrier A) f → trivialCofibrations (Mod C A) g →
      trivialCofibrations C (((relativePushoutProduct (A := A)).obj (Arrow.mk f)).obj (Arrow.mk g)).hom := by
  let : ModelCategory (RightModuleFree.Carrier A) := tR.model
  let : ModelCategory (Mod C A) := tL.model
  intro hf hg
  exact relativePushoutProduct_trivial_right tL.fibrations_eq f g
    (RightForgetCofibrations.cofibrations_underlying_of_transfer tR hIR f hf) hg

/-- The same original module models satisfy the trivial law in the right-module variable. -/
theorem relativePushoutProduct_trivial_left_of_transfers (hIR : IR.rlp = trivialFibrations C)
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') {M M' : Mod C A} (g : M ⟶ M') :
    letI : ModelCategory (RightModuleFree.Carrier A) := tR.model
    letI : ModelCategory (Mod C A) := tL.model
    trivialCofibrations (RightModuleFree.Carrier A) f → cofibrations (Mod C A) g →
      trivialCofibrations C (((relativePushoutProduct (A := A)).obj (Arrow.mk f)).obj (Arrow.mk g)).hom := by
  let : ModelCategory (RightModuleFree.Carrier A) := tR.model
  let : ModelCategory (Mod C A) := tL.model
  intro hf hg
  exact relativePushoutProduct_trivial_left tL.weak_eq tL.fibrations_eq f g
    (RightForgetCofibrations.trivialCofibrations_underlying_of_transfer tR hIR f hf) hg

end Transfers
end HomotopicalAlgebra.ModuleTransfer.RightLeftTensorQuillen
