/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.RightLeftTensorQuillen
public import MathlibExt.AlgebraicTopology.ModelCategory.InternalHomSourceWeakEquivalence
public import MathlibExt.AlgebraicTopology.ModelCategory.WeakEquivalenceFunctor
public import MathlibExt.CategoryTheory.Limits.Shapes.Pullback.LeibnizPushoutInitial

/-!
# Weak invariance in both actual relative tensor variables

The right-variable theorem uses the original relative pushout product
against the initial map of a cofibrant left module. The whole pushout
comparison gives preservation of trivial cofibrations, and Brown's original
factorization proves weak preservation between cofibrant right modules.
No missing right adjunction or relative-flatness outcome is an input.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v wR wL uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty CategoryTheory.SmallObject HomotopicalAlgebra
open CategoryTheory.MonoidalOpposite
open scoped CategoryTheory.MonObj MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer.RightLeftTensorBrown

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [ModelCategory C] [IsClosedSymmetricMonoidalModelCategory C]
  {A : C} [MonObj A] [HasColimitsOfSize.{0, 0} C]

open CategoryTheory.Mod.RightLeftTensor

section InitialComparison

variable [ModelCategory (Mod C A)]

/-- The actual initial-map relative pushout product is the unchanged right tensor map. -/
def rightTensorInitialPushoutProductIso {N N' : RightModuleFree.Carrier A} (f : N ⟶ N')
    (M : Mod C A) :
    ((relativePushoutProduct (A := A)).obj (Arrow.mk f)).obj (Arrow.mk (initial.to M)) ≅
      Arrow.mk ((rightTensorFunctor M).map f) := by
  simp only [relativePushoutProduct, Functor.leibnizPushout_obj_obj, Arrow.mk_hom]
  let : PreservesColimitsOfSize.{0, 0} (leftTensorFunctor N) :=
    (tensorHomAdjunction N).leftAdjoint_preservesColimits
  let : PreservesColimitsOfSize.{0, 0} (leftTensorFunctor N') :=
    (tensorHomAdjunction N').leftAdjoint_preservesColimits
  let : PreservesColimitsOfShape (Discrete PEmpty.{1}) ((tensorCurried (A := A)).obj N) :=
    by change PreservesColimitsOfShape (Discrete PEmpty.{1}) (leftTensorFunctor N); infer_instance
  let : PreservesColimitsOfShape (Discrete PEmpty.{1}) ((tensorCurried (A := A)).obj N') :=
    by change PreservesColimitsOfShape (Discrete PEmpty.{1}) (leftTensorFunctor N'); infer_instance
  exact (tensorCurried (A := A)).leibnizPushoutIsInitialRightIso f initialIsInitial M

end InitialComparison

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

/-- A cofibrant left module earns the full right-tensor trivial-cofibration image. -/
theorem rightTensor_trivialCofibrations (hIR : IR.rlp = trivialFibrations C) (M : Mod C A) :
    letI : ModelCategory (RightModuleFree.Carrier A) := tR.model
    letI : ModelCategory (Mod C A) := tL.model
    IsCofibrant M → trivialCofibrations (RightModuleFree.Carrier A) ≤
      (trivialCofibrations C).inverseImage (rightTensorFunctor M) := by
  let : ModelCategory (RightModuleFree.Carrier A) := tR.model
  let : ModelCategory (Mod C A) := tL.model
  intro hM
  let : IsCofibrant M := hM
  intro N N' f hf
  have h := RightLeftTensorQuillen.relativePushoutProduct_trivial_left_of_transfers tR tL hIR f
    (initial.to M) hf (mem_cofibrations (initial.to M))
  exact ((trivialCofibrations C).arrow_mk_iso_iff (rightTensorInitialPushoutProductIso f M)).mp h

/-- Brown's actual factorization gives right-tensor weak invariance at the original cofibrant endpoints. -/
theorem rightTensor_weak_of_cofibrant (hIR : IR.rlp = trivialFibrations C) (M : Mod C A)
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') :
    letI : ModelCategory (RightModuleFree.Carrier A) := tR.model
    letI : ModelCategory (Mod C A) := tL.model
    IsCofibrant M → IsCofibrant N → IsCofibrant N' →
      weakEquivalences (RightModuleFree.Carrier A) f → weakEquivalences C ((rightTensorFunctor M).map f) := by
  let : ModelCategory (RightModuleFree.Carrier A) := tR.model
  let : ModelCategory (Mod C A) := tL.model
  intro hM hN hN' hf
  let : IsCofibrant N := hN
  let : IsCofibrant N' := hN'
  let : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  exact ((rightTensorFunctor M).map_weakEquivalence_of_cofibrant
    (fun X Y i hi => (rightTensor_trivialCofibrations tR tL hIR M hM i hi).2) f).mem

/-- The actual fixed-right Quillen adjunction gives weak invariance in the left-module variable. -/
theorem leftTensor_weak_of_cofibrant (hIR : IR.rlp = trivialFibrations C) (N : RightModuleFree.Carrier A)
    {M M' : Mod C A} (g : M ⟶ M') :
    letI : ModelCategory (RightModuleFree.Carrier A) := tR.model
    letI : ModelCategory (Mod C A) := tL.model
    IsCofibrant N → IsCofibrant M → IsCofibrant M' →
      weakEquivalences (Mod C A) g → weakEquivalences C ((leftTensorFunctor N).map g) := by
  let : ModelCategory (RightModuleFree.Carrier A) := tR.model
  let : ModelCategory (Mod C A) := tL.model
  intro hN hM hM' hg
  let : IsCofibrant M := hM
  let : IsCofibrant M' := hM'
  let : WeakEquivalence g := (weakEquivalence_iff _).mpr hg
  let : (tensorHomAdjunction N).IsQuillenAdjunction :=
    RightLeftTensorQuillen.tensorHom_isQuillen_of_transfers tR tL hIR N hN
  exact (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
    (adj := tensorHomAdjunction N) g).mem

/-- The same actual adjunction gives weak invariance of Hom on fibrant target objects. -/
theorem homFunctor_weak_of_fibrant (hIR : IR.rlp = trivialFibrations C) (N : RightModuleFree.Carrier A)
    {X Y : C} (f : X ⟶ Y) :
    letI : ModelCategory (RightModuleFree.Carrier A) := tR.model
    letI : ModelCategory (Mod C A) := tL.model
    IsCofibrant N → IsFibrant X → IsFibrant Y →
      weakEquivalences C f → weakEquivalences (Mod C A) ((homFunctor N).map f) := by
  let : ModelCategory (RightModuleFree.Carrier A) := tR.model
  let : ModelCategory (Mod C A) := tL.model
  intro hN hX hY hf
  let : IsFibrant X := hX
  let : IsFibrant Y := hY
  let : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  let : (tensorHomAdjunction N).IsQuillenAdjunction :=
    RightLeftTensorQuillen.tensorHom_isQuillen_of_transfers tR tL hIR N hN
  exact (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
    (adj := tensorHomAdjunction N) f).mem

/-- The original coefficient pre-map is weak between cofibrant right sources into a fibrant target. -/
theorem homPre_weak_of_cofibrant (hIR : IR.rlp = trivialFibrations C)
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') (X : C) :
    letI : ModelCategory (RightModuleFree.Carrier A) := tR.model
    letI : ModelCategory (Mod C A) := tL.model
    IsCofibrant N → IsCofibrant N' → IsFibrant X →
      weakEquivalences (RightModuleFree.Carrier A) f → weakEquivalences (Mod C A) (homPre f X) := by
  let : ModelCategory (RightModuleFree.Carrier A) := tR.model
  let : ModelCategory (Mod C A) := tL.model
  intro hN hN' hX hf
  let : IsCofibrant N.X := RightForgetCofibrations.cofibrant_underlying_of_transfer tR hIR N hN
  let : IsCofibrant N'.X := RightForgetCofibrations.cofibrant_underlying_of_transfer tR hIR N' hN'
  let : IsFibrant X := hX
  let : WeakEquivalence f.hom := (weakEquivalence_iff _).mpr (tR.weak_eq.le f hf)
  rw [tL.weak_eq]
  change weakEquivalences C ((MonoidalClosed.pre f.hom).app X)
  exact (weakEquivalence_pre_app_of_cofibrant f.hom (inferInstance : WeakEquivalence f.hom)).mem

end Transfers
end HomotopicalAlgebra.ModuleTransfer.RightLeftTensorBrown
