/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.BimoduleFreePushoutProduct
public import MathlibExt.CategoryTheory.Monoidal.Bimod.TensorHomLeftParametrized
public import MathlibExt.CategoryTheory.MorphismProperty.LeibnizLiftingClasses

/-!
# The full original bimodule pushout-product laws

Both constructed relative Hom orientations extend the actual three free-cell
laws over the entire original source lifting classes. Source `AB`, source
`BD` and target `AD` retain their independent original cardinals and ordinal
bottoms. No uniform smallness or generating-domain cofibrancy is used.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v wAB wBD wAD w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer.BimodulePushoutProduct

variable {C : Type u} [Category.{v} C] [ModelCategory C] [MonoidalCategory C]

/-- The actual original-rank bimodule generation identifies the entire free-I lifting class. -/
theorem cofibrations_eq_originalFreeI {A B : Mon C} {I J : MorphismProperty C}
    {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (t : RightTransfer.OriginalRankModelTransfer (Bimod.free A B) (Bimod.forget (B := B) A) I J κ) :
    letI : ModelCategory (Bimod A B) := t.model
    cofibrations (Bimod A B) = (I.strictMap (Bimod.free A B)).rlp.llp := by
  let : ModelCategory (Bimod A B) := t.model
  have h := t.generation.I_rlp
  rw [t.generation_I] at h
  have h' := congrArg MorphismProperty.llp h
  rw [trivialFibrations_llp] at h'
  exact h'.symm

variable [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  {A B D : Mon C} {I J : MorphismProperty C}
  {κAB : Cardinal.{wAB}} [Fact κAB.IsRegular] [OrderBot κAB.ord.ToType]
  {κBD : Cardinal.{wBD}} [Fact κBD.IsRegular] [OrderBot κBD.ord.ToType]
  {κAD : Cardinal.{wAD}} [Fact κAD.IsRegular] [OrderBot κAD.ord.ToType]
  (tAB : RightTransfer.OriginalRankModelTransfer (Bimod.free A B) (Bimod.forget (B := B) A) I J κAB)
  (tBD : RightTransfer.OriginalRankModelTransfer (Bimod.free B D) (Bimod.forget (B := D) B) I J κBD)
  (tAD : RightTransfer.OriginalRankModelTransfer (Bimod.free A D) (Bimod.forget (B := D) A) I J κAD)
  [IsCofibrant B.X]

local instance sourceABPullbacks : HasLimitsOfSize.{0, 0} (Bimod A B) := Bimod.hasLimits A B
local instance sourceBDPullbacks : HasLimitsOfSize.{0, 0} (Bimod B D) := Bimod.hasLimits B D
local instance targetADPushouts : HasColimitsOfSize.{0, 0} (Bimod A D) := Bimod.hasColimits A D

/-- The entire original AB/BD cofibration classes satisfy the actual AD tensor cofibration law. -/
theorem pushoutObjObj_cofibration (hI : I.rlp = trivialFibrations C)
    {M M' : Bimod A B} (f : M ⟶ M') {N N' : Bimod B D} (g : N ⟶ N')
    (S : (Bimod.tensorCurried A B D).PushoutObjObj f g) :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Bimod B D) := tBD.model
    letI : ModelCategory (Bimod A D) := tAD.model
    cofibrations (Bimod A B) f → cofibrations (Bimod B D) g →
      cofibrations (Bimod A D) S.ι := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Bimod B D) := tBD.model
  let : ModelCategory (Bimod A D) := tAD.model
  intro hf hg
  have hAB := cofibrations_eq_originalFreeI tAB
  have hBD := cofibrations_eq_originalFreeI tBD
  have hAD := cofibrations_eq_originalFreeI tAD
  rw [hAB] at hf
  rw [hBD] at hg
  rw [hAD]
  apply pushoutObjObj_mem_rlp_llp (Bimod.tensorCurried A B D)
    (Bimod.InternalHom.leftHomContravariant (A := A) (B := B) (D := D))
    (Bimod.InternalHom.homContravariant (A := A) (B := B) (D := D))
    Bimod.InternalHom.leftTensorHomParametrized Bimod.InternalHom.tensorHomParametrized
    (I.strictMap (Bimod.free A B)) (I.strictMap (Bimod.free B D)) (I.strictMap (Bimod.free A D))
    ?_ f g S hf hg
  intro X Y i hi U V j hj
  rw [← hAD]
  exact BimoduleFreePushoutProduct.originalFreeI_pushoutProduct tAD hI i hi j hj

/-- The entire original free-J AB class and free-I BD class satisfy the actual left trivial law. -/
theorem pushoutObjObj_trivial_left (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    {M M' : Bimod A B} (f : M ⟶ M') {N N' : Bimod B D} (g : N ⟶ N')
    (S : (Bimod.tensorCurried A B D).PushoutObjObj f g) :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Bimod B D) := tBD.model
    letI : ModelCategory (Bimod A D) := tAD.model
    trivialCofibrations (Bimod A B) f → cofibrations (Bimod B D) g →
      trivialCofibrations (Bimod A D) S.ι := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Bimod B D) := tBD.model
  let : ModelCategory (Bimod A D) := tAD.model
  intro hf hg
  have hBD := cofibrations_eq_originalFreeI tBD
  rw [tAB.trivialCofibrations_eq] at hf
  rw [hBD] at hg
  rw [tAD.trivialCofibrations_eq]
  apply pushoutObjObj_mem_rlp_llp (Bimod.tensorCurried A B D)
    (Bimod.InternalHom.leftHomContravariant (A := A) (B := B) (D := D))
    (Bimod.InternalHom.homContravariant (A := A) (B := B) (D := D))
    Bimod.InternalHom.leftTensorHomParametrized Bimod.InternalHom.tensorHomParametrized
    (J.strictMap (Bimod.free A B)) (I.strictMap (Bimod.free B D)) (J.strictMap (Bimod.free A D))
    ?_ f g S hf hg
  intro X Y i hi U V j hj
  rw [← tAD.trivialCofibrations_eq]
  exact BimoduleFreePushoutProduct.originalFreeJFreeI_pushoutProduct tAD hI hJ i hi j hj

/-- The entire original free-I AB class and free-J BD class satisfy the other actual trivial law. -/
theorem pushoutObjObj_trivial_right (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    {M M' : Bimod A B} (f : M ⟶ M') {N N' : Bimod B D} (g : N ⟶ N')
    (S : (Bimod.tensorCurried A B D).PushoutObjObj f g) :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Bimod B D) := tBD.model
    letI : ModelCategory (Bimod A D) := tAD.model
    cofibrations (Bimod A B) f → trivialCofibrations (Bimod B D) g →
      trivialCofibrations (Bimod A D) S.ι := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Bimod B D) := tBD.model
  let : ModelCategory (Bimod A D) := tAD.model
  intro hf hg
  have hAB := cofibrations_eq_originalFreeI tAB
  rw [hAB] at hf
  rw [tBD.trivialCofibrations_eq] at hg
  rw [tAD.trivialCofibrations_eq]
  apply pushoutObjObj_mem_rlp_llp (Bimod.tensorCurried A B D)
    (Bimod.InternalHom.leftHomContravariant (A := A) (B := B) (D := D))
    (Bimod.InternalHom.homContravariant (A := A) (B := B) (D := D))
    Bimod.InternalHom.leftTensorHomParametrized Bimod.InternalHom.tensorHomParametrized
    (I.strictMap (Bimod.free A B)) (J.strictMap (Bimod.free B D)) (J.strictMap (Bimod.free A D))
    ?_ f g S hf hg
  intro X Y i hi U V j hj
  rw [← tAD.trivialCofibrations_eq]
  exact BimoduleFreePushoutProduct.originalFreeIFreeJ_pushoutProduct tAD hI hJ i hi j hj

/-- The complete original chosen corner has the cofibration clause at all original endpoints. -/
theorem pushoutProduct_cofibration (hI : I.rlp = trivialFibrations C)
    {M M' : Bimod A B} (f : M ⟶ M') {N N' : Bimod B D} (g : N ⟶ N') :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Bimod B D) := tBD.model
    letI : ModelCategory (Bimod A D) := tAD.model
    cofibrations (Bimod A B) f → cofibrations (Bimod B D) g →
      cofibrations (Bimod A D) (((Bimod.tensorCurried A B D).leibnizPushout.obj (Arrow.mk f)).obj
        (Arrow.mk g)).hom :=
  pushoutObjObj_cofibration tAB tBD tAD hI f g (Functor.PushoutObjObj.ofHasPushout _ f g)

/-- The complete original chosen corner retains the entire left trivial-cofibration clause. -/
theorem pushoutProduct_trivial_left (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    {M M' : Bimod A B} (f : M ⟶ M') {N N' : Bimod B D} (g : N ⟶ N') :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Bimod B D) := tBD.model
    letI : ModelCategory (Bimod A D) := tAD.model
    trivialCofibrations (Bimod A B) f → cofibrations (Bimod B D) g →
      trivialCofibrations (Bimod A D) (((Bimod.tensorCurried A B D).leibnizPushout.obj (Arrow.mk f)).obj
        (Arrow.mk g)).hom :=
  pushoutObjObj_trivial_left tAB tBD tAD hI hJ f g (Functor.PushoutObjObj.ofHasPushout _ f g)

/-- The complete original chosen corner retains the entire right trivial-cofibration clause. -/
theorem pushoutProduct_trivial_right (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    {M M' : Bimod A B} (f : M ⟶ M') {N N' : Bimod B D} (g : N ⟶ N') :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Bimod B D) := tBD.model
    letI : ModelCategory (Bimod A D) := tAD.model
    cofibrations (Bimod A B) f → trivialCofibrations (Bimod B D) g →
      trivialCofibrations (Bimod A D) (((Bimod.tensorCurried A B D).leibnizPushout.obj (Arrow.mk f)).obj
        (Arrow.mk g)).hom :=
  pushoutObjObj_trivial_right tAB tBD tAD hI hJ f g (Functor.PushoutObjObj.ofHasPushout _ f g)

end HomotopicalAlgebra.ModuleTransfer.BimodulePushoutProduct
