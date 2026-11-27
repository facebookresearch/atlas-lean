/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Unitors

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonoidalClosed

set_option autoImplicit false

noncomputable section

universe uV vV uI vI

namespace MathlibExtTest.DayUnitorsTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I)

-- These index hom maps need neither a closed base nor any colimit.
example (i j : I) :
    EnrichedDayKernel.Unitors.leftUnitHom d i j =
      (λ_ (𝟙_ I ⟶[V] i)).inv ≫
        (eHomEquiv V (λ_ j).inv ⊗ₘ EnrichedDayKernel.Unitors.leftTensorHom d i j) ≫
        eComp V j (𝟙_ I ⊗ j) (i ⊗ j) :=
  EnrichedDayKernel.Unitors.leftUnitHom_eq d i j

example (i j : I) :
    EnrichedDayKernel.Unitors.rightUnitHom d i j =
      (λ_ (𝟙_ I ⟶[V] j)).inv ≫
        (eHomEquiv V (ρ_ i).inv ⊗ₘ EnrichedDayKernel.Unitors.rightTensorHom d i j) ≫
        eComp V i (i ⊗ 𝟙_ I) (i ⊗ j) :=
  EnrichedDayKernel.Unitors.rightUnitHom_eq d i j

example (j : I) :
    eId V (𝟙_ I) ≫ EnrichedDayKernel.Unitors.leftUnitHom d (𝟙_ I) j =
      eHomEquiv V (λ_ j).inv :=
  EnrichedDayKernel.Unitors.leftUnitHom_id d j

example (i : I) :
    eId V (𝟙_ I) ≫ EnrichedDayKernel.Unitors.rightUnitHom d i (𝟙_ I) =
      eHomEquiv V (ρ_ i).inv :=
  EnrichedDayKernel.Unitors.rightUnitHom_id d i

variable [MonoidalClosed V] (F : EnrichedFunctor V I V) (k : I)
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]

-- The inverse's actual data needs exactly this one kernel presentation.
example :
    EnrichedDayKernel.Unitors.leftInvComponent d F k =
      (λ_ (F.obj k)).inv ≫
        (eHomEquiv V (λ_ k).hom ⊗ₘ
          ((λ_ (F.obj k)).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 (F.obj k)))) ≫
        EnrichedDayKernel.gen d.tensorEnrichedFunctor
          (GradedYoneda.representable (𝟙_ I)) F k (𝟙_ I, k) := rfl

end MathlibExtTest.DayUnitorsTests

namespace MathlibExtTest.DayUnitorsFullTests

open CategoryTheory.EnrichedDayKernel

section FullHom

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F : EnrichedFunctor V I V)

attribute [local instance] Enriched.prodCategory

-- No colimit, separator or ordinary enrichment on the closed base is assumed.
example (X Y : I × I) :
    MonoidalClosed.uncurry
        (((GradedYoneda.representable (𝟙_ I)).externalTensor F).map X Y) ≫
        Unitors.leftStrengthComponent d F Y =
      (Unitors.leftStrengthComponent d F X ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((d.tensorEnrichedFunctor.comp V F).map X Y) :=
  Unitors.leftStrength_natural d F X Y

example (k : I) :
    EnrichedDayKernel.Balanced d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k (Unitors.leftForwardGen d F k) :=
  Unitors.leftForwardGen_balanced d F k

end FullHom

section ParticularKernel

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F : EnrichedFunctor V I V) (k : I)
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]

attribute [local instance] Enriched.prodCategory

-- This one particular presentation supplies the actual forward map and both inverse laws.
example (X : I × I) :
    EnrichedDayKernel.gen d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k X ≫ Unitors.leftComponent d F k =
      (α_ ((X.1 ⊗ X.2) ⟶[V] k) (𝟙_ I ⟶[V] X.1) (F.obj X.2)).inv ≫
        (((β_ ((X.1 ⊗ X.2) ⟶[V] k) (𝟙_ I ⟶[V] X.1)).hom ≫
          (Unitors.leftUnitHom d X.1 X.2 ⊗ₘ 𝟙 ((X.1 ⊗ X.2) ⟶[V] k)) ≫
          eComp V X.2 (X.1 ⊗ X.2) k) ⊗ₘ 𝟙 (F.obj X.2)) ≫
        (β_ (X.2 ⟶[V] k) (F.obj X.2)).hom ≫ MonoidalClosed.uncurry (F.map X.2 k) :=
  Unitors.gen_leftComponent d F k X

example :
    Unitors.leftComponent d F k ≫ Unitors.leftInvComponent d F k =
      𝟙 (EnrichedDayKernel.obj d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k) :=
  Unitors.leftComponent_hom_inv_id d F k

example : Unitors.leftInvComponent d F k ≫ Unitors.leftComponent d F k = 𝟙 (F.obj k) :=
  Unitors.leftComponent_inv_hom_id d F k

example :
    (Unitors.leftComponentIso d F k).inv = (λ_ (F.obj k)).inv ≫
      (eHomEquiv V (λ_ k).hom ⊗ₘ
        ((λ_ (F.obj k)).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 (F.obj k)))) ≫
      EnrichedDayKernel.gen d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k (𝟙_ I, k) := rfl

example (k' : I)
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k')]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k')
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k')] :
    MonoidalClosed.uncurry (Output.map d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k k') ≫ Unitors.leftComponent d F k' =
      (Unitors.leftComponent d F k ⊗ₘ 𝟙 (k ⟶[V] k')) ≫
        MonoidalClosed.uncurry (F.map k k') :=
  Unitors.leftComponent_natural d F k k'

example {G : EnrichedFunctor V I V}
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G)
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) G k)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) G k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) G k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) G k)] :
    Input.mapAt d.tensorEnrichedFunctor
        (GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I))) a k ≫
        Unitors.leftComponent d G k =
      Unitors.leftComponent d F k ≫ (eHomEquiv V).symm (a.app k) :=
  Unitors.leftComponent_input_natural d a k

end ParticularKernel

section FixedInputFamily

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F : EnrichedFunctor V I V)
  [∀ k, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)]
  [∀ k, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)]
  [∀ k, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]

-- Only the unit/F kernels enter the genuine isomorphism; arbitrary other inputs need no coends.
example :
    (⟨Output.functor d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F⟩ : EnrichedFunctorCat V I) ≅ ⟨F⟩ :=
  Unitors.leftUnitor d F

example (k : I) :
    (eHomEquiv V).symm ((Unitors.leftUnitor d F).hom.app k) = Unitors.leftComponent d F k :=
  Unitors.leftUnitorHom_component d F k

end FixedInputFamily

section FixedUnitEndofunctor

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I)
  [∀ (F : EnrichedFunctor V I V) k,
    HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]
  [∀ (F : EnrichedFunctor V I V) k,
    HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]
  [∀ (F : EnrichedFunctor V I V) k,
    HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k)]

-- This natural isomorphism needs only kernels with the fixed representable unit input.
example : Unitors.leftUnitEndofunctor d ≅ 𝟭 (EnrichedFunctorCat V I) :=
  Unitors.leftUnitorNatIso d

example {F G : EnrichedFunctorCat V I} (a : F ⟶ G) :
    (Unitors.leftUnitEndofunctor d).map a ≫ (Unitors.leftUnitorNatIso d).hom.app G =
      (Unitors.leftUnitorNatIso d).hom.app F ≫ a :=
  (Unitors.leftUnitorNatIso d).hom.naturality a

end FixedUnitEndofunctor

end MathlibExtTest.DayUnitorsFullTests

namespace MathlibExtTest.DayRightUnitorsTests

open CategoryTheory.EnrichedDayKernel

section FixedKernel

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F : EnrichedFunctor V I V)

attribute [local instance] Enriched.prodCategory

-- The whole right strength needs no colimit or separator.
example (X Y : I × I) :
    MonoidalClosed.uncurry
        ((F.externalTensor (GradedYoneda.representable (𝟙_ I))).map X Y) ≫
        Unitors.rightStrengthComponent d F Y =
      (Unitors.rightStrengthComponent d F X ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((d.tensorEnrichedFunctor.comp V F).map X Y) :=
  Unitors.rightStrength_natural d F X Y

variable (k : I)
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k)]

-- The forward characteristic is the original expanded generator formula.
example (X : I × I) :
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F
        (GradedYoneda.representable (𝟙_ I)) k X ≫ Unitors.rightComponent d F k =
      (β_ ((X.1 ⊗ X.2) ⟶[V] k) (F.obj X.1 ⊗ (𝟙_ I ⟶[V] X.2))).hom ≫
        (α_ (F.obj X.1) (𝟙_ I ⟶[V] X.2) ((X.1 ⊗ X.2) ⟶[V] k)).hom ≫
        F.obj X.1 ◁ ((Unitors.rightUnitHom d X.1 X.2 ⊗ₘ
          𝟙 ((X.1 ⊗ X.2) ⟶[V] k)) ≫ eComp V X.1 (X.1 ⊗ X.2) k) ≫
        MonoidalClosed.uncurry (F.map X.1 k) :=
  Unitors.gen_rightComponent d F k X

example :
    Unitors.rightComponent d F k ≫ Unitors.rightInvComponent d F k =
      𝟙 (EnrichedDayKernel.obj d.tensorEnrichedFunctor F
        (GradedYoneda.representable (𝟙_ I)) k) :=
  Unitors.rightComponent_hom_inv_id d F k

example : Unitors.rightInvComponent d F k ≫ Unitors.rightComponent d F k = 𝟙 (F.obj k) :=
  Unitors.rightComponent_inv_hom_id d F k

example : (Unitors.rightComponentIso d F k).inv = (λ_ (F.obj k)).inv ≫
    (eHomEquiv V (ρ_ k).hom ⊗ₘ
      ((ρ_ (F.obj k)).inv ≫ (𝟙 (F.obj k) ⊗ₘ eId V (𝟙_ I)))) ≫
      EnrichedDayKernel.gen d.tensorEnrichedFunctor F
        (GradedYoneda.representable (𝟙_ I)) k (k, 𝟙_ I) := rfl

example (k' : I)
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k')]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k')
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F
        (GradedYoneda.representable (𝟙_ I)) k')] :
    MonoidalClosed.uncurry (Output.map d.tensorEnrichedFunctor F
        (GradedYoneda.representable (𝟙_ I)) k k') ≫ Unitors.rightComponent d F k' =
      (Unitors.rightComponent d F k ⊗ₘ 𝟙 (k ⟶[V] k')) ≫ MonoidalClosed.uncurry (F.map k k') :=
  Unitors.rightComponent_natural d F k k'

-- Exactly the two F/G unit-second kernels suffice for genuine input naturality.
example {G : EnrichedFunctor V I V}
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G)
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor G
      (GradedYoneda.representable (𝟙_ I)) k)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor G
      (GradedYoneda.representable (𝟙_ I)) k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor G
      (GradedYoneda.representable (𝟙_ I)) k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor G
        (GradedYoneda.representable (𝟙_ I)) k)] :
    Input.mapAt d.tensorEnrichedFunctor a
        (GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I))) k ≫
        Unitors.rightComponent d G k =
      Unitors.rightComponent d F k ≫ (eHomEquiv V).symm (a.app k) :=
  Unitors.rightComponent_input_natural d a k

end FixedKernel

section FixedSecondUnit

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I)
  [∀ (F : EnrichedFunctor V I V) k,
    HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k)]
  [∀ (F : EnrichedFunctor V I V) k,
    HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k)]
  [∀ (F : EnrichedFunctor V I V) k,
    HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F
        (GradedYoneda.representable (𝟙_ I)) k)]

-- No other second-input coend family is supplied to this natural isomorphism.
example : Unitors.rightUnitEndofunctor d ≅ 𝟭 (EnrichedFunctorCat V I) :=
  Unitors.rightUnitorNatIso d

example {F G : EnrichedFunctorCat V I} (a : F ⟶ G) :
    (Unitors.rightUnitEndofunctor d).map a ≫ (Unitors.rightUnitorNatIso d).hom.app G =
      (Unitors.rightUnitorNatIso d).hom.app F ≫ a :=
  (Unitors.rightUnitorNatIso d).hom.naturality a

end FixedSecondUnit

end MathlibExtTest.DayRightUnitorsTests
