/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Sequence.Day
public import MathlibExt.CategoryTheory.Monoidal.TensorPowers
public import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# The ordered tensor-power sequence monoid

This file packages the finite tensor powers of an object as a sequence under
Day convolution.  Its multiplication is ordered and generally
noncommutative.  The explicit monoid value is not registered as an instance.
-/

set_option autoImplicit false

noncomputable section

universe vV uV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct
open scoped ExternalProduct MonoidalCategory

namespace CategoryTheory.Sequence

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

@[expose] public section

/-- The sequence whose degree `n` is the `n`th tensor power of `K`. -/
noncomputable def tensorPowerSequence (K : V) : Sequence V :=
  DayFunctor.mk <| Discrete.functor fun n : Multiplicative ℕ =>
    TensorPower.tensorPowObj K n.toAdd

@[simp]
theorem tensorPowerSequence_obj (K : V) (n : ℕ) :
    (tensorPowerSequence K).functor.obj (index n) =
      TensorPower.tensorPowObj K n :=
  rfl

end

variable
  [∀ (F G : Index ⥤ V),
    (tensor Index).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ Index)).HasPointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (W : V) (d : Index),
    PreservesColimitsOfShape
      (CostructuredArrow (tensor Index) d) (tensorLeft W)]
  [∀ (W : V) (d : Index),
    PreservesColimitsOfShape
      (CostructuredArrow (tensor Index) d) (tensorRight W)]
  [∀ (W : V) (d : Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        (Functor.fromPUnit.{0} (𝟙_ Index)) d) (tensorLeft W)]
  [∀ (W : V) (d : Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        (Functor.fromPUnit.{0} (𝟙_ Index)) d) (tensorRight W)]
  [∀ (W : V) (d : Index × Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        ((𝟭 Index).prod
          (Functor.fromPUnit.{0} (𝟙_ Index))) d)
      (tensorRight W)]
  [∀ (W : V) (d : Index × Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        ((tensor Index).prod (𝟭 Index)) d)
      (tensorRight W)]

noncomputable def tensorPowerSequenceMulDesc (K : V) :
    (tensorPowerSequence K).functor ⊠
        (tensorPowerSequence K).functor ⟶
      tensor Index ⋙ (tensorPowerSequence K).functor where
  app i := TensorPower.laxTensorPowerPairing (𝟭 V) K
    (degree i.1) (degree i.2)
  naturality := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ f
    have h : (i, j) = (i', j') := Prod.ext
      (Discrete.ext (Discrete.eq_of_hom f.1))
      (Discrete.ext (Discrete.eq_of_hom f.2))
    cases h
    rw [show f = 𝟙 _ by ext <;> apply Discrete.hom_eq]
    simp only [Functor.map_id]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

noncomputable def tensorPowerSequenceOne (K : V) :
    𝟙_ (Sequence V) ⟶ tensorPowerSequence K :=
  DayFunctor.unitDesc (TensorPower.laxTensorPowerUnit (𝟭 V) K)

noncomputable def tensorPowerSequenceMul (K : V) :
    tensorPowerSequence K ⊗ tensorPowerSequence K ⟶
      tensorPowerSequence K :=
  DayFunctor.tensorDesc (tensorPowerSequenceMulDesc K)

private theorem tensorPowerSequenceMul_fac
    (K : V) (x y : Index) :
    (DayFunctor.η (tensorPowerSequence K)
        (tensorPowerSequence K)).app (x, y) ≫
      (tensorPowerSequenceMul K).natTrans.app (x ⊗ y) =
        (tensorPowerSequenceMulDesc K).app (x, y) := by
  unfold tensorPowerSequenceMul
  exact DayFunctor.η_comp_tensorDesc_app
    (tensorPowerSequenceMulDesc K) x y

private theorem tensorPowerSequenceMul_fac_tensorObj
    (K : V) (x y : Index) :
    (DayFunctor.η (tensorPowerSequence K)
        (tensorPowerSequence K)).app (x, y) ≫
      (tensorPowerSequenceMul K).natTrans.app
        ((tensor Index).obj (x, y)) =
        (tensorPowerSequenceMulDesc K).app (x, y) := by
  exact tensorPowerSequenceMul_fac K x y

public section

/-- The explicit ordered tensor-power monoid under Day convolution. -/
@[instance_reducible]
noncomputable def tensorPowerSequenceMonObj (K : V) :
    MonObj (tensorPowerSequence K) where
  one := tensorPowerSequenceOne K
  mul := tensorPowerSequenceMul K
  one_mul := by
    apply DayFunctor.hom_ext
    apply Functor.hom_ext_of_isLeftKanExtension
      (F' := (𝟙_ (Sequence V) ⊗ tensorPowerSequence K).functor)
      (α := DayFunctor.η (𝟙_ (Sequence V))
        (tensorPowerSequence K))
    let _ : ((𝟙_ (Sequence V)).functor ⊠
          (tensorPowerSequence K).functor).IsLeftKanExtension
        (ExternalProduct.extensionUnitLeft
          (𝟙_ (Sequence V)).functor
          (DayFunctor.νNatTrans Index V)
          (tensorPowerSequence K).functor) :=
      ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitLeft
        (𝟙_ (Sequence V)).functor
        (DayFunctor.νNatTrans Index V)
        (tensorPowerSequence K).functor
        (isPointwiseLeftKanExtensionUnitUnit
          Index V (Sequence V)) |>.isLeftKanExtension
    apply Functor.hom_ext_of_isLeftKanExtension
      (F' := (𝟙_ (Sequence V)).functor ⊠
        (tensorPowerSequence K).functor)
      (α := ExternalProduct.extensionUnitLeft
        (𝟙_ (Sequence V)).functor
        (DayFunctor.νNatTrans Index V)
        (tensorPowerSequence K).functor)
    ext ⟨u, y⟩
    rcases u with ⟨u⟩
    rcases u with ⟨⟩
    dsimp [ExternalProduct.extensionUnitLeft, DayFunctor.νNatTrans]
    simp only [MonoidalCategory.whiskerLeft_id, Category.comp_id]
    have hwhisker :
        (DayFunctor.η (𝟙_ (Sequence V))
              (tensorPowerSequence K)).app (index 0, y) ≫
          (tensorPowerSequenceOne K ▷
              tensorPowerSequence K).natTrans.app
            (index 0 ⊗ y) =
        (tensorPowerSequenceOne K).natTrans.app (index 0) ▷
              (tensorPowerSequence K).functor.obj y ≫
          (DayFunctor.η (tensorPowerSequence K)
              (tensorPowerSequence K)).app (index 0, y) := by
      exact convolutionExtensionUnit_comp_ι_map_whiskerRight_app
        Index V (tensorPowerSequenceOne K)
        (tensorPowerSequence K) (index 0) y
    slice_lhs 2 3 =>
      rw [hwhisker]
    simp only [Category.assoc, tensorPowerSequenceMul_fac]
    have hcomp :
        (DayFunctor.ν Index V ▷
              (tensorPowerSequence K).functor.obj y) ≫
            ((tensorPowerSequenceOne K).natTrans.app (index 0) ▷
              (tensorPowerSequence K).functor.obj y) =
          (DayFunctor.ν Index V ≫
              (tensorPowerSequenceOne K).natTrans.app (index 0)) ▷
            (tensorPowerSequence K).functor.obj y :=
      (MonoidalCategory.comp_whiskerRight _ _ _).symm
    have hOneDesc :
        DayFunctor.ν Index V ≫
            (tensorPowerSequenceOne K).natTrans.app (index 0) =
          TensorPower.laxTensorPowerUnit (𝟭 V) K := by
      unfold tensorPowerSequenceOne
      exact DayFunctor.ν_comp_unitDesc _
    have hfacWhisker := hcomp.trans (congrArg
      (fun f => f ▷ (tensorPowerSequence K).functor.obj y)
      hOneDesc)
    slice_lhs 1 2 =>
      exact hfacWhisker
    have hleft :
        DayFunctor.ν Index V ▷
              (tensorPowerSequence K).functor.obj y ≫
            (DayFunctor.η (𝟙_ (Sequence V))
              (tensorPowerSequence K)).app (index 0, y) ≫
            (λ_ (tensorPowerSequence K)).hom.natTrans.app
                (index 0 ⊗ y) =
          (λ_ ((tensorPowerSequence K).functor.obj y)).hom ≫
            (tensorPowerSequence K).functor.map (λ_ y).inv := by
      exact leftUnitor_hom_unit_app
        V (tensorPowerSequence K) y
    slice_rhs 1 3 =>
      exact hleft
    rcases y with ⟨n⟩
    change
      (TensorPower.laxTensorPowerUnit (Functor.id V) K ▷
          TensorPower.tensorPowObj K n.toAdd) ≫
          TensorPower.laxTensorPowerPairing
            (Functor.id V) K 0 n.toAdd =
        (λ_ (TensorPower.tensorPowObj K n.toAdd)).hom ≫
          eqToHom (congrArg
            (fun m ↦ TensorPower.tensorPowObj K m)
            (Nat.zero_add n.toAdd).symm)
    exact TensorPower.laxTensorPowerPairing_zero_left
      (Functor.id V) K n.toAdd
  mul_one := by
    apply DayFunctor.hom_ext
    apply Functor.hom_ext_of_isLeftKanExtension
      (F' := (tensorPowerSequence K ⊗ 𝟙_ (Sequence V)).functor)
      (α := DayFunctor.η (tensorPowerSequence K)
        (𝟙_ (Sequence V)))
    let _ : ((tensorPowerSequence K).functor ⊠
          (𝟙_ (Sequence V)).functor).IsLeftKanExtension
        (ExternalProduct.extensionUnitRight
          (𝟙_ (Sequence V)).functor
          (DayFunctor.νNatTrans Index V)
          (tensorPowerSequence K).functor) :=
      ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitRight
        (𝟙_ (Sequence V)).functor
        (DayFunctor.νNatTrans Index V)
        (tensorPowerSequence K).functor
        (isPointwiseLeftKanExtensionUnitUnit
          Index V (Sequence V)) |>.isLeftKanExtension
    apply Functor.hom_ext_of_isLeftKanExtension
      (F' := (tensorPowerSequence K).functor ⊠
        (𝟙_ (Sequence V)).functor)
      (α := ExternalProduct.extensionUnitRight
        (𝟙_ (Sequence V)).functor
        (DayFunctor.νNatTrans Index V)
        (tensorPowerSequence K).functor)
    ext ⟨x, u⟩
    rcases u with ⟨u⟩
    rcases u with ⟨⟩
    dsimp [ExternalProduct.extensionUnitRight, DayFunctor.νNatTrans]
    simp only [MonoidalCategory.whiskerRight_id, Iso.hom_inv_id,
      Category.id_comp]
    have hwhisker :
        (DayFunctor.η (tensorPowerSequence K)
              (𝟙_ (Sequence V))).app (x, index 0) ≫
          (tensorPowerSequence K ◁
              tensorPowerSequenceOne K).natTrans.app
            (x ⊗ index 0) =
        (tensorPowerSequence K).functor.obj x ◁
              (tensorPowerSequenceOne K).natTrans.app (index 0) ≫
          (DayFunctor.η (tensorPowerSequence K)
              (tensorPowerSequence K)).app (x, index 0) := by
      exact convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
        V (tensorPowerSequence K) (tensorPowerSequenceOne K)
        x (index 0)
    slice_lhs 2 3 =>
      rw [hwhisker]
    simp only [Category.assoc, tensorPowerSequenceMul_fac]
    have hcomp :
        ((tensorPowerSequence K).functor.obj x ◁
              DayFunctor.ν Index V) ≫
            ((tensorPowerSequence K).functor.obj x ◁
              (tensorPowerSequenceOne K).natTrans.app (index 0)) =
          (tensorPowerSequence K).functor.obj x ◁
            (DayFunctor.ν Index V ≫
              (tensorPowerSequenceOne K).natTrans.app (index 0)) :=
      (MonoidalCategory.whiskerLeft_comp _ _ _).symm
    have hOneDesc :
        DayFunctor.ν Index V ≫
            (tensorPowerSequenceOne K).natTrans.app (index 0) =
          TensorPower.laxTensorPowerUnit (𝟭 V) K := by
      unfold tensorPowerSequenceOne
      exact DayFunctor.ν_comp_unitDesc _
    have hfacWhisker := hcomp.trans (congrArg
      (fun f => (tensorPowerSequence K).functor.obj x ◁ f)
      hOneDesc)
    slice_lhs 1 2 =>
      exact hfacWhisker
    have hright :
        (tensorPowerSequence K).functor.obj x ◁
              DayFunctor.ν Index V ≫
            (DayFunctor.η (tensorPowerSequence K)
              (𝟙_ (Sequence V))).app (x, index 0) ≫
            (ρ_ (tensorPowerSequence K)).hom.natTrans.app
                (x ⊗ index 0) =
          (ρ_ ((tensorPowerSequence K).functor.obj x)).hom ≫
            (tensorPowerSequence K).functor.map (ρ_ x).inv := by
      exact rightUnitor_hom_unit_app
        V (tensorPowerSequence K) x
    slice_rhs 1 3 =>
      exact hright
    rcases x with ⟨n⟩
    simp only [tensorPowerSequenceMulDesc, degree_index]
    have hrho :
        (ρ_ (⟨n⟩ : Index)).inv = 𝟙 (⟨n⟩ : Index) := by
      apply Discrete.hom_eq
    slice_rhs 2 2 =>
      exact hrho
    simp only [Functor.map_id, Category.comp_id]
    apply eq_of_heq
    exact heq_of_eq
      (TensorPower.laxTensorPowerPairing_zero_right
        (Functor.id V) K n.toAdd)
  mul_assoc := by
    apply DayFunctor.hom_ext
    apply Functor.hom_ext_of_isLeftKanExtension
      (F' := ((tensorPowerSequence K ⊗ tensorPowerSequence K) ⊗
        tensorPowerSequence K).functor)
      (α := DayFunctor.η
        (tensorPowerSequence K ⊗ tensorPowerSequence K)
        (tensorPowerSequence K))
    let _ : ((tensorPowerSequence K ⊗
            tensorPowerSequence K).functor ⊠
          (tensorPowerSequence K).functor).IsLeftKanExtension
        (ExternalProduct.extensionUnitLeft
          (tensorPowerSequence K ⊗ tensorPowerSequence K).functor
          (DayFunctor.η (tensorPowerSequence K)
            (tensorPowerSequence K))
          (tensorPowerSequence K).functor) :=
      ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitLeft
        (tensorPowerSequence K ⊗ tensorPowerSequence K).functor
        (DayFunctor.η (tensorPowerSequence K)
          (tensorPowerSequence K))
        (tensorPowerSequence K).functor
        (isPointwiseLeftKanExtensionConvolutionExtensionUnit
          (tensorPowerSequence K) (tensorPowerSequence K)) |>.isLeftKanExtension
    apply Functor.hom_ext_of_isLeftKanExtension
      (F' := (tensorPowerSequence K ⊗ tensorPowerSequence K).functor ⊠
        (tensorPowerSequence K).functor)
      (α := ExternalProduct.extensionUnitLeft
        (tensorPowerSequence K ⊗ tensorPowerSequence K).functor
        (DayFunctor.η (tensorPowerSequence K)
          (tensorPowerSequence K))
        (tensorPowerSequence K).functor)
    ext ⟨⟨x, y⟩, z⟩
    dsimp [ExternalProduct.extensionUnitLeft]
    simp only [MonoidalCategory.whiskerLeft_id, Category.comp_id]
    have hrightWhisker :
        (DayFunctor.η
            (tensorPowerSequence K ⊗ tensorPowerSequence K)
            (tensorPowerSequence K)).app (x ⊗ y, z) ≫
          (tensorPowerSequenceMul K ▷
              tensorPowerSequence K).natTrans.app
            ((x ⊗ y) ⊗ z) =
        (tensorPowerSequenceMul K).natTrans.app (x ⊗ y) ▷
              (tensorPowerSequence K).functor.obj z ≫
          (DayFunctor.η (tensorPowerSequence K)
              (tensorPowerSequence K)).app (x ⊗ y, z) := by
      exact convolutionExtensionUnit_comp_ι_map_whiskerRight_app
        Index V (tensorPowerSequenceMul K)
        (tensorPowerSequence K) (x ⊗ y) z
    slice_lhs 2 3 =>
      rw [hrightWhisker]
    simp only [Category.assoc]
    slice_lhs 1 2 =>
      rw [← MonoidalCategory.comp_whiskerRight,
        tensorPowerSequenceMul_fac]
    slice_lhs 2 3 =>
      rw [tensorPowerSequenceMul_fac]
    have hassoc :
        (DayFunctor.η (tensorPowerSequence K)
              (tensorPowerSequence K)).app (x, y) ▷
              (tensorPowerSequence K).functor.obj z ≫
            (DayFunctor.η
              (tensorPowerSequence K ⊗ tensorPowerSequence K)
              (tensorPowerSequence K)).app (x ⊗ y, z) ≫
            (α_ (tensorPowerSequence K) (tensorPowerSequence K)
              (tensorPowerSequence K)).hom.natTrans.app
                ((x ⊗ y) ⊗ z) =
          (α_ ((tensorPowerSequence K).functor.obj x)
            ((tensorPowerSequence K).functor.obj y)
            ((tensorPowerSequence K).functor.obj z)).hom ≫
            ((tensorPowerSequence K).functor.obj x ◁
              (DayFunctor.η (tensorPowerSequence K)
                (tensorPowerSequence K)).app (y, z)) ≫
            (DayFunctor.η (tensorPowerSequence K)
              (tensorPowerSequence K ⊗ tensorPowerSequence K)).app
                (x, y ⊗ z) ≫
            (tensorPowerSequence K ⊗
              (tensorPowerSequence K ⊗
                tensorPowerSequence K)).functor.map
              (α_ x y z).inv := by
      exact associator_hom_unit_unit
        V (tensorPowerSequence K) (tensorPowerSequence K)
        (tensorPowerSequence K) x y z
    slice_rhs 1 3 =>
      rw [hassoc]
    simp only [Category.assoc, NatTrans.naturality_assoc]
    rw [(tensorPowerSequenceMul K).natTrans.naturality]
    have hleftWhisker :
        (DayFunctor.η (tensorPowerSequence K)
              (tensorPowerSequence K ⊗ tensorPowerSequence K)).app
                (x, y ⊗ z) ≫
          (tensorPowerSequence K ◁
              tensorPowerSequenceMul K).natTrans.app
            ((tensor Index).obj (x, y ⊗ z)) =
        (tensorPowerSequence K).functor.obj x ◁
              (tensorPowerSequenceMul K).natTrans.app (y ⊗ z) ≫
          (DayFunctor.η (tensorPowerSequence K)
              (tensorPowerSequence K)).app (x, y ⊗ z) := by
      exact convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
        V (tensorPowerSequence K) (tensorPowerSequenceMul K)
        x (y ⊗ z)
    slice_rhs 3 4 =>
      rw [hleftWhisker]
    simp only [Category.assoc]
    slice_rhs 2 3 =>
      rw [← MonoidalCategory.whiskerLeft_comp,
        tensorPowerSequenceMul_fac]
    slice_rhs 3 4 =>
      rw [tensorPowerSequenceMul_fac_tensorObj]
    rcases x with ⟨p⟩
    rcases y with ⟨q⟩
    rcases z with ⟨r⟩
    change ℕ at p
    change ℕ at q
    change ℕ at r
    change
      (TensorPower.laxTensorPowerPairing (Functor.id V) K p q ▷
          TensorPower.tensorPowObj K r) ≫
          TensorPower.laxTensorPowerPairing
            (Functor.id V) K (p + q) r =
        (α_ (TensorPower.tensorPowObj K p)
          (TensorPower.tensorPowObj K q)
          (TensorPower.tensorPowObj K r)).hom ≫
          (TensorPower.tensorPowObj K p ◁
            TensorPower.laxTensorPowerPairing
              (Functor.id V) K q r) ≫
          TensorPower.laxTensorPowerPairing
            (Functor.id V) K p (q + r) ≫
          (tensorPowerSequence K).functor.map
            (α_ (index p) (index q) (index r)).inv
    have hmap :
        (tensorPowerSequence K).functor.map
            (α_ (index p) (index q) (index r)).inv =
          eqToHom (congrArg
            (fun n ↦ TensorPower.tensorPowObj K n)
            (Nat.add_assoc p q r).symm) := by
      rfl
    have hpost :
        TensorPower.laxTensorPowerPairing
              (Functor.id V) K p (q + r) ≫
            (tensorPowerSequence K).functor.map
              (α_ (index p) (index q) (index r)).inv =
          TensorPower.laxTensorPowerPairing
              (Functor.id V) K p (q + r) ≫
            eqToHom (congrArg
              (fun n ↦ TensorPower.tensorPowObj K n)
              (Nat.add_assoc p q r).symm) := by
      exact congrArg
        (fun g => TensorPower.laxTensorPowerPairing
          (Functor.id V) K p (q + r) ≫ g) hmap
    slice_rhs 3 4 =>
      exact hpost
    let e :
        TensorPower.tensorPowObj K ((p + q) + r) ≅
          TensorPower.tensorPowObj K (p + (q + r)) :=
      eqToIso (congrArg
        (fun n ↦ TensorPower.tensorPowObj K n)
        (Nat.add_assoc p q r))
    have he :
        eqToHom (congrArg
          (fun n ↦ TensorPower.tensorPowObj K n)
          (Nat.add_assoc p q r).symm) = e.inv := by
      rfl
    rw [he]
    have hgoal :
        ((TensorPower.laxTensorPowerPairing
              (Functor.id V) K p q ▷
            TensorPower.tensorPowObj K r) ≫
          TensorPower.laxTensorPowerPairing
            (Functor.id V) K (p + q) r) ≫ e.hom =
          (α_ (TensorPower.tensorPowObj K p)
            (TensorPower.tensorPowObj K q)
            (TensorPower.tensorPowObj K r)).hom ≫
            (TensorPower.tensorPowObj K p ◁
              TensorPower.laxTensorPowerPairing
                (Functor.id V) K q r) ≫
            TensorPower.laxTensorPowerPairing
              (Functor.id V) K p (q + r) := by
      simpa [e, MonoidalCategory.tensorHom_def] using
        (TensorPower.laxTensorPowerPairing_assoc
          (Functor.id V) K p q r)
    have hfinal := (Iso.eq_comp_inv e).2 hgoal
    have hfinal' :
        (TensorPower.laxTensorPowerPairing
              (Functor.id V) K p q ▷
            TensorPower.tensorPowObj K r) ≫
          TensorPower.laxTensorPowerPairing
            (Functor.id V) K (p + q) r =
        (α_ (TensorPower.tensorPowObj K p)
          (TensorPower.tensorPowObj K q)
          (TensorPower.tensorPowObj K r)).hom ≫
          (TensorPower.tensorPowObj K p ◁
            TensorPower.laxTensorPowerPairing
              (Functor.id V) K q r) ≫
          TensorPower.laxTensorPowerPairing
            (Functor.id V) K p (q + r) ≫ e.inv := by
      simpa only [Category.assoc] using hfinal
    apply eq_of_heq
    exact heq_of_eq hfinal'

/-- The Day-unit generator followed by the tensor-power monoid unit is the
identity functor's tensor-power unit. -/
theorem tensorPowerSequenceOne_ν (K : V) :
    DayFunctor.ν Index V ≫
        (tensorPowerSequenceMonObj K).one.natTrans.app (index 0) =
      TensorPower.laxTensorPowerUnit (𝟭 V) K := by
  change DayFunctor.ν Index V ≫
      (tensorPowerSequenceOne K).natTrans.app (index 0) = _
  unfold tensorPowerSequenceOne
  exact DayFunctor.ν_comp_unitDesc _

/-- The Day generator followed by tensor-power multiplication is the ordered
tensor-power pairing. -/
theorem tensorPowerSequenceMul_η (K : V) (p q : ℕ) :
    (DayFunctor.η (tensorPowerSequence K)
        (tensorPowerSequence K)).app (index p, index q) ≫
        (tensorPowerSequenceMonObj K).mul.natTrans.app
          (index p ⊗ index q) ≫
        (tensorPowerSequence K).functor.map
          (eqToHom (tensorObj_index p q)) =
      TensorPower.laxTensorPowerPairing (𝟭 V) K p q := by
  change
    (DayFunctor.η (tensorPowerSequence K)
        (tensorPowerSequence K)).app (index p, index q) ≫
        (tensorPowerSequenceMul K).natTrans.app (index p ⊗ index q) ≫
        (tensorPowerSequence K).functor.map
          (eqToHom (tensorObj_index p q)) = _
  have hη :
      (DayFunctor.η (tensorPowerSequence K)
          (tensorPowerSequence K)).app (index p, index q) ≫
          (tensorPowerSequenceMul K).natTrans.app
            (index p ⊗ index q) =
        TensorPower.laxTensorPowerPairing (𝟭 V) K p q := by
    simpa only [tensorPowerSequenceMul, tensorPowerSequenceMulDesc,
      degree_index] using DayFunctor.η_comp_tensorDesc_app
        (tensorPowerSequenceMulDesc K) (index p) (index q)
  rw [← Category.assoc, eqToHom_map]
  apply eq_of_heq
  exact (comp_eqToHom_heq _ _).trans (heq_of_eq hη)

attribute [local instance] tensorPowerSequenceMonObj

/-- Modules over the ordered tensor-power sequence acting on sequences. -/
abbrev TensorPowerModule (K : V) :=
  @CategoryTheory.Mod (Sequence V) _ _
    (Sequence V) _ _
    (tensorPowerSequence K)
    (tensorPowerSequenceMonObj K)

namespace TensorPowerModule

variable {K : V}

/-- The one-step left structure map of a tensor-power module. -/
noncomputable def structureMap (M : TensorPowerModule K) (n : ℕ) :
    K ⊗ M.X.functor.obj (index n) ⟶
      M.X.functor.obj (index (n + 1)) :=
  ((λ_ K).inv ⊗ₘ 𝟙 _) ≫
    (DayFunctor.η (tensorPowerSequence K) M.X).app
      (index 1, index n) ≫
    M.mod.smul.natTrans.app (index 1 ⊗ index n) ≫
    M.X.functor.map
      (eqToHom ((tensorObj_index 1 n).trans
        (congrArg index (Nat.one_add n))))

/-- The one-step structure map is the inverse-left-unitor, Day-generator,
module-action, and forward degree-transport composite. -/
theorem structureMap_eq (M : TensorPowerModule K) (n : ℕ) :
    structureMap M n =
      ((λ_ K).inv ⊗ₘ 𝟙 _) ≫
        (DayFunctor.η (tensorPowerSequence K) M.X).app
          (index 1, index n) ≫
        M.mod.smul.natTrans.app (index 1 ⊗ index n) ≫
        M.X.functor.map
          (eqToHom ((tensorObj_index 1 n).trans
            (congrArg index (Nat.one_add n)))) :=
  (rfl)

/-- One-step structure maps are natural under module morphisms. -/
theorem structureMap_naturality {M N : TensorPowerModule K}
    (f : M ⟶ N) (n : ℕ) :
    structureMap M n ≫ f.hom.natTrans.app (index (n + 1)) =
      (𝟙 K ⊗ₘ f.hom.natTrans.app (index n)) ≫
        structureMap N n := by
  let e : Sequence.index 1 ⊗ Sequence.index n =
      Sequence.index (n + 1) :=
    (Sequence.tensorObj_index 1 n).trans
      (congrArg Sequence.index (Nat.one_add n))
  have hTransport :
      M.X.functor.map (eqToHom e) ≫
          f.hom.natTrans.app (Sequence.index (n + 1)) =
        f.hom.natTrans.app
            (Sequence.index 1 ⊗ Sequence.index n) ≫
          N.X.functor.map (eqToHom e) :=
    f.hom.natTrans.naturality (eqToHom e)
  have hSmul :
      M.mod.smul.natTrans.app
            (Sequence.index 1 ⊗ Sequence.index n) ≫
          f.hom.natTrans.app
            (Sequence.index 1 ⊗ Sequence.index n) =
        (MonoidalLeftActionStruct.actionHomRight
            (Sequence.tensorPowerSequence K) f.hom).natTrans.app
              (Sequence.index 1 ⊗ Sequence.index n) ≫
          N.mod.smul.natTrans.app
            (Sequence.index 1 ⊗ Sequence.index n) := by
    simpa only [DayFunctor.comp_natTrans, NatTrans.comp_app] using
      congrArg
        (fun g :
          (Sequence.tensorPowerSequence K ⊗ M.X ⟶ N.X) =>
          g.natTrans.app
            (Sequence.index 1 ⊗ Sequence.index n))
        (IsModHom.smul_hom
          (A := Sequence.tensorPowerSequence K) (f := f.hom))
  have hEta :
      (DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
            (Sequence.index 1, Sequence.index n) ≫
          (MonoidalLeftActionStruct.actionHomRight
              (Sequence.tensorPowerSequence K) f.hom).natTrans.app
                (Sequence.index 1 ⊗ Sequence.index n) =
        ((Sequence.tensorPowerSequence K).functor.obj
            (Sequence.index 1) ◁
              f.hom.natTrans.app (Sequence.index n)) ≫
          (DayFunctor.η (Sequence.tensorPowerSequence K) N.X).app
            (Sequence.index 1, Sequence.index n) := by
    have h :=
      convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
        V (Sequence.tensorPowerSequence K) f.hom
        (Sequence.index 1) (Sequence.index n)
    convert h using 1 <;> rfl
  have hFirst :
      ((λ_ K).inv ⊗ₘ 𝟙 (M.X.functor.obj (Sequence.index n))) ≫
          ((𝟙_ V ⊗ K) ◁
            f.hom.natTrans.app (Sequence.index n)) =
        (𝟙 K ⊗ₘ f.hom.natTrans.app (Sequence.index n)) ≫
          ((λ_ K).inv ⊗ₘ
            𝟙 (N.X.functor.obj (Sequence.index n))) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
  have hCore :
      (DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
            (Sequence.index 1, Sequence.index n) ≫
          M.mod.smul.natTrans.app
              (Sequence.index 1 ⊗ Sequence.index n) ≫
            M.X.functor.map (eqToHom e) ≫
              f.hom.natTrans.app (Sequence.index (n + 1)) =
        ((Sequence.tensorPowerSequence K).functor.obj
            (Sequence.index 1) ◁
              f.hom.natTrans.app (Sequence.index n)) ≫
          (DayFunctor.η (Sequence.tensorPowerSequence K) N.X).app
              (Sequence.index 1, Sequence.index n) ≫
            N.mod.smul.natTrans.app
                (Sequence.index 1 ⊗ Sequence.index n) ≫
              N.X.functor.map (eqToHom e) := by
    calc
      _ =
          (DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
              (Sequence.index 1, Sequence.index n) ≫
            (M.mod.smul.natTrans.app
                (Sequence.index 1 ⊗ Sequence.index n) ≫
              (M.X.functor.map (eqToHom e) ≫
                f.hom.natTrans.app
                  (Sequence.index (n + 1)))) := by rfl
      _ =
          (DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
              (Sequence.index 1, Sequence.index n) ≫
            (M.mod.smul.natTrans.app
                (Sequence.index 1 ⊗ Sequence.index n) ≫
              (f.hom.natTrans.app
                  (Sequence.index 1 ⊗ Sequence.index n) ≫
                N.X.functor.map (eqToHom e))) := by rw [hTransport]
      _ =
          (DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
              (Sequence.index 1, Sequence.index n) ≫
            ((M.mod.smul.natTrans.app
                (Sequence.index 1 ⊗ Sequence.index n) ≫
              f.hom.natTrans.app
                (Sequence.index 1 ⊗ Sequence.index n)) ≫
              N.X.functor.map (eqToHom e)) := by
                simp only [Category.assoc]
      _ =
          (DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
              (Sequence.index 1, Sequence.index n) ≫
            (((MonoidalLeftActionStruct.actionHomRight
                (Sequence.tensorPowerSequence K) f.hom).natTrans.app
                  (Sequence.index 1 ⊗ Sequence.index n) ≫
              N.mod.smul.natTrans.app
                (Sequence.index 1 ⊗ Sequence.index n)) ≫
              N.X.functor.map (eqToHom e)) := by rw [hSmul]
      _ =
          ((DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
              (Sequence.index 1, Sequence.index n) ≫
            (MonoidalLeftActionStruct.actionHomRight
              (Sequence.tensorPowerSequence K) f.hom).natTrans.app
                (Sequence.index 1 ⊗ Sequence.index n)) ≫
            (N.mod.smul.natTrans.app
                (Sequence.index 1 ⊗ Sequence.index n) ≫
              N.X.functor.map (eqToHom e)) := by
                simp only [Category.assoc]
      _ =
          (((Sequence.tensorPowerSequence K).functor.obj
              (Sequence.index 1) ◁
                f.hom.natTrans.app (Sequence.index n)) ≫
            (DayFunctor.η (Sequence.tensorPowerSequence K) N.X).app
              (Sequence.index 1, Sequence.index n)) ≫
            (N.mod.smul.natTrans.app
                (Sequence.index 1 ⊗ Sequence.index n) ≫
              N.X.functor.map (eqToHom e)) := by rw [hEta]
      _ = _ := by simp only [Category.assoc]
  have hCoreExact :
      ((DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
            (Sequence.index 1, Sequence.index n) ≫
          M.mod.smul.natTrans.app
            (Sequence.index 1 ⊗ Sequence.index n) ≫
          M.X.functor.map
            (eqToHom
              ((Sequence.tensorObj_index 1 n).trans
                (congrArg Sequence.index (Nat.one_add n))))) ≫
        f.hom.natTrans.app (Sequence.index (n + 1)) =
      ((Sequence.tensorPowerSequence K).functor.obj
          (Sequence.index 1) ◁
            f.hom.natTrans.app (Sequence.index n)) ≫
        (DayFunctor.η (Sequence.tensorPowerSequence K) N.X).app
          (Sequence.index 1, Sequence.index n) ≫
        N.mod.smul.natTrans.app
          (Sequence.index 1 ⊗ Sequence.index n) ≫
        N.X.functor.map
          (eqToHom
            ((Sequence.tensorObj_index 1 n).trans
              (congrArg Sequence.index (Nat.one_add n)))) := by
    simpa only [e, Category.assoc] using hCore
  have hCoreConcrete :
      (((DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
            (Sequence.index 1, Sequence.index n) ≫
          M.mod.smul.natTrans.app
            (Sequence.index 1 ⊗ Sequence.index n) ≫
          M.X.functor.map
            (eqToHom
              ((Sequence.tensorObj_index 1 n).trans
                (congrArg Sequence.index (Nat.one_add n))))) ≫
        f.hom.natTrans.app (Sequence.index (n + 1)) :
          (𝟙_ V ⊗ K) ⊗ M.X.functor.obj (Sequence.index n) ⟶
            N.X.functor.obj (Sequence.index (n + 1))) =
      (((𝟙_ V ⊗ K) ◁
          f.hom.natTrans.app (Sequence.index n)) ≫
        (DayFunctor.η (Sequence.tensorPowerSequence K) N.X).app
          (Sequence.index 1, Sequence.index n) ≫
        N.mod.smul.natTrans.app
          (Sequence.index 1 ⊗ Sequence.index n) ≫
        N.X.functor.map
          (eqToHom
            ((Sequence.tensorObj_index 1 n).trans
              (congrArg Sequence.index (Nat.one_add n)))) :
          (𝟙_ V ⊗ K) ⊗ M.X.functor.obj (Sequence.index n) ⟶
            N.X.functor.obj (Sequence.index (n + 1))) := by
    exact hCoreExact
  unfold Sequence.TensorPowerModule.structureMap
  have hWhiskered := congrArg
    (fun z : (𝟙_ V ⊗ K) ⊗
          M.X.functor.obj (Sequence.index n) ⟶
        N.X.functor.obj (Sequence.index (n + 1)) =>
      ((λ_ K).inv ⊗ₘ
        𝟙 (M.X.functor.obj (Sequence.index n))) ≫ z)
    hCoreConcrete
  have hFirstWhiskered := congrArg
    (fun z : K ⊗ M.X.functor.obj (Sequence.index n) ⟶
        (𝟙_ V ⊗ K) ⊗
          N.X.functor.obj (Sequence.index n) =>
      z ≫
        (DayFunctor.η (Sequence.tensorPowerSequence K) N.X).app
          (Sequence.index 1, Sequence.index n) ≫
        N.mod.smul.natTrans.app
          (Sequence.index 1 ⊗ Sequence.index n) ≫
        N.X.functor.map
          (eqToHom
            ((Sequence.tensorObj_index 1 n).trans
              (congrArg Sequence.index (Nat.one_add n)))))
    hFirst
  calc
    _ = ((λ_ K).inv ⊗ₘ
          𝟙 (M.X.functor.obj (Sequence.index n))) ≫
        (((𝟙_ V ⊗ K) ◁
            f.hom.natTrans.app (Sequence.index n)) ≫
          (DayFunctor.η (Sequence.tensorPowerSequence K) N.X).app
            (Sequence.index 1, Sequence.index n) ≫
          N.mod.smul.natTrans.app
            (Sequence.index 1 ⊗ Sequence.index n) ≫
          N.X.functor.map
            (eqToHom
              ((Sequence.tensorObj_index 1 n).trans
                (congrArg Sequence.index (Nat.one_add n))))) := by
      simpa only [Category.assoc] using hWhiskered
    _ = _ := by
      simpa only [Category.assoc] using hFirstWhiskered

end TensorPowerModule
end
end CategoryTheory.Sequence
