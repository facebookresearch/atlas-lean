/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.LaxBraidedMonoid

/-!
# Indexed lax structures of Day monoids

The ordinary diagram of a Day monoid is lax monoidal. A commutative Day
monoid over a symmetric source and braided target is lax braided. Its
commutative multiplication needs only braided source and target categories.
The generating unit and tensor coefficients also characterize monoid morphisms.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor Limits MonoidalCategory
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace CategoryTheory.MonoidalCategory.DayFunctor

section CanonicalDayEquations

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} {V : Type u₂} [Category.{v₁} C] [Category.{v₂} V]
  [MonoidalCategory C] [MonoidalCategory V]
  [∀ F G : C ⥤ V, (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ C)).HasPointwiseLeftKanExtension (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (W : V) (a : C), PreservesColimitsOfShape (CostructuredArrow (tensor C) a) (tensorLeft W)]
  [∀ (W : V) (a : C), PreservesColimitsOfShape (CostructuredArrow (tensor C) a) (tensorRight W)]
  [∀ (W : V) (a : C),
    PreservesColimitsOfShape (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) a) (tensorLeft W)]
  [∀ (W : V) (a : C),
    PreservesColimitsOfShape (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) a) (tensorRight W)]
  [∀ (W : V) (a : C × C),
    PreservesColimitsOfShape (CostructuredArrow ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) a)
      (tensorRight W)]
  [∀ (W : V) (a : C × C),
    PreservesColimitsOfShape (CostructuredArrow ((tensor C).prod (𝟭 C)) a) (tensorRight W)]

/-- The actual Day tensor of arbitrary diagram maps retains both original coefficient components. -/
theorem tensorHom_η {X Y X' Y' : DayFunctor C V} (f : X ⟶ X') (g : Y ⟶ Y') (a b : C) :
    (DayFunctor.η X Y).app (a, b) ≫ (f ⊗ₘ g).natTrans.app (a ⊗ b) =
      (f.natTrans.app a ⊗ₘ g.natTrans.app b) ≫ (DayFunctor.η X' Y').app (a, b) :=
  LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_tensorHom_app
    C V f g a b

namespace Monoid

/-- Coefficient unit and multiplication laws determine a Day-monoid morphism. -/
theorem isMonHom_of_coefficients (M Q : DayFunctor C V) [MonObj M] [MonObj Q] (f : M ⟶ Q)
    (ho : DayFunctor.ν C V ≫ η[M].natTrans.app (𝟙_ C) ≫ f.natTrans.app (𝟙_ C) =
      DayFunctor.ν C V ≫ η[Q].natTrans.app (𝟙_ C))
    (hm : ∀ a b : C, (DayFunctor.η M M).app (a, b) ≫ μ[M].natTrans.app (a ⊗ b) ≫
      f.natTrans.app (a ⊗ b) = (f.natTrans.app a ⊗ₘ f.natTrans.app b) ≫
        (DayFunctor.η Q Q).app (a, b) ≫ μ[Q].natTrans.app (a ⊗ b)) : IsMonHom f where
  one_hom := by
    apply DayFunctor.unit_hom_ext
    exact ho
  mul_hom := by
    apply DayFunctor.tensor_hom_ext
    intro a b
    exact (hm a b).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun g => g ≫ μ[Q].natTrans.app (a ⊗ b)) (tensorHom_η f f a b)).trans
          (Category.assoc _ _ _))).symm

end Monoid

/-- An original scalar arrow acts on every actual Day pair map through its complete coefficient component. -/
theorem scalarAction_η {A B X Y : DayFunctor C V} (i : A ⟶ B)
    (s : B ⊗ X ⟶ Y) (a b : C) :
    (DayFunctor.η A X).app (a, b) ≫ ((i ▷ X) ≫ s).natTrans.app (a ⊗ b) =
      (i.natTrans.app a ⊗ₘ 𝟙 (X.functor.obj b)) ≫
        (DayFunctor.η B X).app (a, b) ≫ s.natTrans.app (a ⊗ b) := by
  have h : (DayFunctor.η A X).app (a, b) ≫ (i ▷ X).natTrans.app (a ⊗ b) =
      (i.natTrans.app a ▷ X.functor.obj b) ≫ (DayFunctor.η B X).app (a, b) :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerRight_app
      C V i X a b
  rw [tensorHom_id]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ s.natTrans.app (a ⊗ b)) h).trans (Category.assoc _ _ _))

end CanonicalDayEquations

namespace Monoid
universe uC vC uV vV
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [∀ F G : C ⥤ V, (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ C)).HasPointwiseLeftKanExtension (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (W : V) (a : C), PreservesColimitsOfShape (CostructuredArrow (tensor C) a) (tensorLeft W)]
  [∀ (W : V) (a : C), PreservesColimitsOfShape (CostructuredArrow (tensor C) a) (tensorRight W)]
  [∀ (W : V) (a : C),
    PreservesColimitsOfShape (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) a) (tensorLeft W)]
  [∀ (W : V) (a : C),
    PreservesColimitsOfShape (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) a) (tensorRight W)]
  [∀ (W : V) (a : C × C),
    PreservesColimitsOfShape (CostructuredArrow ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) a)
      (tensorRight W)]
  [∀ (W : V) (a : C × C),
    PreservesColimitsOfShape (CostructuredArrow ((tensor C).prod (𝟭 C)) a) (tensorRight W)]
variable (F : DayFunctor C V) [MonObj F]

/-- The entire original pair transformation of an arbitrary Day monoid. -/
def pair : F.functor ⊠ F.functor ⟶ tensor C ⋙ F.functor :=
  DayFunctor.η F F ≫ Functor.whiskerLeft (tensor C) μ[F].natTrans

/-- The whole original indexed multiplication coefficient. -/
def multiplication (a b : C) : F.functor.obj a ⊗ F.functor.obj b ⟶ F.functor.obj (a ⊗ b) :=
  (pair F).app (a, b)

/-- The whole original indexed unit coefficient. -/
def unit : 𝟙_ V ⟶ F.functor.obj (𝟙_ C) :=
  DayFunctor.ν C V ≫ η[F].natTrans.app (𝟙_ C)

/-- All original pairs of index arrows preserve the full multiplication. -/
theorem multiplication_natural {a a' b b' : C} (f : a ⟶ a') (g : b ⟶ b') :
    (F.functor.map f ⊗ₘ F.functor.map g) ≫ multiplication F a' b' =
      multiplication F a b ≫ F.functor.map (f ⊗ₘ g) :=
  by
    simpa only [multiplication, externalProductBifunctor_obj_map, Functor.comp_map, tensor_map, tensorHom_def] using
      (pair F).naturality (show (a, b) ⟶ (a', b') from (f, g))

/-- The original right indexed unit follows from the actual full Day monoid unit. -/
theorem right_unitality (a : C) :
    (F.functor.obj a ◁ unit F) ≫ multiplication F a (𝟙_ C) ≫ F.functor.map (ρ_ a).hom =
      (ρ_ (F.functor.obj a)).hom := by
  have hMap :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
      (C := C) V F η[F] a (𝟙_ C)
  have hWhole := congrArg (fun q : F ⊗ 𝟙_ (DayFunctor C V) ⟶ F =>
    (F.functor.obj a ◁ DayFunctor.ν C V) ≫
      (DayFunctor.η F (𝟙_ (DayFunctor C V))).app (a, 𝟙_ C) ≫
        q.natTrans.app (a ⊗ 𝟙_ C) ≫ F.functor.map (ρ_ a).hom) (MonObj.mul_one F)
  have hUnitor := LawfulDayConvolutionMonoidalCategoryStruct.rightUnitor_hom_unit_app (C := C) V F a
  change (DayFunctor.η F (𝟙_ (DayFunctor C V))).app (a, 𝟙_ C) ≫
      (F ◁ η[F]).natTrans.app (a ⊗ 𝟙_ C) =
    (F.functor.obj a ◁ η[F].natTrans.app (𝟙_ C)) ≫ (DayFunctor.η F F).app (a, 𝟙_ C) at hMap
  change (F.functor.obj a ◁ DayFunctor.ν C V) ≫
      (DayFunctor.η F (𝟙_ (DayFunctor C V))).app (a, 𝟙_ C) ≫
        (ρ_ F).hom.natTrans.app (a ⊗ 𝟙_ C) =
    (ρ_ (F.functor.obj a)).hom ≫ F.functor.map (ρ_ a).inv at hUnitor
  change (F.functor.obj a ◁ (DayFunctor.ν C V ≫ η[F].natTrans.app (𝟙_ C))) ≫
    ((DayFunctor.η F F).app (a, 𝟙_ C) ≫ μ[F].natTrans.app (a ⊗ 𝟙_ C)) ≫
      F.functor.map (ρ_ a).hom = _
  rw [MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  calc
    _ = (F.functor.obj a ◁ DayFunctor.ν C V) ≫
        (DayFunctor.η F (𝟙_ (DayFunctor C V))).app (a, 𝟙_ C) ≫
          (F ◁ η[F]).natTrans.app (a ⊗ 𝟙_ C) ≫ μ[F].natTrans.app (a ⊗ 𝟙_ C) ≫
            F.functor.map (ρ_ a).hom := by
      simpa only [Category.assoc] using
        congrArg (fun q => (F.functor.obj a ◁ DayFunctor.ν C V) ≫ q ≫
          μ[F].natTrans.app (a ⊗ 𝟙_ C) ≫ F.functor.map (ρ_ a).hom) hMap.symm
    _ = (F.functor.obj a ◁ DayFunctor.ν C V) ≫
        (DayFunctor.η F (𝟙_ (DayFunctor C V))).app (a, 𝟙_ C) ≫
          (ρ_ F).hom.natTrans.app (a ⊗ 𝟙_ C) ≫ F.functor.map (ρ_ a).hom := by
      simpa only [DayFunctor.comp_natTrans, NatTrans.comp_app, Category.assoc] using hWhole
    _ = (ρ_ (F.functor.obj a)).hom ≫ F.functor.map (ρ_ a).inv ≫ F.functor.map (ρ_ a).hom :=
      by
        simpa only [Category.assoc] using congrArg (fun q => q ≫ F.functor.map (ρ_ a).hom) hUnitor
    _ = _ := by
      exact (congrArg (fun q => (ρ_ (F.functor.obj a)).hom ≫ q)
        (F.functor.mapIso (ρ_ a)).inv_hom_id).trans (Category.comp_id _)

/-- The original left indexed unit follows from the same complete original Day monoid. -/
theorem left_unitality (a : C) :
    (unit F ▷ F.functor.obj a) ≫ multiplication F (𝟙_ C) a ≫ F.functor.map (λ_ a).hom =
      (λ_ (F.functor.obj a)).hom := by
  have hMap :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerRight_app
      C V η[F] F (𝟙_ C) a
  have hWhole := congrArg (fun q : 𝟙_ (DayFunctor C V) ⊗ F ⟶ F =>
    (DayFunctor.ν C V ▷ F.functor.obj a) ≫
      (DayFunctor.η (𝟙_ (DayFunctor C V)) F).app (𝟙_ C, a) ≫
        q.natTrans.app (𝟙_ C ⊗ a) ≫ F.functor.map (λ_ a).hom) (MonObj.one_mul F)
  have hUnitor := LawfulDayConvolutionMonoidalCategoryStruct.leftUnitor_hom_unit_app (C := C) V F a
  change (DayFunctor.η (𝟙_ (DayFunctor C V)) F).app (𝟙_ C, a) ≫
      (η[F] ▷ F).natTrans.app (𝟙_ C ⊗ a) =
    (η[F].natTrans.app (𝟙_ C) ▷ F.functor.obj a) ≫ (DayFunctor.η F F).app (𝟙_ C, a) at hMap
  change (DayFunctor.ν C V ▷ F.functor.obj a) ≫
      (DayFunctor.η (𝟙_ (DayFunctor C V)) F).app (𝟙_ C, a) ≫
        (λ_ F).hom.natTrans.app (𝟙_ C ⊗ a) =
    (λ_ (F.functor.obj a)).hom ≫ F.functor.map (λ_ a).inv at hUnitor
  change ((DayFunctor.ν C V ≫ η[F].natTrans.app (𝟙_ C)) ▷ F.functor.obj a) ≫
    ((DayFunctor.η F F).app (𝟙_ C, a) ≫ μ[F].natTrans.app (𝟙_ C ⊗ a)) ≫
      F.functor.map (λ_ a).hom = _
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  calc
    _ = (DayFunctor.ν C V ▷ F.functor.obj a) ≫
        (DayFunctor.η (𝟙_ (DayFunctor C V)) F).app (𝟙_ C, a) ≫
          (η[F] ▷ F).natTrans.app (𝟙_ C ⊗ a) ≫ μ[F].natTrans.app (𝟙_ C ⊗ a) ≫
            F.functor.map (λ_ a).hom := by
      simpa only [Category.assoc] using
        congrArg (fun q => (DayFunctor.ν C V ▷ F.functor.obj a) ≫ q ≫
          μ[F].natTrans.app (𝟙_ C ⊗ a) ≫ F.functor.map (λ_ a).hom) hMap.symm
    _ = (DayFunctor.ν C V ▷ F.functor.obj a) ≫
        (DayFunctor.η (𝟙_ (DayFunctor C V)) F).app (𝟙_ C, a) ≫
          (λ_ F).hom.natTrans.app (𝟙_ C ⊗ a) ≫ F.functor.map (λ_ a).hom := by
      simpa only [DayFunctor.comp_natTrans, NatTrans.comp_app, Category.assoc] using hWhole
    _ = (λ_ (F.functor.obj a)).hom ≫ F.functor.map (λ_ a).inv ≫ F.functor.map (λ_ a).hom :=
      by
        simpa only [Category.assoc] using congrArg (fun q => q ≫ F.functor.map (λ_ a).hom) hUnitor
    _ = _ := by
      exact (congrArg (fun q => (λ_ (F.functor.obj a)).hom ≫ q)
        (F.functor.mapIso (λ_ a)).inv_hom_id).trans (Category.comp_id _)
end Monoid

namespace Monoid
universe uC vC uV vV
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [∀ F G : C ⥤ V, (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ C)).HasPointwiseLeftKanExtension (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (W : V) (a : C), PreservesColimitsOfShape (CostructuredArrow (tensor C) a) (tensorLeft W)]
  [∀ (W : V) (a : C), PreservesColimitsOfShape (CostructuredArrow (tensor C) a) (tensorRight W)]
  [∀ (W : V) (a : C),
    PreservesColimitsOfShape (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) a) (tensorLeft W)]
  [∀ (W : V) (a : C),
    PreservesColimitsOfShape (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) a) (tensorRight W)]
  [∀ (W : V) (a : C × C),
    PreservesColimitsOfShape (CostructuredArrow ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) a)
      (tensorRight W)]
  [∀ (W : V) (a : C × C),
    PreservesColimitsOfShape (CostructuredArrow ((tensor C).prod (𝟭 C)) a) (tensorRight W)]
variable (F : DayFunctor C V) [MonObj F]


/-- Every original indexed multiplication keeps the full Day associator and original index associator. -/
theorem multiplication_associative (a b c : C) :
    (multiplication F a b ▷ F.functor.obj c) ≫ multiplication F (a ⊗ b) c ≫
      F.functor.map (α_ a b c).hom =
    (α_ (F.functor.obj a) (F.functor.obj b) (F.functor.obj c)).hom ≫
      (F.functor.obj a ◁ multiplication F b c) ≫ multiplication F a (b ⊗ c) := by
  have hR := LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerRight_app
    C V μ[F] F (a ⊗ b) c
  change (DayFunctor.η (F ⊗ F) F).app (a ⊗ b, c) ≫
      (μ[F] ▷ F).natTrans.app ((a ⊗ b) ⊗ c) =
    (μ[F].natTrans.app (a ⊗ b) ▷ F.functor.obj c) ≫
      (DayFunctor.η F F).app (a ⊗ b, c) at hR
  have hL := LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
    (C := C) V F μ[F] a (b ⊗ c)
  change (DayFunctor.η F (F ⊗ F)).app (a, b ⊗ c) ≫
      (F ◁ μ[F]).natTrans.app (a ⊗ (b ⊗ c)) =
    (F.functor.obj a ◁ μ[F].natTrans.app (b ⊗ c)) ≫
      (DayFunctor.η F F).app (a, b ⊗ c) at hL
  have hAssoc := LawfulDayConvolutionMonoidalCategoryStruct.associator_hom_unit_unit
    (C := C) V F F F a b c
  change ((DayFunctor.η F F).app (a, b) ▷ F.functor.obj c) ≫
      (DayFunctor.η (F ⊗ F) F).app (a ⊗ b, c) ≫
        (α_ F F F).hom.natTrans.app ((a ⊗ b) ⊗ c) =
    (α_ (F.functor.obj a) (F.functor.obj b) (F.functor.obj c)).hom ≫
      (F.functor.obj a ◁ (DayFunctor.η F F).app (b, c)) ≫
        (DayFunctor.η F (F ⊗ F)).app (a, b ⊗ c) ≫
          (F ⊗ (F ⊗ F)).functor.map (α_ a b c).inv at hAssoc
  have hWhole := congrArg (fun q : (F ⊗ F) ⊗ F ⟶ F =>
    ((DayFunctor.η F F).app (a, b) ▷ F.functor.obj c) ≫
      (DayFunctor.η (F ⊗ F) F).app (a ⊗ b, c) ≫
        q.natTrans.app ((a ⊗ b) ⊗ c) ≫ F.functor.map (α_ a b c).hom) (MonObj.mul_assoc F)
  have hn := ((F ◁ μ[F]) ≫ μ[F]).natTrans.naturality (α_ a b c).inv
  change (F ⊗ (F ⊗ F)).functor.map (α_ a b c).inv ≫
      ((F ◁ μ[F]).natTrans.app ((a ⊗ b) ⊗ c) ≫ μ[F].natTrans.app ((a ⊗ b) ⊗ c)) =
    ((F ◁ μ[F]).natTrans.app (a ⊗ (b ⊗ c)) ≫ μ[F].natTrans.app (a ⊗ (b ⊗ c))) ≫
      F.functor.map (α_ a b c).inv at hn
  have hn0 := congrArg (fun q => q ≫ F.functor.map (α_ a b c).hom) hn
  have hi := (F.functor.mapIso (α_ a b c)).inv_hom_id
  change F.functor.map (α_ a b c).inv ≫ F.functor.map (α_ a b c).hom =
    𝟙 (F.functor.obj (a ⊗ (b ⊗ c))) at hi
  simp only [Category.assoc] at hn0
  rw [hi, Category.comp_id] at hn0
  change ((DayFunctor.η F F).app (a, b) ≫ μ[F].natTrans.app (a ⊗ b)) ▷ F.functor.obj c ≫
      ((DayFunctor.η F F).app (a ⊗ b, c) ≫ μ[F].natTrans.app ((a ⊗ b) ⊗ c)) ≫
        F.functor.map (α_ a b c).hom =
    (α_ (F.functor.obj a) (F.functor.obj b) (F.functor.obj c)).hom ≫
      (F.functor.obj a ◁ ((DayFunctor.η F F).app (b, c) ≫ μ[F].natTrans.app (b ⊗ c))) ≫
        ((DayFunctor.η F F).app (a, b ⊗ c) ≫ μ[F].natTrans.app (a ⊗ (b ⊗ c)))
  rw [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  calc
    _ = ((DayFunctor.η F F).app (a, b) ▷ F.functor.obj c) ≫
        (DayFunctor.η (F ⊗ F) F).app (a ⊗ b, c) ≫
          (μ[F] ▷ F).natTrans.app ((a ⊗ b) ⊗ c) ≫ μ[F].natTrans.app ((a ⊗ b) ⊗ c) ≫
            F.functor.map (α_ a b c).hom := by
      simpa only [Category.assoc] using congrArg (fun q =>
        ((DayFunctor.η F F).app (a, b) ▷ F.functor.obj c) ≫ q ≫
          μ[F].natTrans.app ((a ⊗ b) ⊗ c) ≫ F.functor.map (α_ a b c).hom) hR.symm
    _ = ((DayFunctor.η F F).app (a, b) ▷ F.functor.obj c) ≫
        (DayFunctor.η (F ⊗ F) F).app (a ⊗ b, c) ≫
          (α_ F F F).hom.natTrans.app ((a ⊗ b) ⊗ c) ≫
            (F ◁ μ[F]).natTrans.app ((a ⊗ b) ⊗ c) ≫ μ[F].natTrans.app ((a ⊗ b) ⊗ c) ≫
              F.functor.map (α_ a b c).hom := by
      simpa only [DayFunctor.comp_natTrans, NatTrans.comp_app, Category.assoc] using hWhole
    _ = (α_ (F.functor.obj a) (F.functor.obj b) (F.functor.obj c)).hom ≫
        (F.functor.obj a ◁ (DayFunctor.η F F).app (b, c)) ≫
          (DayFunctor.η F (F ⊗ F)).app (a, b ⊗ c) ≫
            (F ⊗ (F ⊗ F)).functor.map (α_ a b c).inv ≫
              (F ◁ μ[F]).natTrans.app ((a ⊗ b) ⊗ c) ≫ μ[F].natTrans.app ((a ⊗ b) ⊗ c) ≫
                F.functor.map (α_ a b c).hom := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫
        (F ◁ μ[F]).natTrans.app ((a ⊗ b) ⊗ c) ≫ μ[F].natTrans.app ((a ⊗ b) ⊗ c) ≫
          F.functor.map (α_ a b c).hom) hAssoc
    _ = (α_ (F.functor.obj a) (F.functor.obj b) (F.functor.obj c)).hom ≫
        (F.functor.obj a ◁ (DayFunctor.η F F).app (b, c)) ≫
          (DayFunctor.η F (F ⊗ F)).app (a, b ⊗ c) ≫
            (F ◁ μ[F]).natTrans.app (a ⊗ (b ⊗ c)) ≫ μ[F].natTrans.app (a ⊗ (b ⊗ c)) := by
      exact congrArg (fun q =>
        (α_ (F.functor.obj a) (F.functor.obj b) (F.functor.obj c)).hom ≫
          (F.functor.obj a ◁ (DayFunctor.η F F).app (b, c)) ≫
            (DayFunctor.η F (F ⊗ F)).app (a, b ⊗ c) ≫ q) hn0
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun q =>
        (α_ (F.functor.obj a) (F.functor.obj b) (F.functor.obj c)).hom ≫
          (F.functor.obj a ◁ (DayFunctor.η F F).app (b, c)) ≫ q ≫
            μ[F].natTrans.app (a ⊗ (b ⊗ c))) hL

/-- The complete ordinary diagram of the actual Day monoid is genuinely lax monoidal. -/
@[instance_reducible]
def laxMonoidal : F.functor.LaxMonoidal where
  ε := unit F
  «μ» := multiplication F
  μ_natural_left f a := by
    simpa only [F.functor.map_id, tensorHom_id] using multiplication_natural F f (𝟙 a)
  μ_natural_right a f := by
    simpa only [F.functor.map_id, id_tensorHom] using multiplication_natural F (𝟙 a) f
  associativity := multiplication_associative F
  left_unitality a := (left_unitality F a).symm
  right_unitality a := (right_unitality F a).symm
end Monoid


namespace Monoid
universe uC vC uV vV
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [∀ F G : C ⥤ V, (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ C)).HasPointwiseLeftKanExtension (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (W : V) (a : C), PreservesColimitsOfShape (CostructuredArrow (tensor C) a) (tensorLeft W)]
  [∀ (W : V) (a : C), PreservesColimitsOfShape (CostructuredArrow (tensor C) a) (tensorRight W)]
  [∀ (W : V) (a : C),
    PreservesColimitsOfShape (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) a) (tensorLeft W)]
  [∀ (W : V) (a : C),
    PreservesColimitsOfShape (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) a) (tensorRight W)]
  [∀ (W : V) (a : C × C),
    PreservesColimitsOfShape (CostructuredArrow ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) a)
      (tensorRight W)]
  [∀ (W : V) (a : C × C),
    PreservesColimitsOfShape (CostructuredArrow ((tensor C).prod (𝟭 C)) a) (tensorRight W)]

section Braided

variable [BraidedCategory C] [BraidedCategory V]
variable (F : DayFunctor C V) [MonObj F] [IsCommMonObj F]

/-- The actual Day commutative multiplication retains every full indexed braiding coefficient. -/
theorem multiplication_commutative (a b : C) :
    (β_ (F.functor.obj a) (F.functor.obj b)).hom ≫ multiplication F b a ≫
      F.functor.map (β_ b a).hom = multiplication F a b := by
  let _ : DayConvolution F.functor F.functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution C V (DayFunctor C V) F F
  have hWhole := congrArg (fun t : F ⊗ F ⟶ F =>
    (DayFunctor.η F F).app (a, b) ≫ t.natTrans.app (a ⊗ b)) (IsCommMonObj.mul_comm F)
  have hBraid : (DayFunctor.η F F).app (a, b) ≫ (β_ F F).hom.natTrans.app (a ⊗ b) =
      (β_ (F.functor.obj a) (F.functor.obj b)).hom ≫
        (DayFunctor.η F F).app (b, a) ≫ (F ⊗ F).functor.map (β_ b a).hom := by
    change (DayConvolution.unit F.functor F.functor).app (a, b) ≫
      (DayConvolution.braiding F.functor F.functor).hom.app (a ⊗ b) = _
    exact DayConvolution.unit_app_braiding_hom_app F.functor F.functor a b
  have hNat := μ[F].natTrans.naturality (β_ b a).hom
  change (DayFunctor.η F F).app (a, b) ≫ (β_ F F).hom.natTrans.app (a ⊗ b) ≫
      μ[F].natTrans.app (a ⊗ b) = (DayFunctor.η F F).app (a, b) ≫ μ[F].natTrans.app (a ⊗ b) at hWhole
  have hLeft : (DayFunctor.η F F).app (a, b) ≫ (β_ F F).hom.natTrans.app (a ⊗ b) ≫
      μ[F].natTrans.app (a ⊗ b) =
    (β_ (F.functor.obj a) (F.functor.obj b)).hom ≫ multiplication F b a ≫
      F.functor.map (β_ b a).hom := by
    calc
      _ = (β_ (F.functor.obj a) (F.functor.obj b)).hom ≫
          (DayFunctor.η F F).app (b, a) ≫ (F ⊗ F).functor.map (β_ b a).hom ≫
            μ[F].natTrans.app (a ⊗ b) := by
        simpa only [Category.assoc] using congrArg (fun t => t ≫ μ[F].natTrans.app (a ⊗ b)) hBraid
      _ = (β_ (F.functor.obj a) (F.functor.obj b)).hom ≫
          (DayFunctor.η F F).app (b, a) ≫ μ[F].natTrans.app (b ⊗ a) ≫
            F.functor.map (β_ b a).hom :=
        congrArg (fun t => (β_ (F.functor.obj a) (F.functor.obj b)).hom ≫
          (DayFunctor.η F F).app (b, a) ≫ t) hNat
      _ = _ := congrArg (fun t =>
          (β_ (F.functor.obj a) (F.functor.obj b)).hom ≫ t)
        (Category.assoc ((DayFunctor.η F F).app (b, a))
          (μ[F].natTrans.app (b ⊗ a)) (F.functor.map (β_ b a).hom)).symm
  exact hLeft.symm.trans hWhole

end Braided

variable [SymmetricCategory C] [BraidedCategory V]
variable (F : DayFunctor C V) [MonObj F] [IsCommMonObj F]

/-- The original ordinary diagram of every actual commutative Day monoid is lax braided. -/
@[instance_reducible]
def laxBraided : letI := laxMonoidal F; F.functor.LaxBraided := by
  letI := laxMonoidal F
  refine { braided := ?_ }
  intro a b
  have h := congrArg (fun t => t ≫ F.functor.map (β_ a b).hom) (multiplication_commutative F a b)
  have hi := congrArg F.functor.map (SymmetricCategory.symmetry b a)
  have hi' : F.functor.map (β_ b a).hom ≫ F.functor.map (β_ a b).hom = 𝟙 (F.functor.obj (b ⊗ a)) :=
    ((F.functor.map_comp _ _).symm.trans hi).trans (F.functor.map_id _)
  change multiplication F a b ≫ F.functor.map (β_ a b).hom =
    (β_ (F.functor.obj a) (F.functor.obj b)).hom ≫ multiplication F b a
  simpa only [Category.assoc, hi', Category.comp_id] using h.symm

end Monoid



end CategoryTheory.MonoidalCategory.DayFunctor
