/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.DayFunctorClosedSymmetric
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.InternalHomSource

/-!
# End projections and generators for Day convolution

Under the pointwise Kan-extension, tensor-preservation, and end hypotheses
for closed Day convolution, each projection of coevaluation or curry is the
base-category curry of a Day convolution generator. The inverse Day
associator is computed on nested generators using the coefficient and
index associators. In braided base and index categories, the braiding
formula includes both the coefficient swap and the reversed index braiding.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uI vI uV vV
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed ExternalProduct

namespace NativeOmegaPreparation.DayClosedProjection
variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  [∀ (F G : I ⥤ V), (tensor I).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ I)).HasPointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorRight v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((𝟭 I).prod (Functor.fromPUnit.{0} (𝟙_ I))) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((tensor I).prod (𝟭 I)) d) (tensorRight v)]
  [∀ (F G : I ⥤ V) (c : I), HasEnd
    ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)]

/-- The actual selected Day closed structure is the original end adjunction, using its original Day
tensor. -/
local instance originalDayClosed : MonoidalClosed (DayFunctor I V) := inferInstance

/-- Every original coevaluation end projection is the transpose of the unchanged actual Day coend
generator. -/
@[reassoc]
theorem coevaluation_π (F G : DayFunctor I V) (c j : I) :
    ((DayFunctor.coevaluation F).app G).natTrans.app c ≫
        end_.π
          ((dayConvolutionInternalHomDiagramFunctor F.functor).obj (F ⊗ G).functor |>.obj c) j =
      MonoidalClosed.curry ((DayFunctor.η F G).app (j, c)) := by
  let _ : DayConvolution F.functor G.functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution I V (DayFunctor I V) F G
  change (DayConvolutionInternalHom.coev_app _).app c ≫ _ =
    MonoidalClosed.curry ((DayConvolution.unit F.functor G.functor).app (j, c))
  exact DayConvolutionInternalHom.coev_app_π _ c j

/-- The original Day curry retains its actual original coend generator at every complete end
projection. -/
@[reassoc]
theorem curry_π (F G N : DayFunctor I V) (q : F ⊗ G ⟶ N) (c j : I) :
    (MonoidalClosed.curry q).natTrans.app c ≫
        end_.π
          ((dayConvolutionInternalHomDiagramFunctor F.functor).obj N.functor |>.obj c) j =
      MonoidalClosed.curry
        ((DayFunctor.η F G).app (j, c) ≫ q.natTrans.app (j ⊗ c)) := by
  let E₀ := end_
    ((dayConvolutionInternalHomDiagramFunctor F.functor).obj (F ⊗ G).functor |>.obj c)
  let E₁ := end_
    ((dayConvolutionInternalHomDiagramFunctor F.functor).obj N.functor |>.obj c)
  let u : G.functor.obj c ⟶ E₀ := ((DayFunctor.coevaluation F).app G).natTrans.app c
  let v : E₀ ⟶ E₁ := ((DayFunctor.internalHom F).map q).natTrans.app c
  let p₀ : E₀ ⟶ (ihom (F.functor.obj j)).obj ((F ⊗ G).functor.obj (j ⊗ c)) :=
    end_.π
      ((dayConvolutionInternalHomDiagramFunctor F.functor).obj (F ⊗ G).functor |>.obj c) j
  let p₁ : E₁ ⟶ (ihom (F.functor.obj j)).obj (N.functor.obj (j ⊗ c)) :=
    end_.π
      ((dayConvolutionInternalHomDiagramFunctor F.functor).obj N.functor |>.obj c) j
  have hv : v ≫ p₁ = p₀ ≫ (ihom (F.functor.obj j)).map (q.natTrans.app (j ⊗ c)) :=
    DayFunctor.internalHomMap F q c j
  have hu : u ≫ p₀ = MonoidalClosed.curry ((DayFunctor.η F G).app (j, c)) :=
    coevaluation_π F G c j
  change (u ≫ v) ≫ p₁ = _
  rw [Category.assoc, hv, ← Category.assoc, hu]
  exact (MonoidalClosed.curry_natural_right _ _).symm

omit [MonoidalClosed V] [∀ (F G : I ⥤ V) (c : I), HasEnd
  ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)] in
/-- The original inverse Day associator retains both nested coend generators and its genuine
original index associator. -/
@[reassoc]
theorem associator_inv_generator (F G H : DayFunctor I V) (x y z : I) :
    (F.functor.obj x ◁ (DayFunctor.η G H).app (y, z)) ≫
        (DayFunctor.η F (G ⊗ H)).app (x, y ⊗ z) ≫
        (α_ F G H).inv.natTrans.app (x ⊗ (y ⊗ z)) =
      (α_ (F.functor.obj x) (G.functor.obj y) (H.functor.obj z)).inv ≫
        ((DayFunctor.η F G).app (x, y) ▷ H.functor.obj z) ≫
        (DayFunctor.η (F ⊗ G) H).app (x ⊗ y, z) ≫
        ((F ⊗ G) ⊗ H).functor.map (α_ x y z).hom := by
  let (P Q : DayFunctor I V) : DayConvolution P.functor Q.functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution I V (DayFunctor I V) P Q
  have h : (DayFunctor.equiv I V).functor.mapIso (α_ F G H) =
      DayConvolution.associator F.functor G.functor H.functor := by
    apply Iso.ext
    exact LawfulDayConvolutionMonoidalCategoryStruct.ι_map_associator_hom_eq_associator_hom
      I V (DayFunctor I V) F G H
  have hi := congrArg Iso.inv h
  change (F.functor.obj x ◁ (DayConvolution.unit G.functor H.functor).app (y, z)) ≫
      (DayConvolution.unit F.functor (G ⊗ H).functor).app (x, y ⊗ z) ≫
        ((DayFunctor.equiv I V).functor.mapIso (α_ F G H)).inv.app (x ⊗ (y ⊗ z)) = _
  rw [hi]
  exact DayConvolution.associator_inv_unit_unit F.functor G.functor H.functor x y z

section Braided
variable [BraidedCategory I] [BraidedCategory V]

omit [MonoidalClosed V] [∀ (F G : I ⥤ V) (c : I), HasEnd
  ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)] in
/-- The original Day braiding preserves the full coefficient braiding and the actual reverse-order
index braiding on every whole coend generator. -/
@[reassoc]
theorem braiding_generator (F G : DayFunctor I V) (x y : I) :
    (DayFunctor.η F G).app (x, y) ≫ (β_ F G).hom.natTrans.app (x ⊗ y) =
      (β_ (F.functor.obj x) (G.functor.obj y)).hom ≫
        (DayFunctor.η G F).app (y, x) ≫ (G ⊗ F).functor.map (β_ y x).hom := by
  let (P Q : DayFunctor I V) : DayConvolution P.functor Q.functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution I V (DayFunctor I V) P Q
  change (DayConvolution.unit F.functor G.functor).app (x, y) ≫
      (DayConvolution.braiding F.functor G.functor).hom.app (x ⊗ y) = _
  exact DayConvolution.unit_app_braiding_hom_app F.functor G.functor x y

end Braided

end NativeOmegaPreparation.DayClosedProjection
