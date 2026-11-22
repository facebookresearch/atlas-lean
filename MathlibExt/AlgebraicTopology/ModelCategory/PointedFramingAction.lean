/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction
public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorialFramings
public meta import Batteries.Tactic.Alias
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import MathlibExt.AlgebraicTopology.ModelCategory.FramingCoefficientFactory
public import MathlibExt.AlgebraicTopology.ModelCategory.FramingHomotopy
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenFrameHomComplex
public import MathlibExt.AlgebraicTopology.ModelCategory.LeftFrameHomWeakEquivalence
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFrameHomComparison
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoHom
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Adjunction.Mates
public import MathlibExt.AlgebraicTopology.ModelCategory.Under
public import MathlibExt.CategoryTheory.Functor.FramingEvaluation
public import MathlibExt.CategoryTheory.Reedy.FactorizationCorners
public import MathlibExt.CategoryTheory.Reedy.DegreeZero
public import MathlibExt.CategoryTheory.Reedy.Corner
public import MathlibExt.CategoryTheory.Monoidal.Pointed.Smash
public import Mathlib.CategoryTheory.Localization.Bifunctor
public import MathlibExt.AlgebraicTopology.ModelCategory.PointedSmash
public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.CartesianMonoidalModel
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic

public import Mathlib.CategoryTheory.Limits.Presheaf
public import MathlibExt.AlgebraicTopology.ModelCategory.CompatibleCotensorFraming
import all MathlibExt.AlgebraicTopology.ModelCategory.FiniteResolutionTensor
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.End
public import Mathlib.CategoryTheory.Monoidal.Action.End
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
/-!
# Pointed framing from the actual functorial factories

The ordinary functorial factors construct actual cosimplicial and simplicial
frames in every model category. The degree zero maps, all original Q/R arrows,
all latching and matching maps, and the two entire functor variables remain
explicit. The pointed tensor and cotensor constructions use those frames.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uC vC uA vA uB vB uH1 vH1 uH2 vH2
open CategoryTheory Limits MorphismProperty Simplicial

namespace HomotopicalAlgebra.PointedFramingAction
namespace FrameEndpoints
@[reducible]
alias originalLeft := HomotopicalAlgebra.FunctorialFramings.FrameEndpoints.originalLeft

@[reducible]
alias originalRight := HomotopicalAlgebra.FunctorialFramings.FrameEndpoints.originalRight

alias originalLeft_obj := HomotopicalAlgebra.FunctorialFramings.FrameEndpoints.originalLeft_obj

alias originalLeft_map := HomotopicalAlgebra.FunctorialFramings.FrameEndpoints.originalLeft_map

alias originalRight_obj := HomotopicalAlgebra.FunctorialFramings.FrameEndpoints.originalRight_obj

alias originalRight_map := HomotopicalAlgebra.FunctorialFramings.FrameEndpoints.originalRight_map

@[reducible]
alias originalCosimplicialFold := HomotopicalAlgebra.FunctorialFramings.FrameEndpoints.originalCosimplicialFold

@[reducible]
alias originalSimplicialDiagonal := HomotopicalAlgebra.FunctorialFramings.FrameEndpoints.originalSimplicialDiagonal

@[reducible]
alias originalLeftZeroIso := HomotopicalAlgebra.FunctorialFramings.FrameEndpoints.originalLeftZeroIso

@[reducible]
alias originalRightZeroIso := HomotopicalAlgebra.FunctorialFramings.FrameEndpoints.originalRightZeroIso

alias originalLeftZeroIso_hom := HomotopicalAlgebra.FunctorialFramings.FrameEndpoints.originalLeftZeroIso_hom

alias originalRightZeroIso_inv := HomotopicalAlgebra.FunctorialFramings.FrameEndpoints.originalRightZeroIso_inv

end FrameEndpoints

@[reducible]
alias leftEndpointArrow := HomotopicalAlgebra.FunctorialFramings.leftEndpointArrow

@[reducible]
alias rightEndpointArrow := HomotopicalAlgebra.FunctorialFramings.rightEndpointArrow

@[reducible]
alias leftFactor := HomotopicalAlgebra.FunctorialFramings.leftFactor

@[reducible]
alias rightFactor := HomotopicalAlgebra.FunctorialFramings.rightFactor

@[reducible]
alias leftFrame := HomotopicalAlgebra.FunctorialFramings.leftFrame

@[reducible]
alias rightFrame := HomotopicalAlgebra.FunctorialFramings.rightFrame

@[reducible]
alias fromLeftFree := HomotopicalAlgebra.FunctorialFramings.fromLeftFree

@[reducible]
alias leftResolution := HomotopicalAlgebra.FunctorialFramings.leftResolution

@[reducible]
alias rightResolution := HomotopicalAlgebra.FunctorialFramings.rightResolution

@[reducible]
alias toRightFree := HomotopicalAlgebra.FunctorialFramings.toRightFree

alias left_fac := HomotopicalAlgebra.FunctorialFramings.left_fac

alias right_fac := HomotopicalAlgebra.FunctorialFramings.right_fac

alias leftEndpointArrow_zero_isIso := HomotopicalAlgebra.FunctorialFramings.leftEndpointArrow_zero_isIso

alias rightEndpointArrow_zero_isIso := HomotopicalAlgebra.FunctorialFramings.rightEndpointArrow_zero_isIso

alias leftFactor_zero_p_isIso := HomotopicalAlgebra.FunctorialFramings.leftFactor_zero_p_isIso

alias rightFactor_zero_i_isIso := HomotopicalAlgebra.FunctorialFramings.rightFactor_zero_i_isIso

@[reducible]
alias leftZeroIso := HomotopicalAlgebra.FunctorialFramings.leftZeroIso

@[reducible]
alias rightZeroIso := HomotopicalAlgebra.FunctorialFramings.rightZeroIso

alias leftZeroIso_hom := HomotopicalAlgebra.FunctorialFramings.leftZeroIso_hom

alias rightZeroIso_hom := HomotopicalAlgebra.FunctorialFramings.rightZeroIso_hom

@[reducible]
alias augmentation := HomotopicalAlgebra.FunctorialFramings.augmentation

@[reducible]
alias coaugmentation := HomotopicalAlgebra.FunctorialFramings.coaugmentation

alias augmentation_app := HomotopicalAlgebra.FunctorialFramings.augmentation_app

alias coaugmentation_app := HomotopicalAlgebra.FunctorialFramings.coaugmentation_app

alias augmentation_zero := HomotopicalAlgebra.FunctorialFramings.augmentation_zero

alias coaugmentation_zero := HomotopicalAlgebra.FunctorialFramings.coaugmentation_zero

alias leftResolution_trivialFibration := HomotopicalAlgebra.FunctorialFramings.leftResolution_trivialFibration

alias rightResolution_trivialCofibration := HomotopicalAlgebra.FunctorialFramings.rightResolution_trivialCofibration

alias leftResolution_weak := HomotopicalAlgebra.FunctorialFramings.leftResolution_weak

alias rightResolution_weak := HomotopicalAlgebra.FunctorialFramings.rightResolution_weak

alias augmentation_weak := HomotopicalAlgebra.FunctorialFramings.augmentation_weak

alias coaugmentation_weak := HomotopicalAlgebra.FunctorialFramings.coaugmentation_weak

alias leftFrame_map_weak := HomotopicalAlgebra.FunctorialFramings.leftFrame_map_weak

alias rightFrame_map_weak := HomotopicalAlgebra.FunctorialFramings.rightFrame_map_weak

alias leftFrame_zero_isCofibrant := HomotopicalAlgebra.FunctorialFramings.leftFrame_zero_isCofibrant

alias rightFrame_zero_isFibrant := HomotopicalAlgebra.FunctorialFramings.rightFrame_zero_isFibrant

alias leftFrame_latching_zero := HomotopicalAlgebra.FunctorialFramings.leftFrame_latching_zero

alias rightFrame_matching_zero := HomotopicalAlgebra.FunctorialFramings.rightFrame_matching_zero

alias leftFrame_latching_positive := HomotopicalAlgebra.FunctorialFramings.leftFrame_latching_positive

alias rightFrame_matching_positive := HomotopicalAlgebra.FunctorialFramings.rightFrame_matching_positive

alias leftFrame_latching_cofibration := HomotopicalAlgebra.FunctorialFramings.leftFrame_latching_cofibration

alias rightFrame_matching_fibration := HomotopicalAlgebra.FunctorialFramings.rightFrame_matching_fibration

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

section TensorConstruction

variable {C : Type uC} [Category.{vC} C]

/-- The entire simplex diagram of a simplicial weight with its actual coefficient objects. -/
def tensorDiagram (A : CosimplicialObject C) (K : SSet.{vC}) : K.Elementsᵒᵖ ⥤ C where
  obj e := A.obj e.unop.obj.unop
  map f := A.map f.unop.hom.unop
  map_id _ := by simp
  map_comp _ _ := by simp

variable [HasColimitsOfSize.{0, vC} C]

/-- The actual tensor with any simplicial set is the colimit of its full simplex diagram. -/
def tensor (A : CosimplicialObject C) (K : SSet.{vC}) : C := colimit (tensorDiagram A K)

/-- Every original simplex has its actual coefficient injection into the entire tensor. -/
def tensorInjection (A : CosimplicialObject C) (K : SSet.{vC})
    (n : SimplexCategoryᵒᵖ) (x : K.obj n) : A.obj n.unop ⟶ tensor A K :=
  colimit.ι (tensorDiagram A K) (Opposite.op (K.elementsMk n x))

/-- The actual entire simplex cocone is colimiting. -/
def tensorIsColimit (A : CosimplicialObject C) (K : SSet.{vC}) :
    IsColimit (colimit.cocone (tensorDiagram A K)) := colimit.isColimit _

/-- Every original weight operator gives the actual coefficient-injection square. -/
theorem tensorInjection_map (A : CosimplicialObject C) (K : SSet.{vC})
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : K.obj n) :
    A.map f.unop ≫ tensorInjection A K n x = tensorInjection A K m (K.map f x) := by
  exact colimit.w (tensorDiagram A K)
    ((Functor.Elements.homMk (x := K.elementsMk n x)
      (y := K.elementsMk m (K.map f x)) f rfl).op)

/-- A full coefficient map and weight map give their actual cocone on every original simplex. -/
def tensorMapCocone {A A' : CosimplicialObject C} (a : A ⟶ A')
    {K L : SSet.{vC}} (k : K ⟶ L) : Cocone (tensorDiagram A K) where
  pt := tensor A' L
  ι :=
    { app e := a.app e.unop.obj.unop ≫ tensorInjection A' L e.unop.obj (k.app _ e.unop.val)
      naturality {e e'} f := by
        change A.map f.unop.hom.unop ≫
            (a.app e'.unop.obj.unop ≫ tensorInjection A' L e'.unop.obj
              (k.app _ e'.unop.val)) =
          (a.app e.unop.obj.unop ≫ tensorInjection A' L e.unop.obj
              (k.app _ e.unop.val)) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, a.naturality, Category.assoc]
        have h := tensorInjection_map A' L f.unop.hom (k.app _ e'.unop.val)
        rw [← k.naturality_apply, f.unop.map_val] at h
        rw [h] }

/-- The whole tensor map is obtained from the actual colimit universal property. -/
def tensorMap {A A' : CosimplicialObject C} (a : A ⟶ A')
    {K L : SSet.{vC}} (k : K ⟶ L) : tensor A K ⟶ tensor A' L :=
  colimit.desc (tensorDiagram A K) (tensorMapCocone a k)

/-- Every original coefficient map and weight value read back at its original injection. -/
@[reassoc (attr := simp)]
theorem tensorInjection_tensorMap {A A' : CosimplicialObject C} (a : A ⟶ A')
    {K L : SSet.{vC}} (k : K ⟶ L) (n : SimplexCategoryᵒᵖ) (x : K.obj n) :
    tensorInjection A K n x ≫ tensorMap a k =
      a.app n.unop ≫ tensorInjection A' L n (k.app n x) :=
  colimit.ι_desc _ _

/-- Every original tensor morphism is determined by all of its actual simplex injections. -/
theorem tensor_hom_ext (A : CosimplicialObject C) (K : SSet.{vC}) {Y : C}
    (f g : tensor A K ⟶ Y)
    (h : ∀ (n : SimplexCategoryᵒᵖ) (x : K.obj n),
      tensorInjection A K n x ≫ f = tensorInjection A K n x ≫ g) : f = g := by
  apply colimit.hom_ext
  intro e
  exact h e.unop.obj e.unop.val

/-- The whole tensor map preserves both original identity functions. -/
@[simp]
theorem tensorMap_id (A : CosimplicialObject C) (K : SSet.{vC}) :
    tensorMap (𝟙 A) (𝟙 K) = 𝟙 (tensor A K) := by
  apply tensor_hom_ext A K
  intro n x
  simp

/-- The whole tensor map preserves composition in both original variables. -/
@[simp]
theorem tensorMap_comp {A A' A'' : CosimplicialObject C} (a : A ⟶ A') (b : A' ⟶ A'')
    {K L M : SSet.{vC}} (k : K ⟶ L) (l : L ⟶ M) :
    tensorMap (a ≫ b) (k ≫ l) = tensorMap a k ≫ tensorMap b l := by
  apply tensor_hom_ext A K
  intro n x
  simp [Category.assoc]

/-- Full tensoring as a bifunctor of the actual cosimplicial object and simplicial set. -/
def tensorBifunctor : CosimplicialObject C ⥤ SSet.{vC} ⥤ C where
  obj A :=
    { obj K := tensor A K
      map k := tensorMap (𝟙 A) k
      map_id K := tensorMap_id A K
      map_comp k l := by simpa using tensorMap_comp (𝟙 A) (𝟙 A) k l }
  map a :=
    { app K := tensorMap a (𝟙 K)
      naturality {_ _} k := by
        rw [← tensorMap_comp, ← tensorMap_comp]
        simp }
  map_id A := by ext K; exact tensorMap_id A K
  map_comp a b := by
    ext K
    simpa using tensorMap_comp a b (𝟙 K) (𝟙 K)

/-- The entire forward tensor--Hom function retains every original simplex injection. -/
def tensorHomForward (A : CosimplicialObject C) (K : SSet.{vC}) (Y : C)
    (f : tensor A K ⟶ Y) : K ⟶ ResolutionHomComplex.left A Y where
  app n := ↾fun x => tensorInjection A K n x ≫ f
  naturality {n m} a := by
    ext x
    change tensorInjection A K m (K.map a x) ≫ f =
      (ResolutionHomComplex.left A Y).map a (tensorInjection A K n x ≫ f)
    rw [ResolutionHomComplex.left_map_apply, ← Category.assoc, tensorInjection_map]

/-- Every actual simplicial Hom map supplies the full original coefficient cocone. -/
def tensorHomCocone (A : CosimplicialObject C) (K : SSet.{vC}) (Y : C)
    (g : K ⟶ ResolutionHomComplex.left A Y) : Cocone (tensorDiagram A K) where
  pt := Y
  ι :=
    { app e := g.app e.unop.obj e.unop.val
      naturality {e e'} f := by
        change A.map f.unop.hom.unop ≫ g.app e'.unop.obj e'.unop.val =
          g.app e.unop.obj e.unop.val ≫ 𝟙 Y
        have hv := congrArg (fun x => g.app e.unop.obj x) f.unop.map_val
        have hn := g.naturality_apply f.unop.hom e'.unop.val
        have hm := ResolutionHomComplex.left_map_apply (C := C) A Y f.unop.hom
          (g.app e'.unop.obj e'.unop.val)
        exact ((hv.symm.trans hn).trans hm).symm.trans (Category.comp_id _).symm }

/-- The entire inverse tensor--Hom function is the actual colimit desc of the given map. -/
def tensorHomBackward (A : CosimplicialObject C) (K : SSet.{vC}) (Y : C)
    (g : K ⟶ ResolutionHomComplex.left A Y) : tensor A K ⟶ Y :=
  colimit.desc (tensorDiagram A K) (tensorHomCocone A K Y g)

/-- Every original simplex reads back from the inverse's actual injection. -/
@[reassoc (attr := simp)]
theorem tensorHomBackward_injection (A : CosimplicialObject C) (K : SSet.{vC}) (Y : C)
    (g : K ⟶ ResolutionHomComplex.left A Y) (n : SimplexCategoryᵒᵖ) (x : K.obj n) :
    tensorInjection A K n x ≫ tensorHomBackward A K Y g = g.app n x := colimit.ι_desc _ _

/-- The two complete tensor--Hom functions form the actual adjunction equivalence. -/
def tensorHomEquiv (A : CosimplicialObject C) (K : SSet.{vC}) (Y : C) :
    (tensor A K ⟶ Y) ≃ (K ⟶ ResolutionHomComplex.left A Y) where
  toFun := tensorHomForward A K Y
  invFun := tensorHomBackward A K Y
  left_inv f := by
    apply tensor_hom_ext A K
    intro n x
    rw [tensorHomBackward_injection]
    rfl
  right_inv g := by
    ext n x
    exact tensorHomBackward_injection A K Y g n x

/-- Both tensor--Hom functions keep every actual coefficient map. -/
theorem tensorHomEquiv_source {A A' : CosimplicialObject C} (a : A ⟶ A')
    (K : SSet.{vC}) (Y : C) (f : tensor A' K ⟶ Y) :
    tensorHomEquiv A K Y (tensorMap a (𝟙 K) ≫ f) =
      tensorHomEquiv A' K Y f ≫
        ResolutionHomComplex.precomp a ((SimplicialObject.const C).obj Y) := by
  ext n x
  change tensorInjection A K n x ≫ (tensorMap a (𝟙 K) ≫ f) =
    a.app n.unop ≫ (tensorInjection A' K n x ≫ f)
  rw [← Category.assoc, tensorInjection_tensorMap]
  simp [Category.assoc]

/-- The forward tensor--Hom function retains every original simplicial parameter map. -/
theorem tensorHomEquiv_parameter (A : CosimplicialObject C)
    {K L : SSet.{vC}} (k : K ⟶ L) (Y : C) (f : tensor A L ⟶ Y) :
    tensorHomEquiv A K Y (tensorMap (𝟙 A) k ≫ f) = k ≫ tensorHomEquiv A L Y f := by
  ext n x
  change tensorInjection A K n x ≫ (tensorMap (𝟙 A) k ≫ f) =
    tensorInjection A L n (k.app n x) ≫ f
  rw [← Category.assoc, tensorInjection_tensorMap]
  simp

/-- The forward tensor--Hom function retains every original target morphism. -/
theorem tensorHomEquiv_target (A : CosimplicialObject C) (K : SSet.{vC})
    {Y Y' : C} (p : Y ⟶ Y') (f : tensor A K ⟶ Y) :
    tensorHomEquiv A K Y' (f ≫ p) = tensorHomEquiv A K Y f ≫
      ResolutionHomComplex.postcomp A ((SimplicialObject.const C).map p) := by
  ext n x
  change tensorInjection A K n x ≫ (f ≫ p) = (tensorInjection A K n x ≫ f) ≫ p
  exact (Category.assoc _ _ _).symm

/-- The actual full left resolution Hom functor. -/
abbrev leftHomFunctor (A : CosimplicialObject C) : C ⥤ SSet.{vC} where
  obj Y := ResolutionHomComplex.left A Y
  map p := ResolutionHomComplex.postcomp A ((SimplicialObject.const C).map p)
  map_id _ := by simp
  map_comp _ _ := by simp

/-- Tensoring with the entire original cosimplicial object is actually left adjoint to its resolution Hom. -/
def tensorHomAdjunction (A : CosimplicialObject C) : tensorBifunctor.obj A ⊣ leftHomFunctor A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv A
      homEquiv_naturality_left_symm := by
        intro K L Y k g
        change (tensorHomEquiv A K Y).symm (k ≫ g) =
          tensorMap (𝟙 A) k ≫ (tensorHomEquiv A L Y).symm g
        apply (tensorHomEquiv A K Y).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_parameter, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro K Y Y' f p
        exact tensorHomEquiv_target A K p f }

end TensorConstruction

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

section CotensorConstruction

variable {C : Type uC} [Category.{vC} C]

/-- The actual complete simplex diagram whose limit is the cotensor. -/
def cotensorDiagram (B : SimplicialObject C) (K : SSet.{vC}) : K.Elements ⥤ C :=
  Functor.Elements.π K ⋙ B

variable [HasLimitsOfSize.{0, vC} C]

/-- Cotensoring with an arbitrary actual simplicial weight uses its entire simplex limit. -/
def cotensor (B : SimplicialObject C) (K : SSet.{vC}) : C := limit (cotensorDiagram B K)

/-- Every original weight simplex has its actual cotensor coefficient projection. -/
def cotensorProjection (B : SimplicialObject C) (K : SSet.{vC})
    (n : SimplexCategoryᵒᵖ) (x : K.obj n) : cotensor B K ⟶ B.obj n :=
  limit.π (cotensorDiagram B K) (K.elementsMk n x)

/-- The actual full simplex cone is limiting. -/
def cotensorIsLimit (B : SimplicialObject C) (K : SSet.{vC}) :
    IsLimit (limit.cone (cotensorDiagram B K)) := limit.isLimit _

/-- Every original weight operator retains its actual coefficient-projection triangle. -/
theorem cotensorProjection_map (B : SimplicialObject C) (K : SSet.{vC})
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : K.obj n) :
    cotensorProjection B K n x ≫ B.map f = cotensorProjection B K m (K.map f x) :=
  limit.w (cotensorDiagram B K)
    (Functor.Elements.homMk (x := K.elementsMk n x)
      (y := K.elementsMk m (K.map f x)) f rfl)

/-- The entire actual cone for a coefficient map and original weight restriction. -/
def cotensorMapCone {B B' : SimplicialObject C} (b : B ⟶ B')
    {K L : SSet.{vC}} (k : K ⟶ L) : Cone (cotensorDiagram B' K) where
  pt := cotensor B L
  π :=
    { app e := cotensorProjection B L e.obj (k.app _ e.val) ≫ b.app e.obj
      naturality {e e'} f := by
        change 𝟙 _ ≫ (cotensorProjection B L e'.obj (k.app _ e'.val) ≫ b.app e'.obj) =
          (cotensorProjection B L e.obj (k.app _ e.val) ≫ b.app e.obj) ≫ B'.map f.hom
        rw [Category.id_comp]
        have h := cotensorProjection_map B L f.hom (k.app e.obj e.val)
        rw [← k.naturality_apply, f.map_val] at h
        rw [← h, Category.assoc, b.naturality, Category.assoc] }

/-- The entire cotensor map is the actual limit lift of its original cone. -/
def cotensorMap {B B' : SimplicialObject C} (b : B ⟶ B')
    {K L : SSet.{vC}} (k : K ⟶ L) : cotensor B L ⟶ cotensor B' K :=
  limit.lift (cotensorDiagram B' K) (cotensorMapCone b k)

/-- Every original weight restriction and coefficient map read back at the actual projection. -/
@[reassoc (attr := simp)]
theorem cotensorMap_projection {B B' : SimplicialObject C} (b : B ⟶ B')
    {K L : SSet.{vC}} (k : K ⟶ L) (n : SimplexCategoryᵒᵖ) (x : K.obj n) :
    cotensorMap b k ≫ cotensorProjection B' K n x =
      cotensorProjection B L n (k.app n x) ≫ b.app n := limit.lift_π _ _

/-- Actual cotensor maps are determined by all of their original simplex projections. -/
theorem cotensor_hom_ext (B : SimplicialObject C) (K : SSet.{vC}) {X : C}
    (f g : X ⟶ cotensor B K)
    (h : ∀ (n : SimplexCategoryᵒᵖ) (x : K.obj n),
      f ≫ cotensorProjection B K n x = g ≫ cotensorProjection B K n x) : f = g := by
  apply limit.hom_ext
  intro e
  exact h e.obj e.val

/-- Both original identity maps are retained by the whole cotensor. -/
@[simp]
theorem cotensorMap_id (B : SimplicialObject C) (K : SSet.{vC}) :
    cotensorMap (𝟙 B) (𝟙 K) = 𝟙 (cotensor B K) := by
  apply cotensor_hom_ext B K
  intro n x
  simp

/-- Coefficient composition is covariant and the actual weight composition is contravariant. -/
@[simp]
theorem cotensorMap_comp {B B' B'' : SimplicialObject C} (b : B ⟶ B') (c : B' ⟶ B'')
    {K L M : SSet.{vC}} (k : K ⟶ L) (l : L ⟶ M) :
    cotensorMap (b ≫ c) (k ≫ l) = cotensorMap b l ≫ cotensorMap c k := by
  apply cotensor_hom_ext B'' K
  intro n x
  simp [Category.assoc]

/-- The whole cotensor bifunctor retains the actual weight and coefficient functions. -/
def cotensorBifunctor : SSet.{vC}ᵒᵖ ⥤ SimplicialObject C ⥤ C where
  obj K :=
    { obj B := cotensor B K.unop
      map b := cotensorMap b (𝟙 K.unop)
      map_id B := cotensorMap_id B K.unop
      map_comp b c := by simpa using cotensorMap_comp b c (𝟙 K.unop) (𝟙 K.unop) }
  map k :=
    { app B := cotensorMap (𝟙 B) k.unop
      naturality {_ _} b := by
        rw [← cotensorMap_comp, ← cotensorMap_comp]
        simp }
  map_id K := by ext B; exact cotensorMap_id B K.unop
  map_comp k l := by
    ext B
    simpa using cotensorMap_comp (𝟙 B) (𝟙 B) l.unop k.unop

/-- The actual cotensor--Hom forward function retains every original simplex projection. -/
def cotensorHomForward (X : C) (K : SSet.{vC}) (B : SimplicialObject C)
    (f : X ⟶ cotensor B K) : K ⟶ ResolutionHomComplex.right X B where
  app n := ↾fun x => f ≫ cotensorProjection B K n x
  naturality {n m} a := by
    ext x
    change f ≫ cotensorProjection B K m (K.map a x) =
      (ResolutionHomComplex.right X B).map a (f ≫ cotensorProjection B K n x)
    rw [ResolutionHomComplex.right_map_apply, Category.assoc, cotensorProjection_map]

/-- Every entire simplicial Hom map gives its full original coefficient cone. -/
def cotensorHomCone (X : C) (K : SSet.{vC}) (B : SimplicialObject C)
    (g : K ⟶ ResolutionHomComplex.right X B) : Cone (cotensorDiagram B K) where
  pt := X
  π :=
    { app e := g.app e.obj e.val
      naturality {e e'} f := by
        change 𝟙 X ≫ g.app e'.obj e'.val = g.app e.obj e.val ≫ B.map f.hom
        have hv := congrArg (fun x => g.app e'.obj x) f.map_val
        have hn := g.naturality_apply f.hom e.val
        have hm := ResolutionHomComplex.right_map_apply (C := C) X B f.hom (g.app e.obj e.val)
        exact (Category.id_comp _).trans ((hv.symm.trans hn).trans hm) }

/-- The entire inverse cotensor--Hom function is the actual limit lift. -/
def cotensorHomBackward (X : C) (K : SSet.{vC}) (B : SimplicialObject C)
    (g : K ⟶ ResolutionHomComplex.right X B) : X ⟶ cotensor B K :=
  limit.lift (cotensorDiagram B K) (cotensorHomCone X K B g)

/-- Every original coordinate reads back from the inverse's whole limit lift. -/
@[reassoc (attr := simp)]
theorem cotensorHomBackward_projection (X : C) (K : SSet.{vC}) (B : SimplicialObject C)
    (g : K ⟶ ResolutionHomComplex.right X B) (n : SimplexCategoryᵒᵖ) (x : K.obj n) :
    cotensorHomBackward X K B g ≫ cotensorProjection B K n x = g.app n x := limit.lift_π _ _

/-- The entire full cotensor--Hom equivalence comes from the original limit universal property. -/
def cotensorHomEquiv (X : C) (K : SSet.{vC}) (B : SimplicialObject C) :
    (X ⟶ cotensor B K) ≃ (K ⟶ ResolutionHomComplex.right X B) where
  toFun := cotensorHomForward X K B
  invFun := cotensorHomBackward X K B
  left_inv f := by
    apply cotensor_hom_ext B K
    intro n x
    rw [cotensorHomBackward_projection]
    rfl
  right_inv g := by
    ext n x
    exact cotensorHomBackward_projection X K B g n x

/-- The full cotensor--Hom equivalence retains every original source arrow. -/
theorem cotensorHomEquiv_source {X X' : C} (a : X ⟶ X') (K : SSet.{vC})
    (B : SimplicialObject C) (f : X' ⟶ cotensor B K) :
    cotensorHomEquiv X K B (a ≫ f) = cotensorHomEquiv X' K B f ≫
      ResolutionHomComplex.precomp ((CosimplicialObject.const C).map a) B := by
  ext n x
  change (a ≫ f) ≫ cotensorProjection B K n x = a ≫ (f ≫ cotensorProjection B K n x)
  exact Category.assoc _ _ _

/-- Every original weight map becomes the same original simplicial precomposition. -/
theorem cotensorHomEquiv_parameter (X : C) {K L : SSet.{vC}} (k : K ⟶ L)
    (B : SimplicialObject C) (f : X ⟶ cotensor B L) :
    cotensorHomEquiv X K B (f ≫ cotensorMap (𝟙 B) k) = k ≫ cotensorHomEquiv X L B f := by
  ext n x
  change (f ≫ cotensorMap (𝟙 B) k) ≫ cotensorProjection B K n x =
    f ≫ cotensorProjection B L n (k.app n x)
  rw [Category.assoc, cotensorMap_projection]
  simp

/-- Every original coefficient map remains the same actual Hom postcomposition. -/
theorem cotensorHomEquiv_target (X : C) (K : SSet.{vC})
    {B B' : SimplicialObject C} (b : B ⟶ B') (f : X ⟶ cotensor B K) :
    cotensorHomEquiv X K B' (f ≫ cotensorMap b (𝟙 K)) =
      cotensorHomEquiv X K B f ≫ ResolutionHomComplex.postcomp ((CosimplicialObject.const C).obj X) b := by
  ext n x
  change (f ≫ cotensorMap b (𝟙 K)) ≫ cotensorProjection B' K n x =
    (f ≫ cotensorProjection B K n x) ≫ b.app n
  rw [Category.assoc, cotensorMap_projection]
  simp [Category.assoc]

end CotensorConstruction

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

/-- Pointed simplicial sets on the canonical standard zero-simplex Under carrier. -/
abbrev PointedSSet := Under (Δ[0] : SSet.{vC})

section PointedHom

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C]
/-- The same original zero object supplies the coefficient zero maps. -/
local instance coefficientZeroMorphisms1 : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject
open scoped ZeroObject

/-- The actual zero maps give the basepoint of the entire resolution Hom complex. -/
def zeroBasepoint (A : CosimplicialObject C) (B : SimplicialObject C) :
    (Δ[0] : SSet.{vC}) ⟶ ResolutionHomComplex.obj A B where
  app n := ↾fun _ => (0 : A.obj n.unop ⟶ B.obj n)
  naturality {n m} f := by
    ext x
    change (0 : A.obj m.unop ⟶ B.obj m) = A.map f.unop ≫ 0 ≫ B.map f
    simp

/-- The full pointed resolution Hom retains the original zero map in every degree. -/
abbrev pointedHom (A : CosimplicialObject C) (B : SimplicialObject C) : PointedSSet.{vC} :=
  Under.mk (zeroBasepoint A B)

/-- Actual source precomposition preserves the same original zero basepoint. -/
def pointedHomPrecomp {A A' : CosimplicialObject C} (a : A ⟶ A') (B : SimplicialObject C) :
    pointedHom A' B ⟶ pointedHom A B :=
  Under.homMk (ResolutionHomComplex.precomp a B) (by
    ext n x
    change a.app n.unop ≫ (0 : A'.obj n.unop ⟶ B.obj n) = 0
    simp)

/-- Actual target postcomposition preserves the same original zero basepoint. -/
def pointedHomPostcomp (A : CosimplicialObject C) {B B' : SimplicialObject C} (b : B ⟶ B') :
    pointedHom A B ⟶ pointedHom A B' :=
  Under.homMk (ResolutionHomComplex.postcomp A b) (by
    ext n x
    change (0 : A.obj n.unop ⟶ B.obj n) ≫ b.app n = 0
    simp)

/-- Pointed source maps retain the whole actual underlying resolution precomposition. -/
theorem pointedHomPrecomp_right {A A' : CosimplicialObject C} (a : A ⟶ A') (B : SimplicialObject C) :
    (pointedHomPrecomp a B).right = ResolutionHomComplex.precomp a B := rfl

/-- Pointed target maps retain the whole actual underlying resolution postcomposition. -/
theorem pointedHomPostcomp_right (A : CosimplicialObject C) {B B' : SimplicialObject C} (b : B ⟶ B') :
    (pointedHomPostcomp A b).right = ResolutionHomComplex.postcomp A b := rfl

/-- The original pointed left resolution Hom. -/
abbrev pointedLeftHom (A : CosimplicialObject C) (Y : C) : PointedSSet.{vC} :=
  pointedHom A ((SimplicialObject.const C).obj Y)

/-- The original pointed right resolution Hom. -/
abbrev pointedRightHom (X : C) (B : SimplicialObject C) : PointedSSet.{vC} :=
  pointedHom ((CosimplicialObject.const C).obj X) B

end PointedHom

section PointedTensor

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C]
  [HasColimitsOfSize.{0, vC} C] [HasPushouts C]
/-- The same original zero object supplies the coefficient zero maps. -/
local instance coefficientZeroMorphisms2 : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject
open scoped ZeroObject

/-- The full pointed tensor is the actual cofiber of the original basepoint tensor arrow. -/
abbrev pointedTensor (A : CosimplicialObject C) (K : PointedSSet.{vC}) : C :=
  pushout (tensorMap (𝟙 A) K.hom) (0 : tensor A (Δ[0] : SSet.{vC}) ⟶ (0 : C))

/-- The actual quotient map from the full original unpointed tensor. -/
def pointedTensorQuotient (A : CosimplicialObject C) (K : PointedSSet.{vC}) :
    tensor A K.right ⟶ pointedTensor A K := pushout.inl _ _

/-- The other original cofiber leg is the actual zero-object injection. -/
def pointedTensorZeroLeg (A : CosimplicialObject C) (K : PointedSSet.{vC}) :
    (0 : C) ⟶ pointedTensor A K := pushout.inr _ _

/-- The actual basepoint tensor arrow is killed by the original quotient map. -/
@[reassoc (attr := simp)]
theorem pointedTensor_basepoint (A : CosimplicialObject C) (K : PointedSSet.{vC}) :
    tensorMap (𝟙 A) K.hom ≫ pointedTensorQuotient A K = 0 := by
  exact (pushout.condition (f := tensorMap (𝟙 A) K.hom)
    (g := (0 : tensor A (Δ[0] : SSet.{vC}) ⟶ (0 : C)))).trans (zero_comp)

omit [HasPushouts C] in
/-- The full unpointed Hom function on the original zero map is the actual zero basepoint. -/
theorem tensorHomEquiv_zero (A : CosimplicialObject C) (Y : C) :
    tensorHomEquiv A (Δ[0] : SSet.{vC}) Y (0 : tensor A (Δ[0] : SSet.{vC}) ⟶ Y) =
      zeroBasepoint A ((SimplicialObject.const C).obj Y) := by
  ext n x
  change tensorInjection A (Δ[0] : SSet.{vC}) n x ≫ (0 : tensor A (Δ[0] : SSet.{vC}) ⟶ Y) = 0
  simp

/-- The full pointed tensor--Hom function retains the actual quotient map and zero basepoint. -/
def pointedTensorHomForward (A : CosimplicialObject C) (K : PointedSSet.{vC}) (Y : C)
    (f : pointedTensor A K ⟶ Y) : K ⟶ pointedLeftHom A Y :=
  Under.homMk (tensorHomEquiv A K.right Y (pointedTensorQuotient A K ≫ f)) (by
    rw [← tensorHomEquiv_parameter, ← Category.assoc, pointedTensor_basepoint, zero_comp]
    exact tensorHomEquiv_zero A Y)

omit [HasPushouts C] in
/-- A full pointed Hom map annihilates the exact original basepoint tensor arrow. -/
theorem pointedTensorHomBackward_basepoint (A : CosimplicialObject C) (K : PointedSSet.{vC}) (Y : C)
    (g : K ⟶ pointedLeftHom A Y) :
    tensorMap (𝟙 A) K.hom ≫ (tensorHomEquiv A K.right Y).symm g.right = 0 := by
  apply (tensorHomEquiv A (Δ[0] : SSet.{vC}) Y).injective
  rw [tensorHomEquiv_parameter, Equiv.apply_symm_apply, CategoryTheory.Under.w, tensorHomEquiv_zero]
  rfl

/-- The inverse pointed tensor--Hom function is the actual original cofiber desc. -/
def pointedTensorHomBackward (A : CosimplicialObject C) (K : PointedSSet.{vC}) (Y : C)
    (g : K ⟶ pointedLeftHom A Y) : pointedTensor A K ⟶ Y :=
  pushout.desc (f := tensorMap (𝟙 A) K.hom)
    (g := (0 : tensor A (Δ[0] : SSet.{vC}) ⟶ (0 : C)))
    ((tensorHomEquiv A K.right Y).symm g.right) (0 : (0 : C) ⟶ Y)
    (by simpa using pointedTensorHomBackward_basepoint A K Y g)

/-- The actual quotient leg reads back the entire unpointed inverse Hom map. -/
@[reassoc (attr := simp)]
theorem pointedTensorHomBackward_quotient (A : CosimplicialObject C) (K : PointedSSet.{vC}) (Y : C)
    (g : K ⟶ pointedLeftHom A Y) :
    pointedTensorQuotient A K ≫ pointedTensorHomBackward A K Y g =
      (tensorHomEquiv A K.right Y).symm g.right := pushout.inl_desc _ _ _

/-- The zero-object cofiber leg reads back the same original zero map. -/
@[reassoc (attr := simp)]
theorem pointedTensorHomBackward_zero (A : CosimplicialObject C) (K : PointedSSet.{vC}) (Y : C)
    (g : K ⟶ pointedLeftHom A Y) :
    pointedTensorZeroLeg A K ≫ pointedTensorHomBackward A K Y g = 0 := pushout.inr_desc _ _ _

/-- The full pointed tensor--Hom equivalence is proved from the actual cofiber universal property. -/
def pointedTensorHomEquiv (A : CosimplicialObject C) (K : PointedSSet.{vC}) (Y : C) :
    (pointedTensor A K ⟶ Y) ≃ (K ⟶ pointedLeftHom A Y) where
  toFun := pointedTensorHomForward A K Y
  invFun := pointedTensorHomBackward A K Y
  left_inv f := by
    apply pushout.hom_ext
    · change pointedTensorQuotient A K ≫
          pointedTensorHomBackward A K Y (pointedTensorHomForward A K Y f) =
        pointedTensorQuotient A K ≫ f
      rw [pointedTensorHomBackward_quotient]
      exact (tensorHomEquiv A K.right Y).symm_apply_apply _
    · exact HasZeroObject.zeroIsInitial.hom_ext _ _
  right_inv g := by
    apply Under.UnderMorphism.ext
    change tensorHomEquiv A K.right Y
      (pointedTensorQuotient A K ≫ pointedTensorHomBackward A K Y g) = g.right
    rw [pointedTensorHomBackward_quotient, Equiv.apply_symm_apply]

end PointedTensor

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

section PointedCotensor

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C]
  [HasLimitsOfSize.{0, vC} C] [HasPullbacks C]
/-- The same original zero object supplies the coefficient zero maps. -/
local instance coefficientZeroMorphisms3 : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject
open scoped ZeroObject

/-- The full pointed cotensor is the actual fiber of the original basepoint restriction. -/
abbrev pointedCotensor (B : SimplicialObject C) (K : PointedSSet.{vC}) : C :=
  pullback (cotensorMap (𝟙 B) K.hom) (0 : (0 : C) ⟶ cotensor B (Δ[0] : SSet.{vC}))

/-- The actual full fiber projection into the original unpointed cotensor. -/
def pointedCotensorProjection (B : SimplicialObject C) (K : PointedSSet.{vC}) :
    pointedCotensor B K ⟶ cotensor B K.right := pullback.fst _ _

/-- The other original fiber leg retains the same actual zero object. -/
def pointedCotensorZeroLeg (B : SimplicialObject C) (K : PointedSSet.{vC}) :
    pointedCotensor B K ⟶ (0 : C) := pullback.snd _ _

/-- The actual full fiber projection has zero original basepoint restriction. -/
@[reassoc (attr := simp)]
theorem pointedCotensor_basepoint (B : SimplicialObject C) (K : PointedSSet.{vC}) :
    pointedCotensorProjection B K ≫ cotensorMap (𝟙 B) K.hom = 0 :=
  (pullback.condition (f := cotensorMap (𝟙 B) K.hom)
    (g := (0 : (0 : C) ⟶ cotensor B (Δ[0] : SSet.{vC})))).trans comp_zero

omit [HasPullbacks C] in
/-- The whole cotensor--Hom function on the original zero map is the same zero basepoint. -/
theorem cotensorHomEquiv_zero (X : C) (B : SimplicialObject C) :
    cotensorHomEquiv X (Δ[0] : SSet.{vC}) B (0 : X ⟶ cotensor B (Δ[0] : SSet.{vC})) =
      zeroBasepoint ((CosimplicialObject.const C).obj X) B := by
  ext n x
  change (0 : X ⟶ cotensor B (Δ[0] : SSet.{vC})) ≫ cotensorProjection B (Δ[0] : SSet.{vC}) n x = 0
  simp

/-- The entire pointed cotensor--Hom function uses the actual fiber projection. -/
def pointedCotensorHomForward (X : C) (K : PointedSSet.{vC}) (B : SimplicialObject C)
    (f : X ⟶ pointedCotensor B K) : K ⟶ pointedRightHom X B :=
  Under.homMk (cotensorHomEquiv X K.right B (f ≫ pointedCotensorProjection B K)) (by
    rw [← cotensorHomEquiv_parameter, Category.assoc, pointedCotensor_basepoint, comp_zero]
    exact cotensorHomEquiv_zero X B)

omit [HasPullbacks C] in
/-- Every whole pointed Hom map gives zero actual basepoint restriction of its inverse. -/
theorem pointedCotensorHomBackward_basepoint (X : C) (K : PointedSSet.{vC}) (B : SimplicialObject C)
    (g : K ⟶ pointedRightHom X B) :
    (cotensorHomEquiv X K.right B).symm g.right ≫ cotensorMap (𝟙 B) K.hom = 0 := by
  apply (cotensorHomEquiv X (Δ[0] : SSet.{vC}) B).injective
  rw [cotensorHomEquiv_parameter, Equiv.apply_symm_apply, CategoryTheory.Under.w, cotensorHomEquiv_zero]
  rfl

/-- The inverse whole pointed cotensor--Hom function is the actual original fiber lift. -/
def pointedCotensorHomBackward (X : C) (K : PointedSSet.{vC}) (B : SimplicialObject C)
    (g : K ⟶ pointedRightHom X B) : X ⟶ pointedCotensor B K :=
  pullback.lift (f := cotensorMap (𝟙 B) K.hom)
    (g := (0 : (0 : C) ⟶ cotensor B (Δ[0] : SSet.{vC})))
    ((cotensorHomEquiv X K.right B).symm g.right) (0 : X ⟶ (0 : C))
    (by simpa using pointedCotensorHomBackward_basepoint X K B g)

/-- The actual fiber projection reads back the entire inverse cotensor--Hom map. -/
@[reassoc (attr := simp)]
theorem pointedCotensorHomBackward_projection (X : C) (K : PointedSSet.{vC}) (B : SimplicialObject C)
    (g : K ⟶ pointedRightHom X B) :
    pointedCotensorHomBackward X K B g ≫ pointedCotensorProjection B K =
      (cotensorHomEquiv X K.right B).symm g.right := pullback.lift_fst _ _ _

/-- The actual zero-object projection reads back the same original zero map. -/
@[reassoc (attr := simp)]
theorem pointedCotensorHomBackward_zero (X : C) (K : PointedSSet.{vC}) (B : SimplicialObject C)
    (g : K ⟶ pointedRightHom X B) :
    pointedCotensorHomBackward X K B g ≫ pointedCotensorZeroLeg B K = 0 := pullback.lift_snd _ _ _

/-- The full pointed cotensor--Hom equivalence is derived from the actual fiber universal property. -/
def pointedCotensorHomEquiv (X : C) (K : PointedSSet.{vC}) (B : SimplicialObject C) :
    (X ⟶ pointedCotensor B K) ≃ (K ⟶ pointedRightHom X B) where
  toFun := pointedCotensorHomForward X K B
  invFun := pointedCotensorHomBackward X K B
  left_inv f := by
    apply pullback.hom_ext
    · change pointedCotensorHomBackward X K B (pointedCotensorHomForward X K B f) ≫
          pointedCotensorProjection B K = f ≫ pointedCotensorProjection B K
      rw [pointedCotensorHomBackward_projection]
      exact (cotensorHomEquiv X K.right B).symm_apply_apply _
    · exact HasZeroObject.zeroIsTerminal.hom_ext _ _
  right_inv g := by
    apply Under.UnderMorphism.ext
    change cotensorHomEquiv X K.right B
      (pointedCotensorHomBackward X K B g ≫ pointedCotensorProjection B K) = g.right
    rw [pointedCotensorHomBackward_projection, Equiv.apply_symm_apply]

end PointedCotensor

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

section PointedTensorMaps

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C]
  [HasColimitsOfSize.{0, vC} C] [HasPushouts C]
/-- The same original zero object supplies the coefficient zero maps. -/
local instance coefficientZeroMorphisms4 : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject
open scoped ZeroObject

/-- The actual cofiber map keeps the whole original coefficient and pointed-weight maps. -/
def pointedTensorMap {A A' : CosimplicialObject C} (a : A ⟶ A')
    {K L : PointedSSet.{vC}} (k : K ⟶ L) : pointedTensor A K ⟶ pointedTensor A' L :=
  pushout.map (tensorMap (𝟙 A) K.hom) (0 : tensor A (Δ[0] : SSet.{vC}) ⟶ (0 : C))
    (tensorMap (𝟙 A') L.hom) (0 : tensor A' (Δ[0] : SSet.{vC}) ⟶ (0 : C))
    (tensorMap a k.right) (𝟙 (0 : C)) (tensorMap a (𝟙 (Δ[0] : SSet.{vC})))
    (by rw [← tensorMap_comp, ← tensorMap_comp, CategoryTheory.Under.w]; simp) (by simp)

/-- The original cofiber quotient square retains both complete input maps. -/
@[reassoc (attr := simp)]
theorem pointedTensorMap_quotient {A A' : CosimplicialObject C} (a : A ⟶ A')
    {K L : PointedSSet.{vC}} (k : K ⟶ L) :
    pointedTensorQuotient A K ≫ pointedTensorMap a k =
      tensorMap a k.right ≫ pointedTensorQuotient A' L := pushout.inl_desc _ _ _

/-- The original zero-object leg is retained by the entire cofiber map. -/
@[reassoc (attr := simp)]
theorem pointedTensorMap_zeroLeg {A A' : CosimplicialObject C} (a : A ⟶ A')
    {K L : PointedSSet.{vC}} (k : K ⟶ L) :
    pointedTensorZeroLeg A K ≫ pointedTensorMap a k = pointedTensorZeroLeg A' L := by
  exact (pushout.inr_desc _ _ _).trans (Category.id_comp _)

/-- Every original identity is preserved on the actual complete pointed tensor. -/
@[simp]
theorem pointedTensorMap_id (A : CosimplicialObject C) (K : PointedSSet.{vC}) :
    pointedTensorMap (𝟙 A) (𝟙 K) = 𝟙 (pointedTensor A K) := by
  apply pushout.hom_ext
  · change pointedTensorQuotient A K ≫ pointedTensorMap (𝟙 A) (𝟙 K) =
      pointedTensorQuotient A K ≫ 𝟙 _
    rw [pointedTensorMap_quotient]
    simp
  · exact HasZeroObject.zeroIsInitial.hom_ext _ _

/-- Both actual input compositions are retained by the entire pointed tensor. -/
@[simp]
theorem pointedTensorMap_comp {A A' A'' : CosimplicialObject C} (a : A ⟶ A') (b : A' ⟶ A'')
    {K L M : PointedSSet.{vC}} (k : K ⟶ L) (l : L ⟶ M) :
    pointedTensorMap (a ≫ b) (k ≫ l) = pointedTensorMap a k ≫ pointedTensorMap b l := by
  apply pushout.hom_ext
  · change pointedTensorQuotient A K ≫ pointedTensorMap (a ≫ b) (k ≫ l) =
      pointedTensorQuotient A K ≫ (pointedTensorMap a k ≫ pointedTensorMap b l)
    rw [pointedTensorMap_quotient, ← Category.assoc, pointedTensorMap_quotient,
      Category.assoc, pointedTensorMap_quotient]
    simp [tensorMap_comp, Category.assoc]
  · exact HasZeroObject.zeroIsInitial.hom_ext _ _

/-- The entire actual pointed tensor is a bifunctor on the original two carriers. -/
def pointedTensorBifunctor : CosimplicialObject C ⥤ PointedSSet.{vC} ⥤ C where
  obj A :=
    { obj K := pointedTensor A K
      map k := pointedTensorMap (𝟙 A) k
      map_id K := pointedTensorMap_id A K
      map_comp k l := by simpa using pointedTensorMap_comp (𝟙 A) (𝟙 A) k l }
  map a :=
    { app K := pointedTensorMap a (𝟙 K)
      naturality {_ _} k := by
        rw [← pointedTensorMap_comp, ← pointedTensorMap_comp]
        simp }
  map_id A := by
    apply NatTrans.ext
    funext K
    exact pointedTensorMap_id A K
  map_comp a b := by
    apply NatTrans.ext
    funext K
    simpa using pointedTensorMap_comp a b (𝟙 K) (𝟙 K)

/-- Pointed left resolution Hom retains the whole original target-map functor. -/
abbrev pointedLeftHomFunctor (A : CosimplicialObject C) : C ⥤ PointedSSet.{vC} where
  obj Y := pointedLeftHom A Y
  map p := pointedHomPostcomp A ((SimplicialObject.const C).map p)
  map_id Y := by
    apply Under.UnderMorphism.ext
    exact ResolutionHomComplex.postcomp_id A ((SimplicialObject.const C).obj Y)
  map_comp p q := by
    apply Under.UnderMorphism.ext
    exact (congrArg (ResolutionHomComplex.postcomp A) ((SimplicialObject.const C).map_comp p q)).trans
      (ResolutionHomComplex.postcomp_comp _ _ _)

/-- The whole pointed Hom function retains every actual pointed-weight morphism. -/
theorem pointedTensorHomEquiv_parameter (A : CosimplicialObject C)
    {K L : PointedSSet.{vC}} (k : K ⟶ L) (Y : C) (f : pointedTensor A L ⟶ Y) :
    pointedTensorHomEquiv A K Y (pointedTensorMap (𝟙 A) k ≫ f) =
      k ≫ pointedTensorHomEquiv A L Y f := by
  apply Under.UnderMorphism.ext
  change tensorHomEquiv A K.right Y
      (pointedTensorQuotient A K ≫ (pointedTensorMap (𝟙 A) k ≫ f)) =
    k.right ≫ tensorHomEquiv A L.right Y (pointedTensorQuotient A L ≫ f)
  rw [← Category.assoc, pointedTensorMap_quotient, Category.assoc, tensorHomEquiv_parameter]

/-- Every actual original target morphism stays in the full pointed Hom function. -/
theorem pointedTensorHomEquiv_target (A : CosimplicialObject C) (K : PointedSSet.{vC})
    {Y Y' : C} (p : Y ⟶ Y') (f : pointedTensor A K ⟶ Y) :
    pointedTensorHomEquiv A K Y' (f ≫ p) =
      pointedTensorHomEquiv A K Y f ≫ (pointedLeftHomFunctor A).map p := by
  apply Under.UnderMorphism.ext
  change tensorHomEquiv A K.right Y' (pointedTensorQuotient A K ≫ (f ≫ p)) =
    tensorHomEquiv A K.right Y (pointedTensorQuotient A K ≫ f) ≫
      ResolutionHomComplex.postcomp A ((SimplicialObject.const C).map p)
  rw [← Category.assoc, tensorHomEquiv_target]

/-- The actual full pointed tensor and original pointed resolution Hom form an adjunction. -/
def pointedTensorHomAdjunction (A : CosimplicialObject C) :
    pointedTensorBifunctor.obj A ⊣ pointedLeftHomFunctor A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := pointedTensorHomEquiv A
      homEquiv_naturality_left_symm := by
        intro K L Y k g
        change (pointedTensorHomEquiv A K Y).symm (k ≫ g) =
          pointedTensorMap (𝟙 A) k ≫ (pointedTensorHomEquiv A L Y).symm g
        apply (pointedTensorHomEquiv A K Y).injective
        rw [Equiv.apply_symm_apply, pointedTensorHomEquiv_parameter, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro K Y Y' f p
        exact pointedTensorHomEquiv_target A K p f }

end PointedTensorMaps

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

section PointedCotensorMaps

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C]
  [HasLimitsOfSize.{0, vC} C] [HasPullbacks C]
/-- The same original zero object supplies the coefficient zero maps. -/
local instance coefficientZeroMorphisms5 : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject
open scoped ZeroObject

/-- The actual full fiber map retains its coefficient map and pointed weight restriction. -/
def pointedCotensorMap {B B' : SimplicialObject C} (b : B ⟶ B')
    {K L : PointedSSet.{vC}} (k : K ⟶ L) : pointedCotensor B L ⟶ pointedCotensor B' K :=
  pullback.map (cotensorMap (𝟙 B) L.hom) (0 : (0 : C) ⟶ cotensor B (Δ[0] : SSet.{vC}))
    (cotensorMap (𝟙 B') K.hom) (0 : (0 : C) ⟶ cotensor B' (Δ[0] : SSet.{vC}))
    (cotensorMap b k.right) (𝟙 (0 : C)) (cotensorMap b (𝟙 (Δ[0] : SSet.{vC})))
    (by rw [← cotensorMap_comp, ← cotensorMap_comp, CategoryTheory.Under.w]; simp) (by simp)

/-- The actual full fiber projection square keeps both original maps. -/
@[reassoc (attr := simp)]
theorem pointedCotensorMap_projection {B B' : SimplicialObject C} (b : B ⟶ B')
    {K L : PointedSSet.{vC}} (k : K ⟶ L) :
    pointedCotensorMap b k ≫ pointedCotensorProjection B' K =
      pointedCotensorProjection B L ≫ cotensorMap b k.right := pullback.lift_fst _ _ _

/-- The actual zero-object projection is retained by the whole fiber map. -/
@[reassoc (attr := simp)]
theorem pointedCotensorMap_zeroLeg {B B' : SimplicialObject C} (b : B ⟶ B')
    {K L : PointedSSet.{vC}} (k : K ⟶ L) :
    pointedCotensorMap b k ≫ pointedCotensorZeroLeg B' K = pointedCotensorZeroLeg B L := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- Every original identity is retained by the full pointed cotensor. -/
@[simp]
theorem pointedCotensorMap_id (B : SimplicialObject C) (K : PointedSSet.{vC}) :
    pointedCotensorMap (𝟙 B) (𝟙 K) = 𝟙 (pointedCotensor B K) := by
  apply pullback.hom_ext
  · change pointedCotensorMap (𝟙 B) (𝟙 K) ≫ pointedCotensorProjection B K =
      𝟙 _ ≫ pointedCotensorProjection B K
    rw [pointedCotensorMap_projection]
    simp
  · exact HasZeroObject.zeroIsTerminal.hom_ext _ _

/-- The actual coefficient and reversed scalar compositions are retained by the entire fiber map. -/
@[simp]
theorem pointedCotensorMap_comp {B B' B'' : SimplicialObject C} (b : B ⟶ B') (c : B' ⟶ B'')
    {K L M : PointedSSet.{vC}} (k : K ⟶ L) (l : L ⟶ M) :
    pointedCotensorMap (b ≫ c) (k ≫ l) = pointedCotensorMap b l ≫ pointedCotensorMap c k := by
  apply pullback.hom_ext
  · change pointedCotensorMap (b ≫ c) (k ≫ l) ≫ pointedCotensorProjection B'' K =
      (pointedCotensorMap b l ≫ pointedCotensorMap c k) ≫ pointedCotensorProjection B'' K
    rw [pointedCotensorMap_projection, Category.assoc, pointedCotensorMap_projection,
      ← Category.assoc, pointedCotensorMap_projection]
    simp [cotensorMap_comp, Category.assoc]
  · exact HasZeroObject.zeroIsTerminal.hom_ext _ _

/-- The whole actual pointed cotensor is a bifunctor of its original two carriers. -/
def pointedCotensorBifunctor : PointedSSet.{vC}ᵒᵖ ⥤ SimplicialObject C ⥤ C where
  obj K :=
    { obj B := pointedCotensor B K.unop
      map b := pointedCotensorMap b (𝟙 K.unop)
      map_id B := pointedCotensorMap_id B K.unop
      map_comp b c := by simpa using pointedCotensorMap_comp b c (𝟙 K.unop) (𝟙 K.unop) }
  map k :=
    { app B := pointedCotensorMap (𝟙 B) k.unop
      naturality {_ _} b := by
        rw [← pointedCotensorMap_comp, ← pointedCotensorMap_comp]
        simp }
  map_id K := by
    apply NatTrans.ext
    funext B
    exact pointedCotensorMap_id B K.unop
  map_comp k l := by
    apply NatTrans.ext
    funext B
    simpa using pointedCotensorMap_comp (𝟙 B) (𝟙 B) l.unop k.unop

/-- The full pointed cotensor Hom function retains the actual original source arrow. -/
theorem pointedCotensorHomEquiv_source {X X' : C} (a : X ⟶ X') (K : PointedSSet.{vC})
    (B : SimplicialObject C) (f : X' ⟶ pointedCotensor B K) :
    pointedCotensorHomEquiv X K B (a ≫ f) = pointedCotensorHomEquiv X' K B f ≫
      pointedHomPrecomp ((CosimplicialObject.const C).map a) B := by
  apply Under.UnderMorphism.ext
  change cotensorHomEquiv X K.right B ((a ≫ f) ≫ pointedCotensorProjection B K) =
    cotensorHomEquiv X' K.right B (f ≫ pointedCotensorProjection B K) ≫
      ResolutionHomComplex.precomp ((CosimplicialObject.const C).map a) B
  rw [Category.assoc, cotensorHomEquiv_source]

/-- The full pointed cotensor Hom function retains every actual pointed-weight restriction. -/
theorem pointedCotensorHomEquiv_parameter (X : C) {K L : PointedSSet.{vC}} (k : K ⟶ L)
    (B : SimplicialObject C) (f : X ⟶ pointedCotensor B L) :
    pointedCotensorHomEquiv X K B (f ≫ pointedCotensorMap (𝟙 B) k) =
      k ≫ pointedCotensorHomEquiv X L B f := by
  apply Under.UnderMorphism.ext
  change cotensorHomEquiv X K.right B
      ((f ≫ pointedCotensorMap (𝟙 B) k) ≫ pointedCotensorProjection B K) =
    k.right ≫ cotensorHomEquiv X L.right B (f ≫ pointedCotensorProjection B L)
  rw [Category.assoc, pointedCotensorMap_projection, ← Category.assoc, cotensorHomEquiv_parameter]

/-- Every actual original coefficient map survives in the full pointed cotensor Hom function. -/
theorem pointedCotensorHomEquiv_target (X : C) (K : PointedSSet.{vC})
    {B B' : SimplicialObject C} (b : B ⟶ B') (f : X ⟶ pointedCotensor B K) :
    pointedCotensorHomEquiv X K B' (f ≫ pointedCotensorMap b (𝟙 K)) =
      pointedCotensorHomEquiv X K B f ≫ pointedHomPostcomp ((CosimplicialObject.const C).obj X) b := by
  apply Under.UnderMorphism.ext
  change cotensorHomEquiv X K.right B'
      ((f ≫ pointedCotensorMap b (𝟙 K)) ≫ pointedCotensorProjection B' K) =
    cotensorHomEquiv X K.right B (f ≫ pointedCotensorProjection B K) ≫
      ResolutionHomComplex.postcomp ((CosimplicialObject.const C).obj X) b
  rw [Category.assoc, pointedCotensorMap_projection, ← Category.assoc]
  simp only [CategoryTheory.Under.id_right]
  exact cotensorHomEquiv_target X K.right b (f ≫ pointedCotensorProjection B K)

end PointedCotensorMaps

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

section PointedFrameQuillen

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
open scoped SSet.modelCategoryQuillen

/-- Every original fibration gives a genuine Kan fibration on the entire left frame Hom. -/
theorem leftHom_map_fibration (A : CosimplicialObject C)
    (hA : ∀ j, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A j))
    (hW : ∀ {i j : SimplexCategory} (g : i ⟶ j), weakEquivalences C (A.map g))
    {Y Y' : C} (p : Y ⟶ Y') [Fibration p] :
    Fibration ((leftHomFunctor A).map p) := by
  have hB := LeftFrameHomWeakEquivalence.opposite_matching_fibration A hA
  have hw : ∀ {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j), weakEquivalences Cᵒᵖ (A.op.map g) := by
    intro i j g
    rw [weakEquivalences_op]
    exact hW g.unop
  have hp := QuillenFrameHomComplex.rightPrecomp_fibration p.op A.op hB hw
  exact (fibration_iff _).mpr
    (((fibrations SSet.{vC}).arrow_mk_iso_iff
      (Arrow.isoMk (LeftFrameHomWeakEquivalence.leftRightOppositeIso A Y)
        (LeftFrameHomWeakEquivalence.leftRightOppositeIso A Y')
        (LeftFrameHomWeakEquivalence.leftRightOppositeIso_target A p).symm)).mpr
      ((fibration_iff _).mp hp))

variable [HasZeroObject C] [HasColimitsOfSize.{0, vC} C]

/-- The whole original pointed tensor--Hom adjunction is Quillen for an actual cosimplicial frame. -/
theorem pointedTensorHomAdjunction_isQuillen (A : CosimplicialObject C)
    (hA : ∀ j, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A j))
    (hW : ∀ {i j : SimplexCategory} (g : i ⟶ j), weakEquivalences C (A.map g)) :
    (pointedTensorHomAdjunction A).IsQuillenAdjunction := by
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro Y Y' p hp
    let _ : Fibration p := (fibration_iff _).mpr hp
    exact (fibration_iff _).mp
      ((fibrations_under_iff (Δ[0] : SSet.{vC})
        ((pointedLeftHomFunctor A).map p)).mpr (leftHom_map_fibration A hA hW p))
  · intro Y Y' p hp
    let _ : Fibration p := (fibration_iff _).mpr hp.1
    let _ : WeakEquivalence p := (weakEquivalence_iff _).mpr hp.2
    change trivialFibrations SSet.{vC}
      (ResolutionHomComplex.postcomp A ((SimplicialObject.const C).map p))
    exact LeftFrameHomWeakEquivalence.postcomp_trivialFibration A hA p

/-- Any actual model's original two factories construct the same full left framing functor. -/
def leftFrameOfFactors
    (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C)) :
    C ⥤ CosimplicialObject C :=
  leftFrame (GeneratedFunctorialReplacements.replacementsOfFactors Fc Ff)

/-- Any actual model's original two factories construct the same full right framing functor. -/
def rightFrameOfFactors
    (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C)) :
    C ⥤ SimplicialObject C :=
  rightFrame (GeneratedFunctorialReplacements.replacementsOfFactors Fc Ff)

/-- The actual original generic frame gives its scalar pointed Quillen pair on every original object. -/
theorem originalPointedTensor_isQuillen (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    (pointedTensorHomAdjunction ((leftFrame d).obj X)).IsQuillenAdjunction :=
  pointedTensorHomAdjunction_isQuillen _ (leftFrame_latching_cofibration d X) (leftFrame_map_weak d X)

end PointedFrameQuillen

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

section PointedCotensorAdjunction

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C]
  [HasLimitsOfSize.{0, vC} C] [HasPullbacks C]

/-- The original pointed right Hom as a functor on the full opposite coefficient category. -/
abbrev pointedRightHomFunctor (B : SimplicialObject C) : Cᵒᵖ ⥤ PointedSSet.{vC} where
  obj X := pointedRightHom X.unop B
  map a := pointedHomPrecomp ((CosimplicialObject.const C).map a.unop) B
  map_id X := by
    apply Under.UnderMorphism.ext
    change ResolutionHomComplex.precomp ((CosimplicialObject.const C).map (𝟙 X.unop)) B = 𝟙 _
    rw [CategoryTheory.Functor.map_id, ResolutionHomComplex.precomp_id]
  map_comp a b := by
    apply Under.UnderMorphism.ext
    change ResolutionHomComplex.precomp ((CosimplicialObject.const C).map (b.unop ≫ a.unop)) B =
      ResolutionHomComplex.precomp ((CosimplicialObject.const C).map a.unop) B ≫
        ResolutionHomComplex.precomp ((CosimplicialObject.const C).map b.unop) B
    rw [CategoryTheory.Functor.map_comp, ResolutionHomComplex.precomp_comp]

/-- The full actual scalar cotensor functor, regarded in the original opposite coefficient category. -/
def pointedCotensorScalar (B : SimplicialObject C) : PointedSSet.{vC} ⥤ Cᵒᵖ where
  obj K := Opposite.op (pointedCotensor B K)
  map k := (pointedCotensorMap (𝟙 B) k).op
  map_id K := Quiver.Hom.unop_inj (pointedCotensorMap_id B K)
  map_comp k l := by
    apply Quiver.Hom.unop_inj
    change pointedCotensorMap (𝟙 B) (k ≫ l) =
      pointedCotensorMap (𝟙 B) l ≫ pointedCotensorMap (𝟙 B) k
    simpa using pointedCotensorMap_comp (𝟙 B) (𝟙 B) k l

/-- The actual full cotensor adjunction Hom function retains its original opposite map. -/
def pointedCotensorAdjunctionHom (B : SimplicialObject C) (K : PointedSSet.{vC}) (X : Cᵒᵖ) :
    ((pointedCotensorScalar B).obj K ⟶ X) ≃ (K ⟶ (pointedRightHomFunctor B).obj X) where
  toFun f := pointedCotensorHomEquiv X.unop K B f.unop
  invFun g := ((pointedCotensorHomEquiv X.unop K B).symm g).op
  left_inv f := Quiver.Hom.unop_inj ((pointedCotensorHomEquiv X.unop K B).symm_apply_apply f.unop)
  right_inv g := (pointedCotensorHomEquiv X.unop K B).apply_symm_apply g

/-- The full scalar cotensor and pointed right Hom are an actual adjunction. -/
def pointedCotensorHomAdjunction (B : SimplicialObject C) :
    pointedCotensorScalar B ⊣ pointedRightHomFunctor B :=
  Adjunction.mkOfHomEquiv
    { homEquiv := pointedCotensorAdjunctionHom B
      homEquiv_naturality_left_symm := by
        intro K L X k g
        apply Quiver.Hom.unop_inj
        change (pointedCotensorHomEquiv X.unop K B).symm (k ≫ g) =
          (pointedCotensorHomEquiv X.unop L B).symm g ≫ pointedCotensorMap (𝟙 B) k
        apply (pointedCotensorHomEquiv X.unop K B).injective
        rw [Equiv.apply_symm_apply, pointedCotensorHomEquiv_parameter, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro K X Y f a
        change pointedCotensorHomEquiv Y.unop K B (a.unop ≫ f.unop) =
          pointedCotensorHomEquiv X.unop K B f.unop ≫
            pointedHomPrecomp ((CosimplicialObject.const C).map a.unop) B
        exact pointedCotensorHomEquiv_source a.unop K B f.unop }

end PointedCotensorAdjunction

section PointedCotensorQuillen

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, vC} C]
open scoped SSet.modelCategoryQuillen

/-- An actual right frame gives its full pointed scalar cotensor Quillen adjunction. -/
theorem pointedCotensorHomAdjunction_isQuillen (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (hW : ∀ {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j), weakEquivalences C (B.map g)) :
    (pointedCotensorHomAdjunction B).IsQuillenAdjunction := by
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y p hp
    let _ : Fibration p := (fibration_iff _).mpr hp
    let _ : Cofibration p.unop := (cofibration_unop_iff _).mpr inferInstance
    exact (fibration_iff _).mp
      ((fibrations_under_iff (Δ[0] : SSet.{vC}) ((pointedRightHomFunctor B).map p)).mpr
        (QuillenFrameHomComplex.rightPrecomp_fibration p.unop B hB hW))
  · intro X Y p hp
    let _ : Fibration p := (fibration_iff _).mpr hp.1
    let _ : WeakEquivalence p := (weakEquivalence_iff _).mpr hp.2
    let _ : Cofibration p.unop := (cofibration_unop_iff _).mpr inferInstance
    change trivialFibrations SSet.{vC} (RightFrameHomBoundary.precomp p.unop B)
    exact RightFrameHomBoundary.precomp_trivialFibration p.unop B hB

/-- Every original generic right frame supplies the actual pointed scalar cotensor Quillen pair. -/
theorem originalPointedCotensor_isQuillen (d : GeneratedFunctorialReplacements.Data (C := C)) (Y : C) :
    (pointedCotensorHomAdjunction ((rightFrame d).obj Y)).IsQuillenAdjunction :=
  pointedCotensorHomAdjunction_isQuillen _ (rightFrame_matching_fibration d Y) (rightFrame_map_weak d Y)

end PointedCotensorQuillen

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

section ScalarCofibrancy

open scoped SSet.modelCategoryQuillen

/-- Every actual pointed simplicial set is cofibrant in its created Kan--Quillen model. -/
theorem pointedSSet_isCofibrant (K : PointedSSet.{vC}) : IsCofibrant K := by
  let _ : Mono K.hom := ⟨fun _ _ _ => SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  let f : Under.mk (𝟙 (Δ[0] : SSet.{vC})) ⟶ K := Under.homMk K.hom (Category.id_comp _)
  have hf : Cofibration f :=
    (cofibrations_under_iff (Δ[0] : SSet.{vC}) f).mpr (SSet.modelCategoryQuillen.cofibration_of_mono K.hom)
  exact (isCofibrant_iff_of_isInitial f (Under.mkIdInitial)).mpr hf

end ScalarCofibrancy

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

section PointedHomFunctoriality

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C]

/-- Identity source maps give the identity of the whole pointed Hom complex. -/
@[simp]
theorem pointedHomPrecomp_id (A : CosimplicialObject C) (B : SimplicialObject C) :
    pointedHomPrecomp (𝟙 A) B = 𝟙 (pointedHom A B) := by
  apply Under.UnderMorphism.ext
  exact ResolutionHomComplex.precomp_id A B

/-- The whole pointed source action reverses each original composition. -/
@[simp]
theorem pointedHomPrecomp_comp {A A' A'' : CosimplicialObject C}
    (a : A ⟶ A') (b : A' ⟶ A'') (B : SimplicialObject C) :
    pointedHomPrecomp (a ≫ b) B = pointedHomPrecomp b B ≫ pointedHomPrecomp a B := by
  apply Under.UnderMorphism.ext
  exact ResolutionHomComplex.precomp_comp a b B

/-- Identity target maps give the identity of the whole pointed Hom complex. -/
@[simp]
theorem pointedHomPostcomp_id (A : CosimplicialObject C) (B : SimplicialObject C) :
    pointedHomPostcomp A (𝟙 B) = 𝟙 (pointedHom A B) := by
  apply Under.UnderMorphism.ext
  exact ResolutionHomComplex.postcomp_id A B

/-- The whole pointed target action retains each original composition. -/
@[simp]
theorem pointedHomPostcomp_comp (A : CosimplicialObject C)
    {B B' B'' : SimplicialObject C} (b : B ⟶ B') (c : B' ⟶ B'') :
    pointedHomPostcomp A (b ≫ c) = pointedHomPostcomp A b ≫ pointedHomPostcomp A c := by
  apply Under.UnderMorphism.ext
  exact ResolutionHomComplex.postcomp_comp A b c

/-- The two original pointed coefficient actions commute on the entire complex. -/
theorem pointedHomPrecomp_postcomp {A A' : CosimplicialObject C} (a : A ⟶ A')
    {B B' : SimplicialObject C} (b : B ⟶ B') :
    pointedHomPrecomp a B ≫ pointedHomPostcomp A b =
      pointedHomPostcomp A' b ≫ pointedHomPrecomp a B' := by
  apply Under.UnderMorphism.ext
  exact ResolutionHomComplex.precomp_postcomp a b

/-- The entire genuine pointed resolution Hom is a bifunctor on the original two diagram carriers. -/
def pointedHomBifunctor : (CosimplicialObject C)ᵒᵖ ⥤ SimplicialObject C ⥤ PointedSSet.{vC} where
  obj A :=
    { obj B := pointedHom A.unop B
      map b := pointedHomPostcomp A.unop b
      map_id B := pointedHomPostcomp_id A.unop B
      map_comp b c := pointedHomPostcomp_comp A.unop b c }
  map a :=
    { app B := pointedHomPrecomp a.unop B
      naturality {_ _} b := (pointedHomPrecomp_postcomp a.unop b).symm }
  map_id A := by
    apply NatTrans.ext
    funext B
    exact pointedHomPrecomp_id A.unop B
  map_comp a b := by
    apply NatTrans.ext
    funext B
    change pointedHomPrecomp (b.unop ≫ a.unop) B =
      pointedHomPrecomp a.unop B ≫ pointedHomPrecomp b.unop B
    exact pointedHomPrecomp_comp b.unop a.unop B

end PointedHomFunctoriality

section OriginalPointedComplexes

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  (d : GeneratedFunctorialReplacements.Data (C := C))
open scoped SSet.modelCategoryQuillen

/-- The genuine pointed right HFC on the same original Q and right frame. -/
abbrev pointedRightSpace (X Y : C) : PointedSSet.{vC} :=
  pointedRightHom (d.Q.obj X) ((rightFrame d).obj Y)

/-- The genuine pointed left HFC on the same original left frame and R. -/
abbrev pointedLeftSpace (X Y : C) : PointedSSet.{vC} :=
  pointedLeftHom ((leftFrame d).obj X) (d.R.obj Y)

/-- The genuine pointed two-sided HFC uses both complete original frame diagrams. -/
abbrev pointedTwoSidedSpace (X Y : C) : PointedSSet.{vC} :=
  pointedHom ((leftFrame d).obj X) ((rightFrame d).obj Y)

/-- The entire original Q-resolution map gives the pointed right-to-two-sided comparison. -/
def pointedRightToTwoSided (X Y : C) : pointedRightSpace d X Y ⟶ pointedTwoSidedSpace d X Y :=
  pointedHomPrecomp ((leftResolution d).app X) ((rightFrame d).obj Y)

/-- The entire original R-resolution map gives the pointed left-to-two-sided comparison. -/
def pointedLeftToTwoSided (X Y : C) : pointedLeftSpace d X Y ⟶ pointedTwoSidedSpace d X Y :=
  pointedHomPostcomp ((leftFrame d).obj X) ((rightResolution d).app Y)

/-- The actual original augmentation comparison is weak in the created pointed model. -/
theorem pointedRightToTwoSided_weak (X Y : C) :
    weakEquivalences PointedSSet.{vC} (pointedRightToTwoSided d X Y) := by
  change weakEquivalences SSet.{vC}
    (ResolutionHomComplex.fromAugmentation ((leftResolution d).app X) ((rightFrame d).obj Y))
  let _ : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  exact (weakEquivalence_iff _).mp
    (GeneratedFrameHomComparison.fromAugmentation_weak _ _ _
      (leftFrame_latching_cofibration d X) (rightFrame_matching_fibration d Y)
      (leftResolution_weak d X))

/-- The actual original coaugmentation comparison is weak in the same created pointed model. -/
theorem pointedLeftToTwoSided_weak (X Y : C) :
    weakEquivalences PointedSSet.{vC} (pointedLeftToTwoSided d X Y) := by
  change weakEquivalences SSet.{vC}
    (ResolutionHomComplex.fromCoaugmentation ((leftFrame d).obj X) ((rightResolution d).app Y))
  let _ : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  exact (weakEquivalence_iff _).mp
    (GeneratedFrameHomComparison.fromCoaugmentation_weak _ _ _
      (leftFrame_latching_cofibration d X) (rightFrame_matching_fibration d Y)
      (rightResolution_weak d Y))

/-- The complete original Q coefficient map in the right HFC source variable. -/
def pointedRightSourceMap {X X' : C} (f : X ⟶ X') (Y : C) :
    pointedRightSpace d X' Y ⟶ pointedRightSpace d X Y :=
  pointedHomPrecomp ((CosimplicialObject.const C).map (d.Q.map f)) ((rightFrame d).obj Y)

/-- The complete original R frame map in the right HFC target variable. -/
def pointedRightTargetMap (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    pointedRightSpace d X Y ⟶ pointedRightSpace d X Y' :=
  pointedHomPostcomp ((CosimplicialObject.const C).obj (d.Q.obj X)) ((rightFrame d).map g)

/-- The complete original frame map in the left HFC source variable. -/
def pointedLeftSourceMap {X X' : C} (f : X ⟶ X') (Y : C) :
    pointedLeftSpace d X' Y ⟶ pointedLeftSpace d X Y :=
  pointedHomPrecomp ((leftFrame d).map f) ((SimplicialObject.const C).obj (d.R.obj Y))

/-- The complete original R coefficient map in the left HFC target variable. -/
def pointedLeftTargetMap (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    pointedLeftSpace d X Y ⟶ pointedLeftSpace d X Y' :=
  pointedHomPostcomp ((leftFrame d).obj X) ((SimplicialObject.const C).map (d.R.map g))

/-- The full original left-frame source map in the genuine two-sided complex. -/
def pointedTwoSidedSourceMap {X X' : C} (f : X ⟶ X') (Y : C) :
    pointedTwoSidedSpace d X' Y ⟶ pointedTwoSidedSpace d X Y :=
  pointedHomPrecomp ((leftFrame d).map f) ((rightFrame d).obj Y)

/-- The full original right-frame target map in the genuine two-sided complex. -/
def pointedTwoSidedTargetMap (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    pointedTwoSidedSpace d X Y ⟶ pointedTwoSidedSpace d X Y' :=
  pointedHomPostcomp ((leftFrame d).obj X) ((rightFrame d).map g)

/-- The complete right comparison is natural in every original target map. -/
theorem pointedRightToTwoSided_target (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    pointedRightTargetMap d X g ≫ pointedRightToTwoSided d X Y' =
      pointedRightToTwoSided d X Y ≫ pointedTwoSidedTargetMap d X g :=
  (pointedHomPrecomp_postcomp ((leftResolution d).app X) ((rightFrame d).map g)).symm

/-- The complete left comparison is natural in every original target map. -/
theorem pointedLeftToTwoSided_target (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    pointedLeftTargetMap d X g ≫ pointedLeftToTwoSided d X Y' =
      pointedLeftToTwoSided d X Y ≫ pointedTwoSidedTargetMap d X g := by
  apply Under.UnderMorphism.ext
  change ResolutionHomComplex.postcomp ((leftFrame d).obj X)
      ((SimplicialObject.const C).map (d.R.map g)) ≫
        ResolutionHomComplex.postcomp ((leftFrame d).obj X) ((rightResolution d).app Y') =
    ResolutionHomComplex.postcomp ((leftFrame d).obj X) ((rightResolution d).app Y) ≫
      ResolutionHomComplex.postcomp ((leftFrame d).obj X) ((rightFrame d).map g)
  rw [← ResolutionHomComplex.postcomp_comp, ← ResolutionHomComplex.postcomp_comp]
  exact congrArg (ResolutionHomComplex.postcomp ((leftFrame d).obj X)) ((rightResolution d).naturality g)

/-- The complete right comparison is natural in every original source map. -/
theorem pointedRightToTwoSided_source {X X' : C} (f : X ⟶ X') (Y : C) :
    pointedRightSourceMap d f Y ≫ pointedRightToTwoSided d X Y =
      pointedRightToTwoSided d X' Y ≫ pointedTwoSidedSourceMap d f Y := by
  apply Under.UnderMorphism.ext
  change ResolutionHomComplex.precomp ((CosimplicialObject.const C).map (d.Q.map f))
      ((rightFrame d).obj Y) ≫ ResolutionHomComplex.precomp ((leftResolution d).app X) ((rightFrame d).obj Y) =
    ResolutionHomComplex.precomp ((leftResolution d).app X') ((rightFrame d).obj Y) ≫
      ResolutionHomComplex.precomp ((leftFrame d).map f) ((rightFrame d).obj Y)
  rw [← ResolutionHomComplex.precomp_comp, ← ResolutionHomComplex.precomp_comp]
  exact congrArg (fun a => ResolutionHomComplex.precomp a ((rightFrame d).obj Y))
    ((leftResolution d).naturality f).symm

/-- The complete left comparison is natural in every original source map. -/
theorem pointedLeftToTwoSided_source {X X' : C} (f : X ⟶ X') (Y : C) :
    pointedLeftSourceMap d f Y ≫ pointedLeftToTwoSided d X Y =
      pointedLeftToTwoSided d X' Y ≫ pointedTwoSidedSourceMap d f Y :=
  pointedHomPrecomp_postcomp ((leftFrame d).map f) ((rightResolution d).app Y)

/-- Every original weak source map gives a weak entire pointed right HFC map. -/
theorem pointedRightSourceMap_weak {X X' : C} (f : X ⟶ X')
    (hf : weakEquivalences C f) (Y : C) :
    weakEquivalences PointedSSet.{vC} (pointedRightSourceMap d f Y) := by
  change weakEquivalences SSet.{vC} (RightFrameHomBoundary.precomp (d.Q.map f) ((rightFrame d).obj Y))
  let _ : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let _ : IsCofibrant (d.Q.obj X') := d.q_cofibrant X'
  let _ : WeakEquivalence (d.Q.map f) := (weakEquivalence_iff _).mpr (d.q_map_weak f hf)
  exact (weakEquivalence_iff _).mp
    (RightFrameHomBoundary.precomp_weak _ _ (rightFrame_matching_fibration d Y))

/-- Every original weak target map gives a weak entire pointed left HFC map. -/
theorem pointedLeftTargetMap_weak (X : C) {Y Y' : C} (g : Y ⟶ Y')
    (hg : weakEquivalences C g) :
    weakEquivalences PointedSSet.{vC} (pointedLeftTargetMap d X g) := by
  change weakEquivalences SSet.{vC}
    (ResolutionHomComplex.postcomp ((leftFrame d).obj X) ((SimplicialObject.const C).map (d.R.map g)))
  let _ : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  let _ : IsFibrant (d.R.obj Y') := d.r_fibrant Y'
  let _ : WeakEquivalence (d.R.map g) := (weakEquivalence_iff _).mpr (d.r_map_weak g hg)
  exact (weakEquivalence_iff _).mp
    (LeftFrameHomWeakEquivalence.postcomp_weak _ (leftFrame_latching_cofibration d X) _)

/-- A square of complete pointed spaces with weak vertical maps transfers weakness both ways. -/
theorem pointedWeak_iff_of_square {K L K' L' : PointedSSet.{vC}}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (ha : weakEquivalences PointedSSet.{vC} a) (hb : weakEquivalences PointedSSet.{vC} b)
    (h : f ≫ b = a ≫ g) :
    weakEquivalences PointedSSet.{vC} f ↔ weakEquivalences PointedSSet.{vC} g := by
  constructor
  · intro hf
    apply (weakEquivalences PointedSSet.{vC}).of_precomp a g ha
    rw [← h]
    exact (weakEquivalences PointedSSet.{vC}).comp_mem _ _ hf hb
  · intro hg
    apply (weakEquivalences PointedSSet.{vC}).of_postcomp f b hb
    rw [h]
    exact (weakEquivalences PointedSSet.{vC}).comp_mem _ _ ha hg

/-- Every original weak target map gives a weak entire pointed right HFC map, by the actual comparison span. -/
theorem pointedRightTargetMap_weak (X : C) {Y Y' : C} (g : Y ⟶ Y')
    (hg : weakEquivalences C g) :
    weakEquivalences PointedSSet.{vC} (pointedRightTargetMap d X g) := by
  have hTwo : weakEquivalences PointedSSet.{vC} (pointedTwoSidedTargetMap d X g) :=
    (pointedWeak_iff_of_square (pointedLeftTargetMap d X g) (pointedTwoSidedTargetMap d X g)
      (pointedLeftToTwoSided d X Y) (pointedLeftToTwoSided d X Y')
      (pointedLeftToTwoSided_weak d X Y) (pointedLeftToTwoSided_weak d X Y')
      (pointedLeftToTwoSided_target d X g)).mp (pointedLeftTargetMap_weak d X g hg)
  exact
    (pointedWeak_iff_of_square (pointedRightTargetMap d X g) (pointedTwoSidedTargetMap d X g)
      (pointedRightToTwoSided d X Y) (pointedRightToTwoSided d X Y')
      (pointedRightToTwoSided_weak d X Y) (pointedRightToTwoSided_weak d X Y')
      (pointedRightToTwoSided_target d X g)).mpr hTwo

end OriginalPointedComplexes

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

section PointedHomotopySpaces

open scoped SSet.modelCategoryQuillen

/-- The actual canonical homotopy category of pointed simplicial sets. -/
abbrev PointedSpaceHo := (weakEquivalences PointedSSet.{vC}).Localization

/-- The original weak localization of the actual pointed simplicial-set carrier. -/
abbrev pointedProjection : PointedSSet.{vC} ⥤ PointedSpaceHo.{vC} :=
  (weakEquivalences PointedSSet.{vC}).Q

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

/-- The actual pointed right homotopy function space. -/
abbrev pointedRightHoSpace (X Y : C) : PointedSpaceHo.{vC} :=
  pointedProjection.obj (pointedRightSpace d X Y)

/-- The actual pointed left homotopy function space. -/
abbrev pointedLeftHoSpace (X Y : C) : PointedSpaceHo.{vC} :=
  pointedProjection.obj (pointedLeftSpace d X Y)

/-- The entire original right comparison gives its actual weak-localization isomorphism. -/
def pointedRightComparisonIso (X Y : C) :
    pointedRightHoSpace d X Y ≅ pointedProjection.obj (pointedTwoSidedSpace d X Y) := by
  let _ : IsIso (pointedProjection.map (pointedRightToTwoSided d X Y)) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC}) _
      (pointedRightToTwoSided_weak d X Y)
  exact asIso (pointedProjection.map (pointedRightToTwoSided d X Y))

/-- The entire original left comparison gives its actual weak-localization isomorphism. -/
def pointedLeftComparisonIso (X Y : C) :
    pointedLeftHoSpace d X Y ≅ pointedProjection.obj (pointedTwoSidedSpace d X Y) := by
  let _ : IsIso (pointedProjection.map (pointedLeftToTwoSided d X Y)) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC}) _
      (pointedLeftToTwoSided_weak d X Y)
  exact asIso (pointedProjection.map (pointedLeftToTwoSided d X Y))

/-- The same original pointed left/right comparison span gives the full homotopy-space isomorphism. -/
def pointedLeftRightIso (X Y : C) : pointedLeftHoSpace d X Y ≅ pointedRightHoSpace d X Y :=
  pointedLeftComparisonIso d X Y ≪≫ (pointedRightComparisonIso d X Y).symm

/-- The entire original forward comparison word retains both actual weak frame legs. -/
theorem pointedLeftRightIso_hom (X Y : C) :
    (pointedLeftRightIso d X Y).hom =
      pointedProjection.map (pointedLeftToTwoSided d X Y) ≫
        (pointedRightComparisonIso d X Y).inv := rfl

/-- The entire original inverse comparison word retains the same two weak frame legs. -/
theorem pointedLeftRightIso_inv (X Y : C) :
    (pointedLeftRightIso d X Y).inv =
      pointedProjection.map (pointedRightToTwoSided d X Y) ≫
        (pointedLeftComparisonIso d X Y).inv := rfl

/-- The full pointed homotopy-space comparison is natural in every original target morphism. -/
theorem pointedLeftRightIso_target (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    pointedProjection.map (pointedLeftTargetMap d X g) ≫ (pointedLeftRightIso d X Y').hom =
      (pointedLeftRightIso d X Y).hom ≫ pointedProjection.map (pointedRightTargetMap d X g) := by
  have hL : pointedProjection.map (pointedLeftTargetMap d X g) ≫
        (pointedLeftComparisonIso d X Y').hom =
      (pointedLeftComparisonIso d X Y).hom ≫ pointedProjection.map (pointedTwoSidedTargetMap d X g) :=
    (pointedProjection.map_comp _ _).symm.trans
      ((congrArg pointedProjection.map (pointedLeftToTwoSided_target d X g)).trans (pointedProjection.map_comp _ _))
  have hR : pointedProjection.map (pointedRightTargetMap d X g) ≫
        (pointedRightComparisonIso d X Y').hom =
      (pointedRightComparisonIso d X Y).hom ≫ pointedProjection.map (pointedTwoSidedTargetMap d X g) :=
    (pointedProjection.map_comp _ _).symm.trans
      ((congrArg pointedProjection.map (pointedRightToTwoSided_target d X g)).trans (pointedProjection.map_comp _ _))
  apply (cancel_mono (pointedRightComparisonIso d X Y').hom).mp
  change (pointedProjection.map (pointedLeftTargetMap d X g) ≫
        ((pointedLeftComparisonIso d X Y').hom ≫ (pointedRightComparisonIso d X Y').inv)) ≫
      (pointedRightComparisonIso d X Y').hom =
    (((pointedLeftComparisonIso d X Y).hom ≫ (pointedRightComparisonIso d X Y).inv) ≫
      pointedProjection.map (pointedRightTargetMap d X g)) ≫ (pointedRightComparisonIso d X Y').hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hR]
  simp only [Iso.inv_hom_id_assoc]
  exact hL

/-- The full pointed homotopy-space comparison is natural in every original source morphism. -/
theorem pointedLeftRightIso_source {X X' : C} (f : X ⟶ X') (Y : C) :
    pointedProjection.map (pointedLeftSourceMap d f Y) ≫ (pointedLeftRightIso d X Y).hom =
      (pointedLeftRightIso d X' Y).hom ≫ pointedProjection.map (pointedRightSourceMap d f Y) := by
  have hL : pointedProjection.map (pointedLeftSourceMap d f Y) ≫
        (pointedLeftComparisonIso d X Y).hom =
      (pointedLeftComparisonIso d X' Y).hom ≫ pointedProjection.map (pointedTwoSidedSourceMap d f Y) :=
    (pointedProjection.map_comp _ _).symm.trans
      ((congrArg pointedProjection.map (pointedLeftToTwoSided_source d f Y)).trans (pointedProjection.map_comp _ _))
  have hR : pointedProjection.map (pointedRightSourceMap d f Y) ≫
        (pointedRightComparisonIso d X Y).hom =
      (pointedRightComparisonIso d X' Y).hom ≫ pointedProjection.map (pointedTwoSidedSourceMap d f Y) :=
    (pointedProjection.map_comp _ _).symm.trans
      ((congrArg pointedProjection.map (pointedRightToTwoSided_source d f Y)).trans (pointedProjection.map_comp _ _))
  apply (cancel_mono (pointedRightComparisonIso d X Y).hom).mp
  change (pointedProjection.map (pointedLeftSourceMap d f Y) ≫
        ((pointedLeftComparisonIso d X Y).hom ≫ (pointedRightComparisonIso d X Y).inv)) ≫
      (pointedRightComparisonIso d X Y).hom =
    (((pointedLeftComparisonIso d X' Y).hom ≫ (pointedRightComparisonIso d X' Y).inv) ≫
      pointedProjection.map (pointedRightSourceMap d f Y)) ≫ (pointedRightComparisonIso d X Y).hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hR]
  simp only [Iso.inv_hom_id_assoc]
  exact hL

end PointedHomotopySpaces

section TensorHomotopyHom

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  [HasColimitsOfSize.{0, vC} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))
open scoped SSet.modelCategoryQuillen

/-- The actual scalar Quillen pair gives the full ordinary-Ho tensor mapping comparison. -/
def pointedTensorHoHomEquiv (X : C) (K : PointedSSet.{vC}) (Y : C) :
    ((weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X) K) ⟶
      (weakEquivalences C).Q.obj (d.R.obj Y)) ≃
    (pointedProjection.obj K ⟶ pointedLeftHoSpace d X Y) := by
  let _ : (pointedTensorHomAdjunction ((leftFrame d).obj X)).IsQuillenAdjunction :=
    originalPointedTensor_isQuillen d X
  let _ : IsCofibrant K := pointedSSet_isCofibrant K
  let _ : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  exact QuillenOrdinaryHoHom.homEquiv (pointedTensorHomAdjunction ((leftFrame d).obj X)) K (d.R.obj Y)

end TensorHomotopyHom

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

namespace LocalQuillenHom

variable {A : Type uA} [Category.{vA} A] [ModelCategory A]
  {B : Type uB} [Category.{vB} B] [ModelCategory B]
  {HA : Type uH1} [Category.{vH1} HA] {HB : Type uH2} [Category.{vH2} HB]
  {T : A ⥤ B} {U : B ⥤ A} (adj : T ⊣ U) [adj.IsQuillenAdjunction]
  (LA : A ⥤ HA) [LA.IsLocalization (weakEquivalences A)]
  (LB : B ⥤ HB) [LB.IsLocalization (weakEquivalences B)]

/-- The actual original Quillen Hom functions give the full comparison for any two original localizations. -/
def homEquiv (X : A) [IsCofibrant X] (Y : B) [IsFibrant Y] :
    (LB.obj (T.obj X) ⟶ LB.obj Y) ≃ (LA.obj X ⟶ LA.obj (U.obj Y)) := by
  let _ : IsCofibrant (T.obj X) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) inferInstance
  let _ : IsFibrant (U.obj Y) :=
    Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adj) inferInstance
  exact (leftHomotopyClassEquivOfIsLocalization LB (X := T.obj X) (Y := Y)).symm.trans
    ((QuillenOrdinaryHoHom.classEquiv adj X Y).trans
      (leftHomotopyClassEquivOfIsLocalization LA (X := X) (Y := U.obj Y)))

/-- Every represented arrow retains the full original Quillen adjunct under the chosen localizations. -/
theorem homEquiv_map (X : A) [IsCofibrant X] (Y : B) [IsFibrant Y] (f : T.obj X ⟶ Y) :
    homEquiv adj LA LB X Y (LB.map f) = LA.map (adj.homEquiv X Y f) := by
  let _ : IsCofibrant (T.obj X) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) inferInstance
  let _ : IsFibrant (U.obj Y) :=
    Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adj) inferInstance
  let e := leftHomotopyClassEquivOfIsLocalization LB (X := T.obj X) (Y := Y)
  have he : e.symm (LB.map f) = LeftHomotopyClass.mk f := by
    rw [← leftHomotopyClassEquivOfIsLocalization_mk LB f]
    exact e.symm_apply_apply _
  change leftHomotopyClassEquivOfIsLocalization LA
    (QuillenOrdinaryHoHom.classEquiv adj X Y (e.symm (LB.map f))) = _
  rw [he, QuillenOrdinaryHoHom.classEquiv_mk, leftHomotopyClassEquivOfIsLocalization_mk]

end LocalQuillenHom

section CotensorHomotopyHom

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, vC} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))
open scoped SSet.modelCategoryQuillen

/-- The actual scalar cotensor Quillen pair gives the full ordinary-Ho mapping comparison. -/
def pointedCotensorHoHomEquiv (X : C) (K : PointedSSet.{vC}) (Y : C) :
    ((weakEquivalences C).Q.obj (d.Q.obj X) ⟶
      (weakEquivalences C).Q.obj (pointedCotensor ((rightFrame d).obj Y) K)) ≃
    (pointedProjection.obj K ⟶ pointedRightHoSpace d X Y) := by
  let B := (rightFrame d).obj Y
  let q := d.Q.obj X
  let adj := pointedCotensorHomAdjunction B
  let _ : adj.IsQuillenAdjunction := originalPointedCotensor_isQuillen d Y
  let _ : IsCofibrant K := pointedSSet_isCofibrant K
  let _ : IsCofibrant q := d.q_cofibrant X
  let _ : IsFibrant (Opposite.op q) := by
    apply (isFibrant_iff_of_isTerminal (initial.to q).op initialIsInitial.op).mpr
    rw [fibration_op_iff]
    infer_instance
  let _ : ((weakEquivalences C).Q.op).IsLocalization (weakEquivalences Cᵒᵖ) := by
    rw [weakEquivalences_op]
    infer_instance
  exact Quiver.Hom.opEquiv.trans
    (LocalQuillenHom.homEquiv adj pointedProjection (weakEquivalences C).Q.op K (Opposite.op q))

end CotensorHomotopyHom

section FramedHomotopyHom

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))
open scoped SSet.modelCategoryQuillen

/-- The original full Q counit supplies its actual localization isomorphism. -/
def qHomotopyIso (X : C) : (weakEquivalences C).Q.obj (d.Q.obj X) ≅ (weakEquivalences C).Q.obj X := by
  let _ : IsIso ((weakEquivalences C).Q.map (d.q.app X)) :=
    Localization.inverts (weakEquivalences C).Q (weakEquivalences C) _ (d.q_trivialFibration X).2
  exact asIso ((weakEquivalences C).Q.map (d.q.app X))

/-- The original full R unit supplies its actual localization isomorphism. -/
def rHomotopyIso (Y : C) : (weakEquivalences C).Q.obj Y ≅ (weakEquivalences C).Q.obj (d.R.obj Y) := by
  let _ : IsIso ((weakEquivalences C).Q.map (d.r.app Y)) :=
    Localization.inverts (weakEquivalences C).Q (weakEquivalences C) _ (d.r_trivialCofibration Y).2
  exact asIso ((weakEquivalences C).Q.map (d.r.app Y))

/-- The actual framing gives the full scalar tensor--cotensor Ho Hom bijection in every pointed model. -/
def framedHomEquiv (X : C) (K : PointedSSet.{vC}) (Y : C) :
    ((weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X) K) ⟶ (weakEquivalences C).Q.obj Y) ≃
      ((weakEquivalences C).Q.obj X ⟶ (weakEquivalences C).Q.obj (pointedCotensor ((rightFrame d).obj Y) K)) :=
  (Iso.homCongr (Iso.refl _) (rHomotopyIso d Y)).trans
    ((pointedTensorHoHomEquiv d X K Y).trans
      ((Iso.homCongr (Iso.refl (pointedProjection.obj K)) (pointedLeftRightIso d X Y)).trans
        ((pointedCotensorHoHomEquiv d X K Y).symm.trans
          (Iso.homCongr (qHomotopyIso d X) (Iso.refl _)))))

end FramedHomotopyHom

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

section AdjunctionReadbacks

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C]

section Tensor
variable [HasColimitsOfSize.{0, vC} C] [HasPushouts C]

/-- The scalar tensor adjunction uses the entire original pointed Hom function. -/
theorem pointedTensorHomAdjunction_homEquiv (A : CosimplicialObject C) (K : PointedSSet.{vC}) (Y : C)
    (f : pointedTensor A K ⟶ Y) :
    (pointedTensorHomAdjunction A).homEquiv K Y f = pointedTensorHomEquiv A K Y f := by
  simp only [pointedTensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The whole pointed tensor Hom function keeps every original frame map. -/
theorem pointedTensorHomEquiv_source {A A' : CosimplicialObject C} (a : A ⟶ A')
    (K : PointedSSet.{vC}) (Y : C) (f : pointedTensor A' K ⟶ Y) :
    pointedTensorHomEquiv A K Y (pointedTensorMap a (𝟙 K) ≫ f) =
      pointedTensorHomEquiv A' K Y f ≫ pointedHomPrecomp a ((SimplicialObject.const C).obj Y) := by
  apply Under.UnderMorphism.ext
  change tensorHomEquiv A K.right Y
      (pointedTensorQuotient A K ≫ (pointedTensorMap a (𝟙 K) ≫ f)) =
    tensorHomEquiv A' K.right Y (pointedTensorQuotient A' K ≫ f) ≫
      ResolutionHomComplex.precomp a ((SimplicialObject.const C).obj Y)
  rw [← Category.assoc, pointedTensorMap_quotient, Category.assoc]
  simp only [CategoryTheory.Under.id_right]
  exact tensorHomEquiv_source a K.right Y (pointedTensorQuotient A' K ≫ f)

end Tensor

section Cotensor
variable [HasLimitsOfSize.{0, vC} C] [HasPullbacks C]

/-- The scalar cotensor adjunction keeps the entire original pointed Hom function on opposite maps. -/
theorem pointedCotensorHomAdjunction_homEquiv (B : SimplicialObject C) (K : PointedSSet.{vC}) (X : Cᵒᵖ)
    (f : (pointedCotensorScalar B).obj K ⟶ X) :
    (pointedCotensorHomAdjunction B).homEquiv K X f = pointedCotensorHomEquiv X.unop K B f.unop := by
  simp only [pointedCotensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

end Cotensor

end AdjunctionReadbacks

section TensorHomotopyNaturality

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  [HasColimitsOfSize.{0, vC} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))
open scoped SSet.modelCategoryQuillen

/-- The actual framed pointed tensor is cofibrant for every original weight and input object. -/
theorem pointedTensor_isCofibrant (X : C) (K : PointedSSet.{vC}) :
    IsCofibrant (pointedTensor ((leftFrame d).obj X) K) := by
  let _ : (pointedTensorHomAdjunction ((leftFrame d).obj X)).IsQuillenAdjunction :=
    originalPointedTensor_isQuillen d X
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := pointedTensorHomAdjunction ((leftFrame d).obj X)) (pointedSSet_isCofibrant K)

/-- Every represented full tensor Ho arrow retains its original pointed transpose. -/
theorem pointedTensorHoHomEquiv_map (X : C) (K : PointedSSet.{vC}) (Y : C)
    (f : pointedTensor ((leftFrame d).obj X) K ⟶ d.R.obj Y) :
    pointedTensorHoHomEquiv d X K Y ((weakEquivalences C).Q.map f) =
      pointedProjection.map (pointedTensorHomEquiv ((leftFrame d).obj X) K (d.R.obj Y) f) := by
  let _ : (pointedTensorHomAdjunction ((leftFrame d).obj X)).IsQuillenAdjunction :=
    originalPointedTensor_isQuillen d X
  let _ : IsCofibrant K := pointedSSet_isCofibrant K
  let _ : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  exact (QuillenOrdinaryHoHom.homEquiv_map
    (pointedTensorHomAdjunction ((leftFrame d).obj X)) K (d.R.obj Y) f).trans
      (congrArg pointedProjection.map (pointedTensorHomAdjunction_homEquiv _ _ _ f))

/-- The ordinary-Ho tensor transpose retains every original source frame map. -/
theorem pointedTensorHoHomEquiv_source {X X' : C} (f : X ⟶ X') (K : PointedSSet.{vC}) (Y : C)
    (h : (weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X') K) ⟶
      (weakEquivalences C).Q.obj (d.R.obj Y)) :
    pointedTensorHoHomEquiv d X K Y
      ((weakEquivalences C).Q.map (pointedTensorMap ((leftFrame d).map f) (𝟙 K)) ≫ h) =
    pointedTensorHoHomEquiv d X' K Y h ≫ pointedProjection.map (pointedLeftSourceMap d f Y) := by
  let _ : IsCofibrant (pointedTensor ((leftFrame d).obj X') K) := pointedTensor_isCofibrant d X' K
  let _ : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  obtain ⟨g, rfl⟩ := map_surjective_of_isLocalization (weakEquivalences C).Q _ _ h
  rw [← CategoryTheory.Functor.map_comp, pointedTensorHoHomEquiv_map, pointedTensorHoHomEquiv_map,
    pointedTensorHomEquiv_source, CategoryTheory.Functor.map_comp]
  rfl

/-- The ordinary-Ho tensor transpose retains every original R target map. -/
theorem pointedTensorHoHomEquiv_target (X : C) (K : PointedSSet.{vC}) {Y Y' : C} (g : Y ⟶ Y')
    (h : (weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X) K) ⟶
      (weakEquivalences C).Q.obj (d.R.obj Y)) :
    pointedTensorHoHomEquiv d X K Y' (h ≫ (weakEquivalences C).Q.map (d.R.map g)) =
      pointedTensorHoHomEquiv d X K Y h ≫ pointedProjection.map (pointedLeftTargetMap d X g) := by
  let _ : IsCofibrant (pointedTensor ((leftFrame d).obj X) K) := pointedTensor_isCofibrant d X K
  let _ : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  obtain ⟨f, rfl⟩ := map_surjective_of_isLocalization (weakEquivalences C).Q _ _ h
  rw [← CategoryTheory.Functor.map_comp, pointedTensorHoHomEquiv_map, pointedTensorHoHomEquiv_map,
    pointedTensorHomEquiv_target, CategoryTheory.Functor.map_comp]
  rfl

/-- The ordinary-Ho tensor transpose retains every original pointed weight map. -/
theorem pointedTensorHoHomEquiv_parameter (X : C) {K L : PointedSSet.{vC}} (k : K ⟶ L) (Y : C)
    (h : (weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X) L) ⟶
      (weakEquivalences C).Q.obj (d.R.obj Y)) :
    pointedTensorHoHomEquiv d X K Y
      ((weakEquivalences C).Q.map (pointedTensorMap (𝟙 ((leftFrame d).obj X)) k) ≫ h) =
    pointedProjection.map k ≫ pointedTensorHoHomEquiv d X L Y h := by
  let _ : IsCofibrant (pointedTensor ((leftFrame d).obj X) L) := pointedTensor_isCofibrant d X L
  let _ : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  obtain ⟨f, rfl⟩ := map_surjective_of_isLocalization (weakEquivalences C).Q _ _ h
  rw [← CategoryTheory.Functor.map_comp, pointedTensorHoHomEquiv_map, pointedTensorHoHomEquiv_map,
    pointedTensorHomEquiv_parameter, CategoryTheory.Functor.map_comp]

end TensorHomotopyNaturality

section CotensorHomotopyNaturality

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, vC} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))
open scoped SSet.modelCategoryQuillen

/-- The actual framed pointed cotensor is fibrant for every original input and weight. -/
theorem pointedCotensor_isFibrant (Y : C) (K : PointedSSet.{vC}) :
    IsFibrant (pointedCotensor ((rightFrame d).obj Y) K) := by
  let _ : (pointedCotensorHomAdjunction ((rightFrame d).obj Y)).IsQuillenAdjunction :=
    originalPointedCotensor_isQuillen d Y
  let _ : IsCofibrant K := pointedSSet_isCofibrant K
  have hc : IsCofibrant (Opposite.op (pointedCotensor ((rightFrame d).obj Y) K)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := pointedCotensorHomAdjunction ((rightFrame d).obj Y)) inferInstance
  have hp := (isCofibrant_iff_of_isInitial
    (terminal.from (pointedCotensor ((rightFrame d).obj Y) K)).op terminalIsTerminal.op).mp hc
  exact (isFibrant_iff_of_isTerminal _ terminalIsTerminal).mpr ((cofibration_op_iff _).mp hp)

/-- Every represented whole cotensor Ho arrow retains its original pointed transpose. -/
theorem pointedCotensorHoHomEquiv_map (X : C) (K : PointedSSet.{vC}) (Y : C)
    (f : d.Q.obj X ⟶ pointedCotensor ((rightFrame d).obj Y) K) :
    pointedCotensorHoHomEquiv d X K Y ((weakEquivalences C).Q.map f) =
      pointedProjection.map (pointedCotensorHomEquiv (d.Q.obj X) K ((rightFrame d).obj Y) f) := by
  let _ : (pointedCotensorHomAdjunction ((rightFrame d).obj Y)).IsQuillenAdjunction :=
    originalPointedCotensor_isQuillen d Y
  let _ : IsCofibrant K := pointedSSet_isCofibrant K
  let _ : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let _ : IsFibrant (Opposite.op (d.Q.obj X)) := by
    apply (isFibrant_iff_of_isTerminal (initial.to (d.Q.obj X)).op initialIsInitial.op).mpr
    rw [fibration_op_iff]
    infer_instance
  let _ : ((weakEquivalences C).Q.op).IsLocalization (weakEquivalences Cᵒᵖ) := by
    rw [weakEquivalences_op]
    infer_instance
  exact (LocalQuillenHom.homEquiv_map
    (pointedCotensorHomAdjunction ((rightFrame d).obj Y)) pointedProjection (weakEquivalences C).Q.op
    K (Opposite.op (d.Q.obj X)) f.op).trans
      (congrArg pointedProjection.map (pointedCotensorHomAdjunction_homEquiv _ _ _ f.op))

/-- The ordinary-Ho cotensor transpose keeps the complete original Q source map. -/
theorem pointedCotensorHoHomEquiv_source {X X' : C} (f : X ⟶ X') (K : PointedSSet.{vC}) (Y : C)
    (h : (weakEquivalences C).Q.obj (d.Q.obj X') ⟶
      (weakEquivalences C).Q.obj (pointedCotensor ((rightFrame d).obj Y) K)) :
    pointedCotensorHoHomEquiv d X K Y ((weakEquivalences C).Q.map (d.Q.map f) ≫ h) =
      pointedCotensorHoHomEquiv d X' K Y h ≫ pointedProjection.map (pointedRightSourceMap d f Y) := by
  let _ : IsCofibrant (d.Q.obj X') := d.q_cofibrant X'
  let _ : IsFibrant (pointedCotensor ((rightFrame d).obj Y) K) := pointedCotensor_isFibrant d Y K
  obtain ⟨g, rfl⟩ := map_surjective_of_isLocalization (weakEquivalences C).Q _ _ h
  rw [← CategoryTheory.Functor.map_comp, pointedCotensorHoHomEquiv_map, pointedCotensorHoHomEquiv_map,
    pointedCotensorHomEquiv_source, CategoryTheory.Functor.map_comp]
  rfl

/-- The ordinary-Ho cotensor transpose keeps the complete original R frame target map. -/
theorem pointedCotensorHoHomEquiv_target (X : C) (K : PointedSSet.{vC}) {Y Y' : C} (g : Y ⟶ Y')
    (h : (weakEquivalences C).Q.obj (d.Q.obj X) ⟶
      (weakEquivalences C).Q.obj (pointedCotensor ((rightFrame d).obj Y) K)) :
    pointedCotensorHoHomEquiv d X K Y'
      (h ≫ (weakEquivalences C).Q.map (pointedCotensorMap ((rightFrame d).map g) (𝟙 K))) =
      pointedCotensorHoHomEquiv d X K Y h ≫ pointedProjection.map (pointedRightTargetMap d X g) := by
  let _ : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let _ : IsFibrant (pointedCotensor ((rightFrame d).obj Y) K) := pointedCotensor_isFibrant d Y K
  obtain ⟨f, rfl⟩ := map_surjective_of_isLocalization (weakEquivalences C).Q _ _ h
  rw [← CategoryTheory.Functor.map_comp, pointedCotensorHoHomEquiv_map, pointedCotensorHoHomEquiv_map,
    pointedCotensorHomEquiv_target, CategoryTheory.Functor.map_comp]
  rfl

/-- The ordinary-Ho cotensor transpose keeps every original pointed weight restriction. -/
theorem pointedCotensorHoHomEquiv_parameter (X : C) {K L : PointedSSet.{vC}} (k : K ⟶ L) (Y : C)
    (h : (weakEquivalences C).Q.obj (d.Q.obj X) ⟶
      (weakEquivalences C).Q.obj (pointedCotensor ((rightFrame d).obj Y) L)) :
    pointedCotensorHoHomEquiv d X K Y
      (h ≫ (weakEquivalences C).Q.map (pointedCotensorMap (𝟙 ((rightFrame d).obj Y)) k)) =
      pointedProjection.map k ≫ pointedCotensorHoHomEquiv d X L Y h := by
  let _ : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let _ : IsFibrant (pointedCotensor ((rightFrame d).obj Y) L) := pointedCotensor_isFibrant d Y L
  obtain ⟨f, rfl⟩ := map_surjective_of_isLocalization (weakEquivalences C).Q _ _ h
  rw [← CategoryTheory.Functor.map_comp, pointedCotensorHoHomEquiv_map, pointedCotensorHoHomEquiv_map,
    pointedCotensorHomEquiv_parameter, CategoryTheory.Functor.map_comp]

end CotensorHomotopyNaturality

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

section FullFramedHomNaturality

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))
open scoped SSet.modelCategoryQuillen

/-- The full framed Hom function is its entire original five-map comparison word. -/
theorem framedHomEquiv_apply (X : C) (K : PointedSSet.{vC}) (Y : C)
    (h : (weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X) K) ⟶ (weakEquivalences C).Q.obj Y) :
    framedHomEquiv d X K Y h =
      (qHomotopyIso d X).inv ≫ (pointedCotensorHoHomEquiv d X K Y).symm
        (pointedTensorHoHomEquiv d X K Y (h ≫ (rHomotopyIso d Y).hom) ≫
          (pointedLeftRightIso d X Y).hom) := by
  simp only [framedHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id]

omit [HasZeroObject C] [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C] in
/-- The original Q counit gives the full inverse-Q source naturality square. -/
theorem qHomotopyIso_inv_naturality {X X' : C} (f : X ⟶ X') :
    (qHomotopyIso d X).inv ≫ (weakEquivalences C).Q.map (d.Q.map f) =
      (weakEquivalences C).Q.map f ≫ (qHomotopyIso d X').inv := by
  have h : (weakEquivalences C).Q.map (d.Q.map f) ≫ (qHomotopyIso d X').hom =
      (qHomotopyIso d X).hom ≫ (weakEquivalences C).Q.map f := by
    change (weakEquivalences C).Q.map (d.Q.map f) ≫ (weakEquivalences C).Q.map (d.q.app X') =
      (weakEquivalences C).Q.map (d.q.app X) ≫ (weakEquivalences C).Q.map f
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (weakEquivalences C).Q.map (d.q.naturality f)
  apply (cancel_mono (qHomotopyIso d X').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

omit [HasZeroObject C] [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C] in
/-- The original R unit retains the entire full target naturality square. -/
theorem rHomotopyIso_naturality {Y Y' : C} (g : Y ⟶ Y') :
    (weakEquivalences C).Q.map g ≫ (rHomotopyIso d Y').hom =
      (rHomotopyIso d Y).hom ≫ (weakEquivalences C).Q.map (d.R.map g) := by
  change (weakEquivalences C).Q.map g ≫ (weakEquivalences C).Q.map (d.r.app Y') =
    (weakEquivalences C).Q.map (d.r.app Y) ≫ (weakEquivalences C).Q.map (d.R.map g)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (weakEquivalences C).Q.map (d.r.naturality g)

omit [HasColimitsOfSize.{0, vC} C] in
/-- The complete inverse cotensor Hom function retains every original Q source arrow. -/
theorem pointedCotensorHoHomEquiv_symm_source {X X' : C} (f : X ⟶ X') (K : PointedSSet.{vC}) (Y : C)
    (h : pointedProjection.obj K ⟶ pointedRightHoSpace d X' Y) :
    (pointedCotensorHoHomEquiv d X K Y).symm
      (h ≫ pointedProjection.map (pointedRightSourceMap d f Y)) =
    (weakEquivalences C).Q.map (d.Q.map f) ≫ (pointedCotensorHoHomEquiv d X' K Y).symm h := by
  apply (pointedCotensorHoHomEquiv d X K Y).injective
  rw [Equiv.apply_symm_apply, pointedCotensorHoHomEquiv_source, Equiv.apply_symm_apply]

omit [HasColimitsOfSize.{0, vC} C] in
/-- The complete inverse cotensor Hom function retains every original R frame target arrow. -/
theorem pointedCotensorHoHomEquiv_symm_target (X : C) (K : PointedSSet.{vC}) {Y Y' : C} (g : Y ⟶ Y')
    (h : pointedProjection.obj K ⟶ pointedRightHoSpace d X Y) :
    (pointedCotensorHoHomEquiv d X K Y').symm
      (h ≫ pointedProjection.map (pointedRightTargetMap d X g)) =
    (pointedCotensorHoHomEquiv d X K Y).symm h ≫
      (weakEquivalences C).Q.map (pointedCotensorMap ((rightFrame d).map g) (𝟙 K)) := by
  apply (pointedCotensorHoHomEquiv d X K Y').injective
  rw [Equiv.apply_symm_apply, pointedCotensorHoHomEquiv_target, Equiv.apply_symm_apply]

omit [HasColimitsOfSize.{0, vC} C] in
/-- The complete inverse cotensor Hom function retains every original pointed weight arrow. -/
theorem pointedCotensorHoHomEquiv_symm_parameter (X : C) {K L : PointedSSet.{vC}} (k : K ⟶ L) (Y : C)
    (h : pointedProjection.obj L ⟶ pointedRightHoSpace d X Y) :
    (pointedCotensorHoHomEquiv d X K Y).symm (pointedProjection.map k ≫ h) =
      (pointedCotensorHoHomEquiv d X L Y).symm h ≫
        (weakEquivalences C).Q.map (pointedCotensorMap (𝟙 ((rightFrame d).obj Y)) k) := by
  apply (pointedCotensorHoHomEquiv d X K Y).injective
  rw [Equiv.apply_symm_apply, pointedCotensorHoHomEquiv_parameter, Equiv.apply_symm_apply]

/-- The full framed ordinary-Ho Hom bijection is natural in every original source map. -/
theorem framedHomEquiv_source {X X' : C} (f : X ⟶ X') (K : PointedSSet.{vC}) (Y : C)
    (h : (weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X') K) ⟶ (weakEquivalences C).Q.obj Y) :
    framedHomEquiv d X K Y
      ((weakEquivalences C).Q.map (pointedTensorMap ((leftFrame d).map f) (𝟙 K)) ≫ h) =
      (weakEquivalences C).Q.map f ≫ framedHomEquiv d X' K Y h := by
  rw [framedHomEquiv_apply, framedHomEquiv_apply, Category.assoc,
    pointedTensorHoHomEquiv_source, Category.assoc, pointedLeftRightIso_source,
    ← Category.assoc, pointedCotensorHoHomEquiv_symm_source,
    ← Category.assoc, qHomotopyIso_inv_naturality, Category.assoc]

/-- The full framed ordinary-Ho Hom bijection is natural in every original target map. -/
theorem framedHomEquiv_target (X : C) (K : PointedSSet.{vC}) {Y Y' : C} (g : Y ⟶ Y')
    (h : (weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X) K) ⟶ (weakEquivalences C).Q.obj Y) :
    framedHomEquiv d X K Y' (h ≫ (weakEquivalences C).Q.map g) =
      framedHomEquiv d X K Y h ≫
        (weakEquivalences C).Q.map (pointedCotensorMap ((rightFrame d).map g) (𝟙 K)) := by
  rw [framedHomEquiv_apply, framedHomEquiv_apply, Category.assoc, rHomotopyIso_naturality,
    ← Category.assoc, pointedTensorHoHomEquiv_target, Category.assoc, pointedLeftRightIso_target,
    ← Category.assoc, pointedCotensorHoHomEquiv_symm_target, Category.assoc]

/-- The full framed ordinary-Ho Hom bijection retains every original pointed weight map. -/
theorem framedHomEquiv_parameter (X : C) {K L : PointedSSet.{vC}} (k : K ⟶ L) (Y : C)
    (h : (weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X) L) ⟶ (weakEquivalences C).Q.obj Y) :
    framedHomEquiv d X K Y
      ((weakEquivalences C).Q.map (pointedTensorMap (𝟙 ((leftFrame d).obj X)) k) ≫ h) =
      framedHomEquiv d X L Y h ≫
        (weakEquivalences C).Q.map (pointedCotensorMap (𝟙 ((rightFrame d).obj Y)) k) := by
  rw [framedHomEquiv_apply, framedHomEquiv_apply, Category.assoc, pointedTensorHoHomEquiv_parameter,
    Category.assoc, pointedCotensorHoHomEquiv_symm_parameter, Category.assoc]

end FullFramedHomNaturality

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

section FramedOrdinaryFunctors

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))
open scoped SSet.modelCategoryQuillen

/-- The full original framed tensor, covariant in every original coefficient map. -/
abbrev framedTensor (K : PointedSSet.{vC}) : C ⥤ C :=
  leftFrame d ⋙ pointedTensorBifunctor.flip.obj K

/-- The full original framed cotensor, covariant in every original coefficient map. -/
abbrev framedCotensor (K : PointedSSet.{vC}) : C ⥤ C :=
  rightFrame d ⋙ pointedCotensorBifunctor.obj (Opposite.op K)

/-- Every original weak arrow gives a weak full framed tensor arrow. -/
theorem framedTensor_map_weak (K : PointedSSet.{vC}) {X Y : C} (f : X ⟶ Y)
    (hf : weakEquivalences C f) : weakEquivalences C ((framedTensor d K).map f) := by
  apply (weakEquivalence_iff_isIso_map_of_isLocalization (weakEquivalences C).Q _).mpr
  let u := (weakEquivalences C).Q.map f
  let t := (weakEquivalences C).Q.map (pointedTensorMap ((leftFrame d).map f) (𝟙 K))
  let _ : IsIso u := Localization.inverts (weakEquivalences C).Q (weakEquivalences C) f hf
  have ht (Z : C) (h : (weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj Y) K) ⟶
      (weakEquivalences C).Q.obj Z) :
      framedHomEquiv d X K Z (t ≫ h) = u ≫ framedHomEquiv d Y K Z h :=
    framedHomEquiv_source d f K Z h
  have hinj (Z : C) : Function.Injective (fun h :
      (weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj Y) K) ⟶ (weakEquivalences C).Q.obj Z => t ≫ h) := by
    intro a b hab
    change t ≫ a = t ≫ b at hab
    apply (framedHomEquiv d Y K Z).injective
    apply (cancel_epi u).mp
    rw [← ht Z a, ← ht Z b, hab]
  let g := (framedHomEquiv d Y K (pointedTensor ((leftFrame d).obj X) K)).symm
    (inv u ≫ framedHomEquiv d X K (pointedTensor ((leftFrame d).obj X) K) (𝟙 _))
  have hg : t ≫ g = 𝟙 _ := by
    apply (framedHomEquiv d X K (pointedTensor ((leftFrame d).obj X) K)).injective
    rw [ht]
    dsimp only [g]
    rw [Equiv.apply_symm_apply, IsIso.hom_inv_id_assoc]
  have gh : g ≫ t = 𝟙 _ := by
    apply hinj (pointedTensor ((leftFrame d).obj Y) K)
    change t ≫ (g ≫ t) = t ≫ 𝟙 _
    rw [← Category.assoc, hg, Category.id_comp, Category.comp_id]
  exact ⟨g, hg, gh⟩

/-- Every original weak arrow gives a weak full framed cotensor arrow. -/
theorem framedCotensor_map_weak (K : PointedSSet.{vC}) {Y Y' : C} (f : Y ⟶ Y')
    (hf : weakEquivalences C f) : weakEquivalences C ((framedCotensor d K).map f) := by
  apply (weakEquivalence_iff_isIso_map_of_isLocalization (weakEquivalences C).Q _).mpr
  let u := (weakEquivalences C).Q.map f
  let t := (weakEquivalences C).Q.map (pointedCotensorMap ((rightFrame d).map f) (𝟙 K))
  let _ : IsIso u := Localization.inverts (weakEquivalences C).Q (weakEquivalences C) f hf
  have ht (X : C) (h : (weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X) K) ⟶
      (weakEquivalences C).Q.obj Y) :
      framedHomEquiv d X K Y' (h ≫ u) = framedHomEquiv d X K Y h ≫ t :=
    framedHomEquiv_target d X K f h
  have hinj (X : C) : Function.Injective (fun h :
      (weakEquivalences C).Q.obj X ⟶ (weakEquivalences C).Q.obj (pointedCotensor ((rightFrame d).obj Y) K) => h
        ≫ t) := by
    intro a b hab
    change a ≫ t = b ≫ t at hab
    apply (framedHomEquiv d X K Y).symm.injective
    apply (cancel_mono u).mp
    apply (framedHomEquiv d X K Y').injective
    rw [ht, ht, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hab]
  let g := framedHomEquiv d (pointedCotensor ((rightFrame d).obj Y') K) K Y
    ((framedHomEquiv d (pointedCotensor ((rightFrame d).obj Y') K) K Y').symm (𝟙 _) ≫ inv u)
  have gt : g ≫ t = 𝟙 _ := by
    dsimp only [g]
    rw [← ht]
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Equiv.apply_symm_apply]
  have tg : t ≫ g = 𝟙 _ := by
    apply hinj (pointedCotensor ((rightFrame d).obj Y) K)
    change (t ≫ g) ≫ t = 𝟙 _ ≫ t
    rw [Category.assoc, gt, Category.comp_id, Category.id_comp]
  exact ⟨g, tg, gt⟩

end FramedOrdinaryFunctors

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

section FullOrdinaryAdjunction

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C]
  (d : GeneratedFunctorialReplacements.Data (C := C)) (K : PointedSSet.{vC})
open scoped SSet.modelCategoryQuillen

/-- The original full framed tensor descends to every object and morphism of the ordinary homotopy category. -/
def tensorHo : (weakEquivalences C).Localization ⥤ (weakEquivalences C).Localization :=
  Localization.Construction.lift (framedTensor d K ⋙ (weakEquivalences C).Q)
    (fun {_ _} f hf => Localization.inverts (weakEquivalences C).Q (weakEquivalences C)
      _ (framedTensor_map_weak d K f hf))

/-- The original full framed cotensor descends to every object and morphism of the ordinary homotopy category. -/
def cotensorHo : (weakEquivalences C).Localization ⥤ (weakEquivalences C).Localization :=
  Localization.Construction.lift (framedCotensor d K ⋙ (weakEquivalences C).Q)
    (fun {_ _} f hf => Localization.inverts (weakEquivalences C).Q (weakEquivalences C)
      _ (framedCotensor_map_weak d K f hf))

/-- The full tensor descent retains the same entire original framed functor. -/
theorem tensorHo_projection :
    (weakEquivalences C).Q ⋙ tensorHo d K = framedTensor d K ⋙ (weakEquivalences C).Q :=
  Localization.Construction.fac _ _

/-- The full cotensor descent retains the same entire original framed functor. -/
theorem cotensorHo_projection :
    (weakEquivalences C).Q ⋙ cotensorHo d K = framedCotensor d K ⋙ (weakEquivalences C).Q :=
  Localization.Construction.fac _ _

/-- Every original tensor arrow has its unchanged localization image. -/
theorem tensorHo_map {X Y : C} (f : X ⟶ Y) :
    (tensorHo d K).map ((weakEquivalences C).Q.map f) =
      (weakEquivalences C).Q.map (pointedTensorMap ((leftFrame d).map f) (𝟙 K)) :=
  CategoryTheory.Functor.congr_hom (tensorHo_projection d K) f

/-- Every original cotensor arrow has its unchanged localization image. -/
theorem cotensorHo_map {X Y : C} (f : X ⟶ Y) :
    (cotensorHo d K).map ((weakEquivalences C).Q.map f) =
      (weakEquivalences C).Q.map (pointedCotensorMap ((rightFrame d).map f) (𝟙 K)) :=
  CategoryTheory.Functor.congr_hom (cotensorHo_projection d K) f

/-- The full framed Hom equivalence on every pair of original localization objects. -/
def homEquivHo (X Y : (weakEquivalences C).Localization) :
    ((tensorHo d K).obj X ⟶ Y) ≃ (X ⟶ (cotensorHo d K).obj Y) := by
  rcases X with ⟨⟨X⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  exact framedHomEquiv d X K Y

/-- The complete Ho Hom function retains its original framing comparison on every original object. -/
theorem homEquivHo_original (X Y : C) :
    homEquivHo d K ((weakEquivalences C).Q.obj X) ((weakEquivalences C).Q.obj Y) =
      framedHomEquiv d X K Y := rfl

/-- The entire Hom function is natural in every ordinary-Ho source arrow, including formal inverses. -/
theorem homEquivHo_source {X X' : (weakEquivalences C).Localization} (f : X ⟶ X')
    (Y : (weakEquivalences C).Localization) (h : (tensorHo d K).obj X' ⟶ Y) :
    homEquivHo d K X Y ((tensorHo d K).map f ≫ h) = f ≫ homEquivHo d K X' Y h := by
  let γ := (weakEquivalences C).Q
  let F₁ := (tensorHo d K).op ⋙ yoneda.obj Y
  let F₂ := yoneda.obj ((cotensorHo d K).obj Y)
  let τ₀ : γ.op ⋙ F₁ ⟶ γ.op ⋙ F₂ :=
    { app X := ↾(homEquivHo d K (γ.obj X.unop) Y)
      naturality {X X'} g := by
        ext a
        rcases Y with ⟨⟨Y⟩⟩
        change framedHomEquiv d X'.unop K Y ((tensorHo d K).map (γ.map g.unop) ≫ a) =
          γ.map g.unop ≫ framedHomEquiv d X.unop K Y a
        rw [tensorHo_map]
        exact framedHomEquiv_source d g.unop K Y a }
  let τ : F₁ ⟶ F₂ := Localization.liftNatTrans γ.op (weakEquivalences C).op
    (γ.op ⋙ F₁) (γ.op ⋙ F₂) F₁ F₂ τ₀
  have hτ (X : C) : τ.app (Opposite.op (γ.obj X)) = ↾(homEquivHo d K (γ.obj X) Y) := by
    change (Localization.liftNatTrans γ.op (weakEquivalences C).op
      (γ.op ⋙ F₁) (γ.op ⋙ F₂) F₁ F₂ τ₀).app (γ.op.obj (Opposite.op X)) = _
    rw [Localization.liftNatTrans_app]
    rfl
  rcases X with ⟨⟨X⟩⟩
  rcases X' with ⟨⟨X'⟩⟩
  have hn := τ.naturality_apply f.op h
  change (τ.app (Opposite.op (γ.obj X))) ((tensorHo d K).map f ≫ h) =
    f ≫ (τ.app (Opposite.op (γ.obj X'))) h at hn
  rw [hτ X, hτ X'] at hn
  exact hn

/-- The entire Hom function is natural in every ordinary-Ho target arrow, including formal inverses. -/
theorem homEquivHo_target (X : (weakEquivalences C).Localization)
    {Y Y' : (weakEquivalences C).Localization} (g : Y ⟶ Y') (h : (tensorHo d K).obj X ⟶ Y) :
    homEquivHo d K X Y' (h ≫ g) = homEquivHo d K X Y h ≫ (cotensorHo d K).map g := by
  let γ := (weakEquivalences C).Q
  let F₁ := coyoneda.obj (Opposite.op ((tensorHo d K).obj X))
  let F₂ := cotensorHo d K ⋙ coyoneda.obj (Opposite.op X)
  let τ₀ : γ ⋙ F₁ ⟶ γ ⋙ F₂ :=
    { app Y := ↾(homEquivHo d K X (γ.obj Y))
      naturality {Y Y'} f := by
        ext a
        rcases X with ⟨⟨X⟩⟩
        change framedHomEquiv d X K Y' (a ≫ γ.map f) =
          framedHomEquiv d X K Y a ≫ (cotensorHo d K).map (γ.map f)
        rw [cotensorHo_map]
        exact framedHomEquiv_target d X K f a }
  let τ : F₁ ⟶ F₂ := Localization.liftNatTrans γ (weakEquivalences C)
    (γ ⋙ F₁) (γ ⋙ F₂) F₁ F₂ τ₀
  have hτ (Y : C) : τ.app (γ.obj Y) = ↾(homEquivHo d K X (γ.obj Y)) := by
    change (Localization.liftNatTrans γ (weakEquivalences C)
      (γ ⋙ F₁) (γ ⋙ F₂) F₁ F₂ τ₀).app (γ.obj Y) = _
    rw [Localization.liftNatTrans_app]
    rfl
  rcases Y with ⟨⟨Y⟩⟩
  rcases Y' with ⟨⟨Y'⟩⟩
  have hn := τ.naturality_apply g h
  change (τ.app (γ.obj Y')) (h ≫ g) = (τ.app (γ.obj Y)) h ≫ (cotensorHo d K).map g at hn
  rw [hτ Y, hτ Y'] at hn
  exact hn

/-- The actual framing-derived ordinary-Ho scalar tensor and cotensor form a full adjunction. -/
def ordinaryAdjunction : tensorHo d K ⊣ cotensorHo d K :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquivHo d K
      homEquiv_naturality_left_symm := by
        intro X X' Y f h
        apply (homEquivHo d K X Y).injective
        rw [Equiv.apply_symm_apply, homEquivHo_source, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro X Y Y' f g
        exact homEquivHo_target d K X g f }

end FullOrdinaryAdjunction

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C]
  (d : GeneratedFunctorialReplacements.Data (C := C)) (K : PointedSSet.{vC})

/-- The full ordinary adjunction retains the same entire original Hom function on every Ho object. -/
theorem ordinaryAdjunction_homEquiv (X Y : (weakEquivalences C).Localization)
    (f : (tensorHo d K).obj X ⟶ Y) :
    (ordinaryAdjunction d K).homEquiv X Y f = homEquivHo d K X Y f := by
  unfold ordinaryAdjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

/-- The original cosimplicial codegeneracy and same degree-zero Q identification form a weak retraction. -/
theorem leftCylinder_projection_weak (X : C) :
    weakEquivalences C (((leftFrame d).obj X).σ (0 : Fin 1) ≫
      (leftZeroIso d).hom.app X) :=
  (weakEquivalences C).comp_mem _ _
    (leftFrame_map_weak d X (SimplexCategory.σ (0 : Fin 1)))
    ((weakEquivalences C).of_isIso _)

/-- The actual original degree-one coproduct inclusion at the same Q endpoint is a cofibration. -/
theorem leftCylinder_inclusion_cofibration (X : C) :
    cofibrations C (coprod.desc
      ((leftZeroIso d).inv.app X ≫ ((leftFrame d).obj X).δ (0 : Fin 2))
      ((leftZeroIso d).inv.app X ≫ ((leftFrame d).obj X).δ (1 : Fin 2))) := by
  let A := (leftFrame d).obj X
  let e := (leftZeroIso d).app X
  have hA : cofibrations C (SimplexCategory.ReedyBoundaries.cosimplicialLatchingMap A ⦋1⦌) :=
    leftFrame_latching_cofibration d X ⦋1⦌
  let _ : IsIso (coprod.map e.inv e.inv) := by infer_instance
  have hpair : cofibrations C (coprod.desc (A.δ (0 : Fin 2)) (A.δ (1 : Fin 2))) :=
    FramingDegreeOneBoundaries.cosimplicialLatchingOneIso_inv_map A ▸
      (cofibrations C).comp_mem _ _ ((cofibrations C).of_isIso _) hA
  have he : coprod.map e.inv e.inv ≫ coprod.desc (A.δ (0 : Fin 2)) (A.δ (1 : Fin 2)) =
      coprod.desc (e.inv ≫ A.δ (0 : Fin 2)) (e.inv ≫ A.δ (1 : Fin 2)) :=
    coprod.map_desc (A.δ (0 : Fin 2)) (A.δ (1 : Fin 2)) e.inv e.inv
  exact he ▸ (cofibrations C).comp_mem _ _ ((cofibrations C).of_isIso _) hpair

/-- The original simplicial degeneracy and same degree-zero R identification form a weak section. -/
theorem rightPath_section_weak (X : C) :
    weakEquivalences C ((rightZeroIso d).hom.app X ≫
      ((rightFrame d).obj X).σ (0 : Fin 1)) :=
  (weakEquivalences C).comp_mem _ _ ((weakEquivalences C).of_isIso _)
    (rightFrame_map_weak d X (SimplexCategory.σ (0 : Fin 1)).op)

/-- The actual original degree-one ordered product projection to the same R endpoint is a fibration. -/
theorem rightPath_projection_fibration (X : C) :
    fibrations C (prod.lift
      (((rightFrame d).obj X).δ (0 : Fin 2) ≫ (rightZeroIso d).inv.app X)
      (((rightFrame d).obj X).δ (1 : Fin 2) ≫ (rightZeroIso d).inv.app X)) := by
  let B := (rightFrame d).obj X
  let e := (rightZeroIso d).app X
  have hB : fibrations C (SimplexCategory.ReedyBoundaries.simplicialMatchingMap B (Opposite.op ⦋1⦌)) :=
    rightFrame_matching_fibration d X (Opposite.op ⦋1⦌)
  let _ : IsIso (prod.map e.inv e.inv) := by infer_instance
  rw [← prod.lift_map, ← FramingDegreeOneBoundaries.simplicialMatchingOneIso_map_hom B]
  exact (fibrations C).comp_mem _ _
    ((fibrations C).comp_mem _ _ hB ((fibrations C).of_isIso _)) ((fibrations C).of_isIso _)

/-- The actual original-Q good cylinder uses the same frame object and original structure maps. -/
def leftCylinder (X : C) : Cylinder (d.Q.obj X) := by
  let A := (leftFrame d).obj X
  let e := ((leftZeroIso d).app X).symm
  letI : WeakEquivalence (A.σ (0 : Fin 1) ≫ e.inv) :=
    (weakEquivalence_iff _).mpr (leftCylinder_projection_weak d X)
  exact ResolutionHomComplex.LeftPiZero.cylinder A e

/-- The actual original-R path object uses the same frame object and original structure maps. -/
def rightPath (X : C) : PathObject (d.R.obj X) := by
  let B := (rightFrame d).obj X
  let e := (rightZeroIso d).app X
  letI : WeakEquivalence (e.hom ≫ B.σ (0 : Fin 1)) :=
    (weakEquivalence_iff _).mpr (rightPath_section_weak d X)
  exact ResolutionHomComplex.RightPiZero.path B e

/-- The same original degree-one coproduct map makes the actual cylinder good. -/
instance leftCylinder_isGood (X : C) : (leftCylinder d X).IsGood where
  cofibration_i := by
    change Cofibration (coprod.desc
      ((leftZeroIso d).inv.app X ≫ ((leftFrame d).obj X).δ (0 : Fin 2))
      ((leftZeroIso d).inv.app X ≫ ((leftFrame d).obj X).δ (1 : Fin 2)))
    exact (cofibration_iff _).mpr (leftCylinder_inclusion_cofibration d X)

/-- The same original degree-one product map makes the actual path object good. -/
instance rightPath_isGood (X : C) : (rightPath d X).IsGood where
  fibration_p := by
    change Fibration (prod.lift
      (((rightFrame d).obj X).δ (0 : Fin 2) ≫ (rightZeroIso d).inv.app X)
      (((rightFrame d).obj X).δ (1 : Fin 2) ≫ (rightZeroIso d).inv.app X))
    exact (fibration_iff _).mpr (rightPath_projection_fibration d X)

/-- The actual cylinder carrier is the original first cosimplicial frame degree. -/
theorem leftCylinder_I (X : C) : (leftCylinder d X).I = ((leftFrame d).obj X).obj ⦋1⦌ := rfl

/-- The first original cylinder inclusion retains the original coface zero and Q identification. -/
theorem leftCylinder_i₀ (X : C) :
    (leftCylinder d X).i₀ = (leftZeroIso d).inv.app X ≫
      ((leftFrame d).obj X).δ (0 : Fin 2) := rfl

/-- The second original cylinder inclusion retains the original coface one and Q identification. -/
theorem leftCylinder_i₁ (X : C) :
    (leftCylinder d X).i₁ = (leftZeroIso d).inv.app X ≫
      ((leftFrame d).obj X).δ (1 : Fin 2) := rfl

/-- The actual cylinder retraction retains the original codegeneracy and Q identification. -/
theorem leftCylinder_π (X : C) :
    (leftCylinder d X).π = ((leftFrame d).obj X).σ (0 : Fin 1) ≫
      (leftZeroIso d).hom.app X := rfl

/-- The actual path carrier is the original first simplicial frame degree. -/
theorem rightPath_P (X : C) :
    (rightPath d X).P = ((rightFrame d).obj X).obj (Opposite.op ⦋1⦌) := rfl

/-- The first original path projection retains face zero and the R identification. -/
theorem rightPath_p₀ (X : C) :
    (rightPath d X).p₀ = ((rightFrame d).obj X).δ (0 : Fin 2) ≫
      (rightZeroIso d).inv.app X := rfl

/-- The second original path projection retains face one and the R identification. -/
theorem rightPath_p₁ (X : C) :
    (rightPath d X).p₁ = ((rightFrame d).obj X).δ (1 : Fin 2) ≫
      (rightZeroIso d).inv.app X := rfl

/-- The actual path section retains the original degeneracy and R identification. -/
theorem rightPath_ι (X : C) :
    (rightPath d X).ι = (rightZeroIso d).hom.app X ≫
      ((rightFrame d).obj X).σ (0 : Fin 1) := rfl

/-- Every original Q morphism preserves the first actual chosen cylinder inclusion. -/
theorem leftCylinder_i₀_naturality {X Y : C} (f : X ⟶ Y) :
    d.Q.map f ≫ (leftCylinder d Y).i₀ =
      (leftCylinder d X).i₀ ≫ ((leftFrame d).map f).app ⦋1⦌ :=
  ((leftZeroIso d).inv ≫ Functor.whiskerLeft (leftFrame d)
    ((evaluation SimplexCategory C).map (SimplexCategory.δ (0 : Fin 2)))).naturality f

/-- Every original Q morphism preserves the second actual chosen cylinder inclusion. -/
theorem leftCylinder_i₁_naturality {X Y : C} (f : X ⟶ Y) :
    d.Q.map f ≫ (leftCylinder d Y).i₁ =
      (leftCylinder d X).i₁ ≫ ((leftFrame d).map f).app ⦋1⦌ :=
  ((leftZeroIso d).inv ≫ Functor.whiskerLeft (leftFrame d)
    ((evaluation SimplexCategory C).map (SimplexCategory.δ (1 : Fin 2)))).naturality f

/-- Every original Q morphism preserves the actual chosen cylinder retraction. -/
theorem leftCylinder_π_naturality {X Y : C} (f : X ⟶ Y) :
    ((leftFrame d).map f).app ⦋1⦌ ≫ (leftCylinder d Y).π =
      (leftCylinder d X).π ≫ d.Q.map f :=
  (Functor.whiskerLeft (leftFrame d)
    ((evaluation SimplexCategory C).map (SimplexCategory.σ (0 : Fin 1))) ≫
      (leftZeroIso d).hom).naturality f

/-- Every original R morphism preserves the first actual chosen path projection. -/
theorem rightPath_p₀_naturality {X Y : C} (f : X ⟶ Y) :
    ((rightFrame d).map f).app (Opposite.op ⦋1⦌) ≫ (rightPath d Y).p₀ =
      (rightPath d X).p₀ ≫ d.R.map f :=
  (Functor.whiskerLeft (rightFrame d)
    ((evaluation SimplexCategoryᵒᵖ C).map (SimplexCategory.δ (0 : Fin 2)).op) ≫
      (rightZeroIso d).inv).naturality f

/-- Every original R morphism preserves the second actual chosen path projection. -/
theorem rightPath_p₁_naturality {X Y : C} (f : X ⟶ Y) :
    ((rightFrame d).map f).app (Opposite.op ⦋1⦌) ≫ (rightPath d Y).p₁ =
      (rightPath d X).p₁ ≫ d.R.map f :=
  (Functor.whiskerLeft (rightFrame d)
    ((evaluation SimplexCategoryᵒᵖ C).map (SimplexCategory.δ (1 : Fin 2)).op) ≫
      (rightZeroIso d).inv).naturality f

/-- Every original R morphism preserves the actual chosen path section. -/
theorem rightPath_ι_naturality {X Y : C} (f : X ⟶ Y) :
    d.R.map f ≫ (rightPath d Y).ι =
      (rightPath d X).ι ≫ ((rightFrame d).map f).app (Opposite.op ⦋1⦌) :=
  ((rightZeroIso d).hom ≫ Functor.whiskerLeft (rightFrame d)
    ((evaluation SimplexCategoryᵒᵖ C).map (SimplexCategory.σ (0 : Fin 1)).op)).naturality f


end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))
open scoped SSet.modelCategoryQuillen

/-- Every original weight arrow acts naturally on the entire ordinary homotopy category. -/
def tensorWeightMap {K L : PointedSSet.{vC}} (k : K ⟶ L) : tensorHo d K ⟶ tensorHo d L :=
  Localization.liftNatTrans (weakEquivalences C).Q (weakEquivalences C)
    ((weakEquivalences C).Q ⋙ tensorHo d K) ((weakEquivalences C).Q ⋙ tensorHo d L)
    (tensorHo d K) (tensorHo d L)
    { app X := (weakEquivalences C).Q.map (pointedTensorMap (𝟙 ((leftFrame d).obj X)) k)
      naturality {X Y} f := by
        change (tensorHo d K).map ((weakEquivalences C).Q.map f) ≫
            (weakEquivalences C).Q.map (pointedTensorMap (𝟙 ((leftFrame d).obj Y)) k) =
          (weakEquivalences C).Q.map (pointedTensorMap (𝟙 ((leftFrame d).obj X)) k) ≫
            (tensorHo d L).map ((weakEquivalences C).Q.map f)
        rw [tensorHo_map, tensorHo_map]
        change (weakEquivalences C).Q.map (pointedTensorMap ((leftFrame d).map f) (𝟙 K)) ≫
            (weakEquivalences C).Q.map (pointedTensorMap (𝟙 ((leftFrame d).obj Y)) k) =
          (weakEquivalences C).Q.map (pointedTensorMap (𝟙 ((leftFrame d).obj X)) k) ≫
            (weakEquivalences C).Q.map (pointedTensorMap ((leftFrame d).map f) (𝟙 L))
        rw [← CategoryTheory.Functor.map_comp,
          ← CategoryTheory.Functor.map_comp, ← pointedTensorMap_comp, ← pointedTensorMap_comp]
        simp }

/-- The full ordinary weight action reads back the original point-set frame map. -/
theorem tensorWeightMap_app {K L : PointedSSet.{vC}} (k : K ⟶ L) (X : C) :
    (tensorWeightMap d k).app ((weakEquivalences C).Q.obj X) =
      (weakEquivalences C).Q.map (pointedTensorMap (𝟙 ((leftFrame d).obj X)) k) := by
  rw [tensorWeightMap, Localization.liftNatTrans_app]
  rfl

/-- All weights and all coefficient homotopy arrows form the original tensor bifunctor. -/
def tensorWeightFunctor : PointedSSet.{vC} ⥤
    ((weakEquivalences C).Localization ⥤ (weakEquivalences C).Localization) where
  obj K := tensorHo d K
  map k := tensorWeightMap d k
  map_id K := by
    apply NatTrans.ext
    funext X
    rcases X with ⟨⟨X⟩⟩
    change (tensorWeightMap d (𝟙 K)).app ((weakEquivalences C).Q.obj X) =
      𝟙 ((weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X) K))
    rw [tensorWeightMap_app]
    rw [pointedTensorMap_id, CategoryTheory.Functor.map_id]
  map_comp k l := by
    apply NatTrans.ext
    funext X
    rcases X with ⟨⟨X⟩⟩
    change (tensorWeightMap d (k ≫ l)).app ((weakEquivalences C).Q.obj X) =
      (tensorWeightMap d k).app ((weakEquivalences C).Q.obj X) ≫
        (tensorWeightMap d l).app ((weakEquivalences C).Q.obj X)
    rw [tensorWeightMap_app]
    change (weakEquivalences C).Q.map (pointedTensorMap (𝟙 ((leftFrame d).obj X)) (k ≫ l)) =
      (tensorWeightMap d k).app ((weakEquivalences C).Q.obj X) ≫
        (tensorWeightMap d l).app ((weakEquivalences C).Q.obj X)
    rw [tensorWeightMap_app, tensorWeightMap_app]
    change (weakEquivalences C).Q.map (pointedTensorMap (𝟙 ((leftFrame d).obj X)) (k ≫ l)) =
      (weakEquivalences C).Q.map (pointedTensorMap (𝟙 ((leftFrame d).obj X)) k) ≫
        (weakEquivalences C).Q.map (pointedTensorMap (𝟙 ((leftFrame d).obj X)) l)
    rw [← CategoryTheory.Functor.map_comp, ← pointedTensorMap_comp, Category.id_comp]

/-- An original weak weight arrow gives an isomorphism of the full tensor functors. -/
theorem tensorWeightMap_isIso {K L : PointedSSet.{vC}} (k : K ⟶ L)
    (hk : weakEquivalences PointedSSet.{vC} k) : IsIso (tensorWeightMap d k) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro X
  rcases X with ⟨⟨X⟩⟩
  change IsIso ((tensorWeightMap d k).app ((weakEquivalences C).Q.obj X))
  rw [tensorWeightMap_app]
  let _ : (pointedTensorHomAdjunction ((leftFrame d).obj X)).IsQuillenAdjunction :=
    originalPointedTensor_isQuillen d X
  let _ : IsCofibrant K := pointedSSet_isCofibrant K
  let _ : IsCofibrant L := pointedSSet_isCofibrant L
  let _ : WeakEquivalence k := (weakEquivalence_iff _).mpr hk
  have hw : WeakEquivalence (pointedTensorMap (𝟙 ((leftFrame d).obj X)) k) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := pointedTensorHomAdjunction ((leftFrame d).obj X)) k
  exact Localization.inverts (weakEquivalences C).Q (weakEquivalences C) _
    ((weakEquivalence_iff _).mp hw)

/-- The original tensor is defined on every pointed-space homotopy arrow and every coefficient homotopy arrow. -/
def tensorAction : PointedSpaceHo.{vC} ⥤
    ((weakEquivalences C).Localization ⥤ (weakEquivalences C).Localization) :=
  Localization.Construction.lift (tensorWeightFunctor d)
    (fun {_ _} k hk => tensorWeightMap_isIso d k hk)

/-- The entire scalar projection is the same original tensor-weight functor. -/
theorem tensorAction_projection : pointedProjection ⋙ tensorAction d = tensorWeightFunctor d :=
  Localization.Construction.fac _ _

/-- Every original weight object retains its actual whole coefficient homotopy functor. -/
theorem tensorAction_obj (K : PointedSSet.{vC}) :
    (tensorAction d).obj (pointedProjection.obj K) = tensorHo d K := rfl

/-- Every original scalar arrow retains the whole natural frame map and its two carrier equality legs. -/
theorem tensorAction_map {K L : PointedSSet.{vC}} (k : K ⟶ L) :
    (tensorAction d).map (pointedProjection.map k) =
      eqToHom (tensorAction_obj d K) ≫ tensorWeightMap d k ≫
        eqToHom (tensorAction_obj d L).symm := by
  simpa only [CategoryTheory.Functor.comp_map, tensorWeightFunctor]
    using! CategoryTheory.Functor.congr_hom (tensorAction_projection d) k

/-- Each original weight restriction acts on the same whole ordinary cotensor functor. -/
def cotensorWeightMap {K L : PointedSSet.{vC}} (k : K ⟶ L) : cotensorHo d L ⟶ cotensorHo d K :=
  Localization.liftNatTrans (weakEquivalences C).Q (weakEquivalences C)
    ((weakEquivalences C).Q ⋙ cotensorHo d L) ((weakEquivalences C).Q ⋙ cotensorHo d K)
    (cotensorHo d L) (cotensorHo d K)
    { app Y := (weakEquivalences C).Q.map (pointedCotensorMap (𝟙 ((rightFrame d).obj Y)) k)
      naturality {X Y} f := by
        change (cotensorHo d L).map ((weakEquivalences C).Q.map f) ≫
            (weakEquivalences C).Q.map (pointedCotensorMap (𝟙 ((rightFrame d).obj Y)) k) =
          (weakEquivalences C).Q.map (pointedCotensorMap (𝟙 ((rightFrame d).obj X)) k) ≫
            (cotensorHo d K).map ((weakEquivalences C).Q.map f)
        rw [cotensorHo_map, cotensorHo_map]
        change (weakEquivalences C).Q.map (pointedCotensorMap ((rightFrame d).map f) (𝟙 L)) ≫
            (weakEquivalences C).Q.map (pointedCotensorMap (𝟙 ((rightFrame d).obj Y)) k) =
          (weakEquivalences C).Q.map (pointedCotensorMap (𝟙 ((rightFrame d).obj X)) k) ≫
            (weakEquivalences C).Q.map (pointedCotensorMap ((rightFrame d).map f) (𝟙 K))
        rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
          ← pointedCotensorMap_comp, ← pointedCotensorMap_comp]
        simp }

/-- The full ordinary weight restriction retains its original point-set frame map. -/
theorem cotensorWeightMap_app {K L : PointedSSet.{vC}} (k : K ⟶ L) (X : C) :
    (cotensorWeightMap d k).app ((weakEquivalences C).Q.obj X) =
      (weakEquivalences C).Q.map (pointedCotensorMap (𝟙 ((rightFrame d).obj X)) k) := by
  rw [cotensorWeightMap, Localization.liftNatTrans_app]
  rfl

/-- The whole scalar Hom function is natural in every original weight arrow on all coefficient Ho objects. -/
theorem homEquivHo_weight {K L : PointedSSet.{vC}} (k : K ⟶ L)
    (X Y : (weakEquivalences C).Localization) (h : (tensorHo d L).obj X ⟶ Y) :
    homEquivHo d K X Y ((tensorWeightMap d k).app X ≫ h) =
      homEquivHo d L X Y h ≫ (cotensorWeightMap d k).app Y := by
  rcases X with ⟨⟨X⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  change framedHomEquiv d X K Y
      ((tensorWeightMap d k).app ((weakEquivalences C).Q.obj X) ≫ h) =
    framedHomEquiv d X L Y h ≫ (cotensorWeightMap d k).app ((weakEquivalences C).Q.obj Y)
  rw [tensorWeightMap_app, cotensorWeightMap_app]
  exact framedHomEquiv_parameter d X k Y h

/-- The original cotensor for an arbitrary pointed homotopy-space object. -/
def cotensorActionObj (K : PointedSpaceHo.{vC}) :
    (weakEquivalences C).Localization ⥤ (weakEquivalences C).Localization :=
  cotensorHo d ((Localization.Construction.objEquiv (weakEquivalences PointedSSet.{vC})).symm K)

/-- Every scalar homotopy object retains the ordinary framing adjunction from the original factories. -/
def tensorActionAdjunction (K : PointedSpaceHo.{vC}) :
    (tensorAction d).obj K ⊣ cotensorActionObj d K := by
  rcases K with ⟨⟨K⟩⟩
  exact ordinaryAdjunction d K

/-- The original cotensor functors act contravariantly on all pointed-space Ho arrows via their actual mates. -/
def cotensorAction : PointedSpaceHo.{vC}ᵒᵖ ⥤
    ((weakEquivalences C).Localization ⥤ (weakEquivalences C).Localization) where
  obj K := cotensorActionObj d K.unop
  map k := conjugateEquiv (tensorActionAdjunction d _) (tensorActionAdjunction d _)
    ((tensorAction d).map k.unop)
  map_id K := by
    change conjugateEquiv (tensorActionAdjunction d K.unop) (tensorActionAdjunction d K.unop)
      ((tensorAction d).map (𝟙 K.unop)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, conjugateEquiv_id]
  map_comp {K L M} k l := by
    change conjugateEquiv (tensorActionAdjunction d K.unop) (tensorActionAdjunction d M.unop)
        ((tensorAction d).map (l.unop ≫ k.unop)) =
      conjugateEquiv (tensorActionAdjunction d K.unop) (tensorActionAdjunction d L.unop)
          ((tensorAction d).map k.unop) ≫
        conjugateEquiv (tensorActionAdjunction d L.unop) (tensorActionAdjunction d M.unop)
          ((tensorAction d).map l.unop)
    rw [CategoryTheory.Functor.map_comp, conjugateEquiv_comp]

/-- The arbitrary-scalar right adjoint has the same original cotensor on every original weight. -/
theorem cotensorActionObj_original (K : PointedSSet.{vC}) :
    cotensorActionObj d (pointedProjection.obj K) = cotensorHo d K := rfl

/-- Every original scalar adjunction is retained as a complete adjunction record. -/
theorem tensorActionAdjunction_original (K : PointedSSet.{vC}) :
    tensorActionAdjunction d (pointedProjection.obj K) = ordinaryAdjunction d K := rfl

end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction.FrameCoherence

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  (d : GeneratedFunctorialReplacements.Data (C := C))
open scoped SSet.modelCategoryQuillen

/-- An actual weak augmentation makes the induced left-Hom maps equal through the genuine HFC span. -/
theorem leftHomPrecomp_eq_of_augmentation
    {A B : CosimplicialObject C}
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hB : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy B n))
    {Z : C} [IsCofibrant Z] (β : B ⟶ (CosimplicialObject.const C).obj Z)
    (hβ : ∀ n, weakEquivalences C (β.app n))
    (a b : A ⟶ B) (hab : a ≫ β = b ≫ β) (Y : C) :
    pointedProjection.map (pointedHomPrecomp a ((SimplicialObject.const C).obj (d.R.obj Y))) =
      pointedProjection.map (pointedHomPrecomp b ((SimplicialObject.const C).obj (d.R.obj Y))) := by
  let B' := (rightFrame d).obj Y
  let ρ := (rightResolution d).app Y
  have hβPointed : weakEquivalences PointedSSet.{vC} (pointedHomPrecomp β B') := by
    change weakEquivalences SSet.{vC} (ResolutionHomComplex.fromAugmentation β B')
    exact (weakEquivalence_iff _).mp
      (GeneratedFrameHomComparison.fromAugmentation_weak B B' β hB
        (rightFrame_matching_fibration d Y) hβ)
  let _ : IsIso (pointedProjection.map (pointedHomPrecomp β B')) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC}) _ hβPointed
  have hTwo : pointedProjection.map (pointedHomPrecomp a B') =
      pointedProjection.map (pointedHomPrecomp b B') := by
    apply (cancel_epi (pointedProjection.map (pointedHomPrecomp β B'))).mp
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← pointedHomPrecomp_comp, ← pointedHomPrecomp_comp, hab]
  have hρA : weakEquivalences PointedSSet.{vC} (pointedHomPostcomp A ρ) := by
    change weakEquivalences SSet.{vC} (ResolutionHomComplex.fromCoaugmentation A ρ)
    let _ : IsFibrant (d.R.obj Y) := d.r_fibrant Y
    exact (weakEquivalence_iff _).mp
      (GeneratedFrameHomComparison.fromCoaugmentation_weak A B' ρ hA
        (rightFrame_matching_fibration d Y) (rightResolution_weak d Y))
  let _ : IsIso (pointedProjection.map (pointedHomPostcomp A ρ)) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC}) _ hρA
  apply (cancel_mono (pointedProjection.map (pointedHomPostcomp A ρ))).mp
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    pointedHomPrecomp_postcomp, pointedHomPrecomp_postcomp,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hTwo]

/-- The entire canonical augmentation of a cosimplicial object retains the unique original zero-degree operator. -/
def augmentation (A : CosimplicialObject C) : A ⟶ (CosimplicialObject.const C).obj (A.obj ⦋0⦌) where
  app n := A.map (SimplexCategory.isTerminalZero.from n)
  naturality {n m} f := by
    change A.map f ≫ A.map (SimplexCategory.isTerminalZero.from m) =
      A.map (SimplexCategory.isTerminalZero.from n) ≫ 𝟙 (A.obj ⦋0⦌)
    rw [← CategoryTheory.Functor.map_comp, Category.comp_id]
    exact A.congr_map (SimplexCategory.isTerminalZero.hom_ext _ _)

omit [ModelCategory C] [HasZeroObject C] in
/-- The canonical augmentation retains every original cosimplicial transformation and its degree-zero map. -/
theorem augmentation_square {A B : CosimplicialObject C} (a : A ⟶ B) :
    a ≫ augmentation B = augmentation A ≫ (CosimplicialObject.const C).map (a.app ⦋0⦌) := by
  apply NatTrans.ext
  funext n
  exact (a.naturality (SimplexCategory.isTerminalZero.from n)).symm

omit [HasZeroObject C] in
/-- Every original operator of a homotopically constant frame gives a weak augmentation component. -/
theorem augmentation_weak (A : CosimplicialObject C)
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f)) (n : SimplexCategory) :
    weakEquivalences C ((augmentation A).app n) := hW _

section Tensor

variable [HasColimitsOfSize.{0, vC} C]

/-- The original scalar Quillen Hom function for any actual cofibrant cosimplicial frame. -/
def tensorHomEquivHo (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC}) (Y : C) :
    ((weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj A).obj K) ⟶ (weakEquivalences C).Q.obj Y) ≃
      (pointedProjection.obj K ⟶ pointedProjection.obj (pointedLeftHom A (d.R.obj Y))) := by
  let _ : (pointedTensorHomAdjunction A).IsQuillenAdjunction :=
    pointedTensorHomAdjunction_isQuillen A hA hW
  let _ : IsCofibrant K := pointedSSet_isCofibrant K
  let _ : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  exact (Iso.homCongr (Iso.refl _) (rHomotopyIso d Y)).trans
    (QuillenOrdinaryHoHom.homEquiv (pointedTensorHomAdjunction A) K (d.R.obj Y))

/-- The full scalar Hom equivalence is the original right-unit word followed by the original Quillen transpose. -/
theorem tensorHomEquivHo_apply (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC}) (Y : C)
    (h : (weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj A).obj K) ⟶ (weakEquivalences C).Q.obj Y) :
    tensorHomEquivHo d A hA hW K Y h =
      letI := pointedTensorHomAdjunction_isQuillen A hA hW
      letI := pointedSSet_isCofibrant K
      letI := d.r_fibrant Y
      QuillenOrdinaryHoHom.homEquiv (pointedTensorHomAdjunction A) K (d.R.obj Y)
        (h ≫ (rHomotopyIso d Y).hom) := by
  simp only [tensorHomEquivHo, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Category.id_comp]

/-- Every represented original tensor arrow retains its actual full pointed transpose and original R unit. -/
theorem tensorHomEquivHo_map (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC}) (Y : C) (f : (pointedTensorBifunctor.obj A).obj K ⟶ Y) :
    tensorHomEquivHo d A hA hW K Y ((weakEquivalences C).Q.map f) =
      pointedProjection.map (pointedTensorHomEquiv A K (d.R.obj Y) (f ≫ d.r.app Y)) := by
  let _ : (pointedTensorHomAdjunction A).IsQuillenAdjunction :=
    pointedTensorHomAdjunction_isQuillen A hA hW
  let _ : IsCofibrant K := pointedSSet_isCofibrant K
  let _ : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  rw [tensorHomEquivHo_apply]
  change QuillenOrdinaryHoHom.homEquiv (pointedTensorHomAdjunction A) K (d.R.obj Y)
    ((weakEquivalences C).Q.map f ≫ (weakEquivalences C).Q.map (d.r.app Y)) = _
  rw [← CategoryTheory.Functor.map_comp, QuillenOrdinaryHoHom.homEquiv_map]
  exact congrArg pointedProjection.map
    (pointedTensorHomAdjunction_homEquiv A K (d.R.obj Y) (f ≫ d.r.app Y))

/-- Source-frame transposition is natural on every genuine coefficient homotopy arrow. -/
theorem tensorHomEquivHo_source {A B : CosimplicialObject C}
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hWA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hB : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy B n))
    (hWB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (a : A ⟶ B) (K : PointedSSet.{vC}) (Y : C)
    (h : (weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj B).obj K) ⟶ (weakEquivalences C).Q.obj Y) :
    tensorHomEquivHo d A hA hWA K Y
        ((weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K) ≫ h) =
      tensorHomEquivHo d B hB hWB K Y h ≫
        pointedProjection.map (pointedHomPrecomp a ((SimplicialObject.const C).obj (d.R.obj Y))) := by
  let _ : (pointedTensorHomAdjunction A).IsQuillenAdjunction :=
    pointedTensorHomAdjunction_isQuillen A hA hWA
  let _ : (pointedTensorHomAdjunction B).IsQuillenAdjunction :=
    pointedTensorHomAdjunction_isQuillen B hB hWB
  let _ : IsCofibrant K := pointedSSet_isCofibrant K
  let _ : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  let _ : IsCofibrant ((pointedTensorBifunctor.obj B).obj K) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := pointedTensorHomAdjunction B) inferInstance
  obtain ⟨g, hg⟩ := map_surjective_of_isLocalization (weakEquivalences C).Q _ _
    (h ≫ (rHomotopyIso d Y).hom)
  rw [tensorHomEquivHo_apply, tensorHomEquivHo_apply]
  change QuillenOrdinaryHoHom.homEquiv (pointedTensorHomAdjunction A) K (d.R.obj Y)
      (((weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K) ≫ h) ≫ (rHomotopyIso d Y).hom) =
    QuillenOrdinaryHoHom.homEquiv (pointedTensorHomAdjunction B) K (d.R.obj Y)
      (h ≫ (rHomotopyIso d Y).hom) ≫ _
  rw [Category.assoc, ← hg, ← CategoryTheory.Functor.map_comp,
    QuillenOrdinaryHoHom.homEquiv_map, QuillenOrdinaryHoHom.homEquiv_map]
  have h₁ := pointedTensorHomAdjunction_homEquiv A K (d.R.obj Y)
    ((pointedTensorBifunctor.map a).app K ≫ g)
  have h₂ := pointedTensorHomAdjunction_homEquiv B K (d.R.obj Y) g
  have h₃ := pointedTensorHomEquiv_source a K (d.R.obj Y) g
  exact (congrArg pointedProjection.map h₁).trans
    ((congrArg pointedProjection.map h₃).trans
      ((pointedProjection.map_comp _ _).trans
        (congrArg (fun z => z ≫ pointedProjection.map
          (pointedHomPrecomp a ((SimplicialObject.const C).obj (d.R.obj Y))))
          (congrArg pointedProjection.map h₂).symm)))

include d in
/-- Actual frame maps agreeing through an original weak augmentation induce identical tensor maps at every weight. -/
theorem tensorMap_eq_of_augmentation {A B : CosimplicialObject C}
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hWA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hB : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy B n))
    (hWB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    {Z : C} [IsCofibrant Z] (β : B ⟶ (CosimplicialObject.const C).obj Z)
    (hβ : ∀ n, weakEquivalences C (β.app n))
    (a b : A ⟶ B) (hab : a ≫ β = b ≫ β) (K : PointedSSet.{vC}) :
    (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K) =
      (weakEquivalences C).Q.map ((pointedTensorBifunctor.map b).app K) := by
  apply (tensorHomEquivHo d A hA hWA K ((pointedTensorBifunctor.obj B).obj K)).injective
  have ha := tensorHomEquivHo_source d hA hWA hB hWB a K ((pointedTensorBifunctor.obj B).obj K) (𝟙 _)
  have hb := tensorHomEquivHo_source d hA hWA hB hWB b K ((pointedTensorBifunctor.obj B).obj K) (𝟙 _)
  simp only [Category.comp_id] at ha hb
  rw [ha, hb, leftHomPrecomp_eq_of_augmentation d hA hB β hβ a b hab]

include d in
/-- The full derived tensor transformation between cofibrant frames is determined by its original degree-zero map. -/
theorem tensorMap_eq_of_degreeZero {A B : CosimplicialObject C}
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hWA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hB : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy B n))
    (hWB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (a b : A ⟶ B) (hab : a.app ⦋0⦌ = b.app ⦋0⦌) (K : PointedSSet.{vC}) :
    (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K) =
      (weakEquivalences C).Q.map ((pointedTensorBifunctor.map b).app K) := by
  let _ : IsCofibrant (B.obj ⦋0⦌) := LeftFrameHomWeakEquivalence.coefficient_isCofibrant B hB ⦋0⦌
  apply tensorMap_eq_of_augmentation d hA hWA hB hWB (augmentation B) (augmentation_weak B hWB) a b
  rw [augmentation_square, augmentation_square, hab]

end Tensor
end HomotopicalAlgebra.PointedFramingAction.FrameCoherence

namespace HomotopicalAlgebra.PointedFramingAction

/-- The genuine freely based point, which is the original pointed smash unit. -/
abbrev pointedUnit : PointedSSet.{vC} := Pointed.smashUnit (Δ[0] : SSet.{vC})

/-- The scalar point is the same canonical standard zero simplex, with its identity comparison. -/
def scalarZeroIso : (SSet.stdSimplex.obj ⦋0⦌ : SSet.{vC}) ≅ (Δ[0] : SSet.{vC}) :=
  Iso.refl _

section Raw
variable {C : Type uC} [Category.{vC} C] [HasZeroObject C]
  [HasColimitsOfSize.{0, vC} C] [HasPushouts C]

/-- The actual pointed tensor at the smash unit represents the original zero-degree coefficient. -/
def unitHomEquiv (A : CosimplicialObject C) (Y : C) :
    (pointedTensor A pointedUnit.{vC} ⟶ Y) ≃ (A.obj ⦋0⦌ ⟶ Y) :=
  (pointedTensorHomEquiv A pointedUnit Y).trans
    (((Under.costarAdjForget (Δ[0] : SSet.{vC})).homEquiv (Δ[0] : SSet.{vC}) (pointedLeftHom A Y)).trans
      ((Iso.homCongr scalarZeroIso.symm (Iso.refl _)).trans SSet.yonedaEquiv))

/-- Every original map at the unit retains its full pointed transpose and original zero-simplex map. -/
theorem unitHomEquiv_apply (A : CosimplicialObject C) (Y : C)
    (f : pointedTensor A pointedUnit.{vC} ⟶ Y) :
    unitHomEquiv A Y f = SSet.yonedaEquiv
      (scalarZeroIso.hom ≫ (Under.costarAdjForget (Δ[0] : SSet.{vC})).homEquiv (Δ[0] : SSet.{vC})
        (pointedLeftHom A Y) (pointedTensorHomEquiv A pointedUnit Y f)) := by
  rfl

/-- The entire original unit transpose retains every coefficient target arrow. -/
theorem unitHomEquiv_target (A : CosimplicialObject C) {Y Y' : C} (g : Y ⟶ Y')
    (f : pointedTensor A pointedUnit.{vC} ⟶ Y) :
    unitHomEquiv A Y' (f ≫ g) = unitHomEquiv A Y f ≫ g := by
  rw [unitHomEquiv_apply, unitHomEquiv_apply, pointedTensorHomEquiv_target]
  have h := (Under.costarAdjForget (Δ[0] : SSet.{vC})).homEquiv_naturality_right
    (pointedTensorHomEquiv A pointedUnit Y f) ((pointedLeftHomFunctor A).map g)
  have h' := congrArg (fun z => SSet.yonedaEquiv (scalarZeroIso.hom ≫ z)) h
  exact h'.trans (by rw [← Category.assoc, SSet.yonedaEquiv_comp]; rfl)

/-- The entire original unit transpose retains every cosimplicial frame map and its degree-zero component. -/
theorem unitHomEquiv_frame {A B : CosimplicialObject C} (a : A ⟶ B) (Y : C)
    (f : pointedTensor B pointedUnit.{vC} ⟶ Y) :
    unitHomEquiv A Y (pointedTensorMap a (𝟙 pointedUnit) ≫ f) = a.app ⦋0⦌ ≫ unitHomEquiv B Y f := by
  rw [unitHomEquiv_apply, unitHomEquiv_apply, pointedTensorHomEquiv_source]
  have h := (Under.costarAdjForget (Δ[0] : SSet.{vC})).homEquiv_naturality_right
    (pointedTensorHomEquiv B pointedUnit Y f) (pointedHomPrecomp a ((SimplicialObject.const C).obj Y))
  have h' := congrArg (fun z => SSet.yonedaEquiv (scalarZeroIso.hom ≫ z)) h
  exact h'.trans (by rw [← Category.assoc, SSet.yonedaEquiv_comp]; rfl)

/-- The original pointed tensor unit isomorphism is obtained from its full colimit/cofiber Hom universal property. -/
def tensorUnitIso (A : CosimplicialObject C) : pointedTensor A pointedUnit.{vC} ≅ A.obj ⦋0⦌ where
  hom := (unitHomEquiv A (A.obj ⦋0⦌)).symm (𝟙 _)
  inv := unitHomEquiv A (pointedTensor A pointedUnit) (𝟙 _)
  hom_inv_id := by
    apply (unitHomEquiv A (pointedTensor A pointedUnit)).injective
    rw [unitHomEquiv_target, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    have h := unitHomEquiv_target A ((unitHomEquiv A (A.obj ⦋0⦌)).symm (𝟙 _))
      (𝟙 (pointedTensor A pointedUnit))
    rw [Category.id_comp, Equiv.apply_symm_apply] at h
    exact h.symm

/-- Both actual unit comparison maps are natural in every original full frame map. -/
theorem tensorUnitIso_naturality {A B : CosimplicialObject C} (a : A ⟶ B) :
    pointedTensorMap a (𝟙 pointedUnit.{vC}) ≫ (tensorUnitIso B).hom =
      (tensorUnitIso A).hom ≫ a.app ⦋0⦌ := by
  apply (unitHomEquiv A (B.obj ⦋0⦌)).injective
  rw [unitHomEquiv_frame, unitHomEquiv_target]
  change a.app ⦋0⦌ ≫ unitHomEquiv B (B.obj ⦋0⦌) ((unitHomEquiv B (B.obj ⦋0⦌)).symm (𝟙 _)) =
    unitHomEquiv A (A.obj ⦋0⦌) ((unitHomEquiv A (A.obj ⦋0⦌)).symm (𝟙 _)) ≫ a.app ⦋0⦌
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Category.comp_id, Category.id_comp]

end Raw

section Ordinary
variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))
open scoped SSet.modelCategoryQuillen

/-- The actual tensor unit component retains the original frame-zero isomorphism and original Q counit. -/
def tensorUnitHoComponent (X : C) :
    (tensorHo d pointedUnit.{vC}).obj ((weakEquivalences C).Q.obj X) ≅ (weakEquivalences C).Q.obj X :=
  (weakEquivalences C).Q.mapIso (tensorUnitIso ((leftFrame d).obj X)) ≪≫
    (weakEquivalences C).Q.mapIso ((leftZeroIso d).app X) ≪≫ qHomotopyIso d X

/-- The entire forward unit word consists of the same three original maps. -/
theorem tensorUnitHoComponent_hom (X : C) :
    (tensorUnitHoComponent d X).hom =
      (weakEquivalences C).Q.map (tensorUnitIso ((leftFrame d).obj X)).hom ≫
        (weakEquivalences C).Q.map ((leftZeroIso d).hom.app X) ≫
          (weakEquivalences C).Q.map (d.q.app X) := rfl

/-- Every original coefficient map preserves the actual unit comparison, including its Q arrow. -/
theorem tensorUnitHoComponent_naturality {X Y : C} (f : X ⟶ Y) :
    (tensorHo d pointedUnit).map ((weakEquivalences C).Q.map f) ≫ (tensorUnitHoComponent d Y).hom =
      (tensorUnitHoComponent d X).hom ≫ (weakEquivalences C).Q.map f := by
  rw [tensorUnitHoComponent_hom, tensorUnitHoComponent_hom, tensorHo_map]
  change (weakEquivalences C).Q.map (pointedTensorMap ((leftFrame d).map f) (𝟙 pointedUnit)) ≫
      (weakEquivalences C).Q.map (tensorUnitIso ((leftFrame d).obj Y)).hom ≫
        (weakEquivalences C).Q.map ((leftZeroIso d).hom.app Y) ≫ (weakEquivalences C).Q.map (d.q.app Y) =
    ((weakEquivalences C).Q.map (tensorUnitIso ((leftFrame d).obj X)).hom ≫
      (weakEquivalences C).Q.map ((leftZeroIso d).hom.app X) ≫ (weakEquivalences C).Q.map (d.q.app X)) ≫
        (weakEquivalences C).Q.map f
  have hz : ((leftFrame d).map f).app ⦋0⦌ ≫ (leftZeroIso d).hom.app Y =
      (leftZeroIso d).hom.app X ≫ d.Q.map f := (leftZeroIso d).hom.naturality f
  have h : pointedTensorMap ((leftFrame d).map f) (𝟙 pointedUnit) ≫
      (tensorUnitIso ((leftFrame d).obj Y)).hom ≫ (leftZeroIso d).hom.app Y ≫ d.q.app Y =
    (tensorUnitIso ((leftFrame d).obj X)).hom ≫ (leftZeroIso d).hom.app X ≫ d.q.app X ≫ f := by
    calc
      _ = (pointedTensorMap ((leftFrame d).map f) (𝟙 pointedUnit) ≫
          (tensorUnitIso ((leftFrame d).obj Y)).hom) ≫ (leftZeroIso d).hom.app Y ≫ d.q.app Y := by
        simp only [Category.assoc]
      _ = ((tensorUnitIso ((leftFrame d).obj X)).hom ≫ ((leftFrame d).map f).app ⦋0⦌) ≫
          (leftZeroIso d).hom.app Y ≫ d.q.app Y :=
        congrArg (fun z => z ≫ (leftZeroIso d).hom.app Y ≫ d.q.app Y)
          (tensorUnitIso_naturality ((leftFrame d).map f))
      _ = _ := by
        rw [Category.assoc, ← Category.assoc (((leftFrame d).map f).app ⦋0⦌), hz,
          Category.assoc, d.q.naturality]
        rfl
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using
    congrArg (weakEquivalences C).Q.map h

/-- The original framing tensor unit is a natural isomorphism on all coefficient Ho objects and arrows. -/
def tensorUnitHo : tensorHo d pointedUnit.{vC} ≅ 𝟭 (weakEquivalences C).Localization :=
  Localization.liftNatIso (weakEquivalences C).Q (weakEquivalences C)
    ((weakEquivalences C).Q ⋙ tensorHo d pointedUnit) ((weakEquivalences C).Q ⋙ 𝟭 _)
    (tensorHo d pointedUnit) (𝟭 _)
    (NatIso.ofComponents (tensorUnitHoComponent d)
      (fun {_ _} f => tensorUnitHoComponent_naturality d f))

/-- The full natural unit retains its same original component word on every original object. -/
theorem tensorUnitHo_hom_original (X : C) :
    (tensorUnitHo d).hom.app ((weakEquivalences C).Q.obj X) = (tensorUnitHoComponent d X).hom := by
  change (Localization.liftNatTrans (weakEquivalences C).Q (weakEquivalences C)
    ((weakEquivalences C).Q ⋙ tensorHo d pointedUnit) ((weakEquivalences C).Q ⋙ 𝟭 _)
    (tensorHo d pointedUnit) (𝟭 _)
    (NatIso.ofComponents (tensorUnitHoComponent d)
      (fun {_ _} f => tensorUnitHoComponent_naturality d f)).hom).app ((weakEquivalences C).Q.obj X) = _
  rw [Localization.liftNatTrans_app]
  rfl

/-- The same original scalar adjunction makes the cotensor unit naturally the identity. -/
def cotensorUnitHo : cotensorHo d pointedUnit.{vC} ≅ 𝟭 (weakEquivalences C).Localization :=
  (conjugateIsoEquiv (Adjunction.id) (ordinaryAdjunction d pointedUnit) (tensorUnitHo d)).symm

end Ordinary
end HomotopicalAlgebra.PointedFramingAction

namespace HomotopicalAlgebra.PointedFramingAction

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  (d : GeneratedFunctorialReplacements.Data (C := C))
open scoped SSet.modelCategoryQuillen

/-- The entire original pointed right HFC is the existing pointed-Hom bifunctor at the original Q and right frame. -/
def rightHFCBifunctor : Cᵒᵖ ⥤ C ⥤ PointedSSet.{vC} :=
  (d.Q ⋙ CosimplicialObject.const C).op ⋙ pointedHomBifunctor ⋙
    (Functor.whiskeringLeft C (SimplicialObject C) PointedSSet.{vC}).obj (rightFrame d)

/-- The actual original HFC is localized in the scalar homotopy category before coefficient descent. -/
def rightHFCProjectionBifunctor : Cᵒᵖ ⥤ C ⥤ PointedSpaceHo.{vC} :=
  rightHFCBifunctor d ⋙ (Functor.whiskeringRight C PointedSSet.{vC} PointedSpaceHo.{vC}).obj pointedProjection

/-- Both original weak coefficient arrows are inverted by the genuine HFC projection bifunctor. -/
theorem rightHFC_inverts₂ :
    MorphismProperty.IsInvertedBy₂ (weakEquivalences C).op (weakEquivalences C)
      (rightHFCProjectionBifunctor d) := by
  rintro ⟨X, Y⟩ ⟨X', Y'⟩ ⟨f, g⟩ ⟨hf, hg⟩
  change weakEquivalences C f.unop at hf
  let _ : IsIso (pointedProjection.map (pointedRightSourceMap d f.unop Y)) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC}) _
      (pointedRightSourceMap_weak d f.unop hf Y)
  let _ : IsIso (pointedProjection.map (pointedRightTargetMap d X'.unop g)) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC}) _
      (pointedRightTargetMap_weak d X'.unop g hg)
  change IsIso (pointedProjection.map (pointedRightSourceMap d f.unop Y) ≫
    pointedProjection.map (pointedRightTargetMap d X'.unop g))
  infer_instance

/-- The actual pointed HFC on every object and arrow of both original coefficient homotopy categories. -/
def mappingHo : (weakEquivalences C).Localizationᵒᵖ ⥤
    (weakEquivalences C).Localization ⥤ PointedSpaceHo.{vC} :=
  Localization.lift₂ (rightHFCProjectionBifunctor d) (rightHFC_inverts₂ d)
    (weakEquivalences C).Q.op (weakEquivalences C).Q

/-- The original whole HFC projection is retained by its canonical bifunctor descent. -/
instance mappingHoLifting : Localization.Lifting₂
    (weakEquivalences C).Q.op (weakEquivalences C).Q
    (weakEquivalences C).op (weakEquivalences C) (rightHFCProjectionBifunctor d) (mappingHo d) :=
  inferInstanceAs (Localization.Lifting₂ (weakEquivalences C).Q.op (weakEquivalences C).Q
    (weakEquivalences C).op (weakEquivalences C) (rightHFCProjectionBifunctor d)
    (Localization.lift₂ (rightHFCProjectionBifunctor d) (rightHFC_inverts₂ d)
      (weakEquivalences C).Q.op (weakEquivalences C).Q))

/-- The complete scalar localization comparison retains the same original Q and right-frame mapping space. -/
def mappingHoOriginalIso (X Y : C) :
    ((mappingHo d).obj (Opposite.op ((weakEquivalences C).Q.obj X))).obj ((weakEquivalences C).Q.obj Y) ≅
      pointedRightHoSpace d X Y :=
  ((Localization.Lifting₂.iso (weakEquivalences C).Q.op (weakEquivalences C).Q
    (weakEquivalences C).op (weakEquivalences C) (rightHFCProjectionBifunctor d) (mappingHo d)).app
      (Opposite.op X)).app Y

/-- Every original coefficient target arrow retains the entire HFC descent square. -/
theorem mappingHoOriginalIso_target (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    ((mappingHo d).obj (Opposite.op ((weakEquivalences C).Q.obj X))).map ((weakEquivalences C).Q.map g) ≫
        (mappingHoOriginalIso d X Y').hom =
      (mappingHoOriginalIso d X Y).hom ≫ pointedProjection.map (pointedRightTargetMap d X g) :=
  ((Localization.Lifting₂.iso (weakEquivalences C).Q.op (weakEquivalences C).Q
    (weakEquivalences C).op (weakEquivalences C) (rightHFCProjectionBifunctor d) (mappingHo d)).hom.app
      (Opposite.op X)).naturality g

/-- Every original coefficient source arrow retains the entire HFC descent square. -/
theorem mappingHoOriginalIso_source {X X' : C} (f : X ⟶ X') (Y : C) :
    ((mappingHo d).map ((weakEquivalences C).Q.map f).op).app ((weakEquivalences C).Q.obj Y) ≫
        (mappingHoOriginalIso d X Y).hom =
      (mappingHoOriginalIso d X' Y).hom ≫ pointedProjection.map (pointedRightSourceMap d f Y) := by
  exact congrArg (fun τ => τ.app Y)
    ((Localization.Lifting₂.iso (weakEquivalences C).Q.op (weakEquivalences C).Q
      (weakEquivalences C).op (weakEquivalences C) (rightHFCProjectionBifunctor d) (mappingHo d)).hom.naturality
        f.op)

/-- The entire inverse HFC comparison retains every original target arrow. -/
theorem mappingHoOriginalIso_target_inv (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    pointedProjection.map (pointedRightTargetMap d X g) ≫ (mappingHoOriginalIso d X Y').inv =
      (mappingHoOriginalIso d X Y).inv ≫
        ((mappingHo d).obj (Opposite.op ((weakEquivalences C).Q.obj X))).map ((weakEquivalences C).Q.map g) := by
  apply (cancel_mono (mappingHoOriginalIso d X Y').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [mappingHoOriginalIso_target]
  simp only [Iso.inv_hom_id_assoc]

/-- The entire inverse HFC comparison retains every original source arrow. -/
theorem mappingHoOriginalIso_source_inv {X X' : C} (f : X ⟶ X') (Y : C) :
    pointedProjection.map (pointedRightSourceMap d f Y) ≫ (mappingHoOriginalIso d X Y).inv =
      (mappingHoOriginalIso d X' Y).inv ≫
        ((mappingHo d).map ((weakEquivalences C).Q.map f).op).app ((weakEquivalences C).Q.obj Y) := by
  apply (cancel_mono (mappingHoOriginalIso d X Y).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [mappingHoOriginalIso_source]
  simp only [Iso.inv_hom_id_assoc]

section Weights
variable [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C]

/-- The carrier equality leg of the full scalar action is the actual identity on the original tensor functor. -/
theorem tensorAction_carrierLeg (K : PointedSSet.{vC}) :
    eqToHom (tensorAction_obj d K) = 𝟙 (tensorHo d K) := by
  exact eqToHom_refl (tensorHo d K) (tensorAction_obj d K)

/-- The reverse carrier equality leg is the same actual identity on the original tensor functor. -/
theorem tensorAction_inverseCarrierLeg (K : PointedSSet.{vC}) :
    eqToHom (tensorAction_obj d K).symm = 𝟙 (tensorHo d K) := by
  exact eqToHom_refl (tensorHo d K) (tensorAction_obj d K).symm

/-- Every original pointed weight arrow has exactly its full original tensor natural transformation. -/
theorem tensorAction_map_original {K L : PointedSSet.{vC}} (k : K ⟶ L) :
    (tensorAction d).map (pointedProjection.map k) = tensorWeightMap d k := by
  rw [tensorAction_map, tensorAction_carrierLeg, tensorAction_inverseCarrierLeg]
  change 𝟙 (tensorHo d K) ≫ tensorWeightMap d k ≫ 𝟙 (tensorHo d L) = tensorWeightMap d k
  rw [Category.id_comp, Category.comp_id]

/-- The full closed Hom function on the original tensor, replacements and genuine HFC. -/
def closedHomOriginal (X : C) (K : PointedSSet.{vC}) (Y : C) :
    ((weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X) K) ⟶ (weakEquivalences C).Q.obj Y) ≃
      (pointedProjection.obj K ⟶
        ((mappingHo d).obj (Opposite.op ((weakEquivalences C).Q.obj X))).obj ((weakEquivalences C).Q.obj Y)) :=
  (Iso.homCongr (Iso.refl _) (rHomotopyIso d Y)).trans
    ((pointedTensorHoHomEquiv d X K Y).trans
      ((Iso.homCongr (Iso.refl _) (pointedLeftRightIso d X Y)).trans
        (Iso.homCongr (Iso.refl _) (mappingHoOriginalIso d X Y).symm)))

/-- The original full scalar Hom equivalence gives the actual two-variable closed Hom function on all Ho objects. -/
def closedHomEquiv (X : (weakEquivalences C).Localization) (K : PointedSpaceHo.{vC})
    (Y : (weakEquivalences C).Localization) :
    (((tensorAction d).obj K).obj X ⟶ Y) ≃ (K ⟶ ((mappingHo d).obj (Opposite.op X)).obj Y) := by
  rcases X with ⟨⟨X⟩⟩
  rcases K with ⟨⟨K⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  exact closedHomOriginal d X K Y

/-- The complete closed Hom function retains the same original coefficient and scalar objects. -/
theorem closedHomEquiv_original (X : C) (K : PointedSSet.{vC}) (Y : C) :
    closedHomEquiv d ((weakEquivalences C).Q.obj X) (pointedProjection.obj K) ((weakEquivalences C).Q.obj Y) =
      closedHomOriginal d X K Y := rfl

omit [HasLimitsOfSize.{0, vC} C] in
/-- The closed Hom function retains its complete original replacement and genuine HFC comparison word. -/
theorem closedHomOriginal_apply (X : C) (K : PointedSSet.{vC}) (Y : C)
    (h : (weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X) K) ⟶ (weakEquivalences C).Q.obj Y) :
    closedHomOriginal d X K Y h =
      pointedTensorHoHomEquiv d X K Y (h ≫ (rHomotopyIso d Y).hom) ≫
        (pointedLeftRightIso d X Y).hom ≫ (mappingHoOriginalIso d X Y).inv := by
  simp only [closedHomOriginal, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Iso.symm_hom, Category.id_comp, Category.assoc]

omit [HasLimitsOfSize.{0, vC} C] in
/-- The complete closed Hom word is natural in every original pointed weight arrow. -/
theorem closedHomEquiv_original_weight (X : C) {K L : PointedSSet.{vC}} (k : K ⟶ L) (Y : C)
    (h : (weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X) L) ⟶ (weakEquivalences C).Q.obj Y) :
    closedHomOriginal d X K Y
        ((weakEquivalences C).Q.map (pointedTensorMap (𝟙 ((leftFrame d).obj X)) k) ≫ h) =
      pointedProjection.map k ≫ closedHomOriginal d X L Y h := by
  rw [closedHomOriginal_apply, closedHomOriginal_apply,
    Category.assoc, pointedTensorHoHomEquiv_parameter]
  simp only [Category.assoc]

omit [HasLimitsOfSize.{0, vC} C] in
/-- The complete closed Hom word retains every original coefficient source map. -/
theorem closedHomEquiv_original_source {X X' : C} (f : X ⟶ X') (K : PointedSSet.{vC}) (Y : C)
    (h : (weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X') K) ⟶ (weakEquivalences C).Q.obj Y) :
    closedHomOriginal d X K Y
        ((weakEquivalences C).Q.map (pointedTensorMap ((leftFrame d).map f) (𝟙 K)) ≫ h) =
      closedHomOriginal d X' K Y h ≫
        ((mappingHo d).map ((weakEquivalences C).Q.map f).op).app ((weakEquivalences C).Q.obj Y) := by
  rw [closedHomOriginal_apply, closedHomOriginal_apply,
    Category.assoc, pointedTensorHoHomEquiv_source]
  have hn : pointedProjection.map (pointedLeftSourceMap d f Y) ≫
      (pointedLeftRightIso d X Y).hom ≫ (mappingHoOriginalIso d X Y).inv =
    (pointedLeftRightIso d X' Y).hom ≫ (mappingHoOriginalIso d X' Y).inv ≫
      ((mappingHo d).map ((weakEquivalences C).Q.map f).op).app ((weakEquivalences C).Q.obj Y) := by
    calc
      _ = (pointedProjection.map (pointedLeftSourceMap d f Y) ≫
          (pointedLeftRightIso d X Y).hom) ≫ (mappingHoOriginalIso d X Y).inv :=
        (Category.assoc _ _ _).symm
      _ = ((pointedLeftRightIso d X' Y).hom ≫ pointedProjection.map (pointedRightSourceMap d f Y)) ≫
          (mappingHoOriginalIso d X Y).inv :=
        congrArg (fun z => z ≫ (mappingHoOriginalIso d X Y).inv) (pointedLeftRightIso_source d f Y)
      _ = _ := by rw [Category.assoc, mappingHoOriginalIso_source_inv]
  simpa only [Category.assoc] using congrArg
    (fun z => pointedTensorHoHomEquiv d X' K Y (h ≫ (rHomotopyIso d Y).hom) ≫ z) hn

omit [HasLimitsOfSize.{0, vC} C] in
/-- The complete closed Hom word retains every original coefficient target map. -/
theorem closedHomEquiv_original_target (X : C) (K : PointedSSet.{vC}) {Y Y' : C} (g : Y ⟶ Y')
    (h : (weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X) K) ⟶ (weakEquivalences C).Q.obj Y) :
    closedHomOriginal d X K Y' (h ≫ (weakEquivalences C).Q.map g) =
      closedHomOriginal d X K Y h ≫
        ((mappingHo d).obj (Opposite.op ((weakEquivalences C).Q.obj X))).map ((weakEquivalences C).Q.map g) := by
  rw [closedHomOriginal_apply, closedHomOriginal_apply]
  have hr : (h ≫ (weakEquivalences C).Q.map g) ≫ (rHomotopyIso d Y').hom =
      (h ≫ (rHomotopyIso d Y).hom) ≫ (weakEquivalences C).Q.map (d.R.map g) := by
    rw [Category.assoc, rHomotopyIso_naturality, ← Category.assoc]
  rw [hr, pointedTensorHoHomEquiv_target d X K g]
  have hn : pointedProjection.map (pointedLeftTargetMap d X g) ≫
      (pointedLeftRightIso d X Y').hom ≫ (mappingHoOriginalIso d X Y').inv =
    (pointedLeftRightIso d X Y).hom ≫ (mappingHoOriginalIso d X Y).inv ≫
      ((mappingHo d).obj (Opposite.op ((weakEquivalences C).Q.obj X))).map ((weakEquivalences C).Q.map g) := by
    calc
      _ = (pointedProjection.map (pointedLeftTargetMap d X g) ≫
          (pointedLeftRightIso d X Y').hom) ≫ (mappingHoOriginalIso d X Y').inv :=
        (Category.assoc _ _ _).symm
      _ = ((pointedLeftRightIso d X Y).hom ≫ pointedProjection.map (pointedRightTargetMap d X g)) ≫
          (mappingHoOriginalIso d X Y').inv :=
        congrArg (fun z => z ≫ (mappingHoOriginalIso d X Y').inv) (pointedLeftRightIso_target d X g)
      _ = _ := by rw [Category.assoc, mappingHoOriginalIso_target_inv]
  simpa only [Category.assoc] using congrArg
    (fun z => pointedTensorHoHomEquiv d X K Y (h ≫ (rHomotopyIso d Y).hom) ≫ z) hn

/-- The genuine closed Hom function is natural in every pointed-space Ho arrow, including formal inverses. -/
theorem closedHomEquiv_weight (X : (weakEquivalences C).Localization)
    {K L : PointedSpaceHo.{vC}} (k : K ⟶ L) (Y : (weakEquivalences C).Localization)
    (h : ((tensorAction d).obj L).obj X ⟶ Y) :
    closedHomEquiv d X K Y (((tensorAction d).map k).app X ≫ h) =
      k ≫ closedHomEquiv d X L Y h := by
  let γ := pointedProjection.{vC}
  let F₁ := ((tensorAction d).flip.obj X).op ⋙ uliftYoneda.{max uC (vC + 1)}.obj Y
  let F₂ := uliftYoneda.{max uC (vC + 1)}.obj (((mappingHo d).obj (Opposite.op X)).obj Y)
  let τ₀ : γ.op ⋙ F₁ ⟶ γ.op ⋙ F₂ :=
    { app K := ↾fun a => ULift.up (closedHomEquiv d X (γ.obj K.unop) Y a.down)
      naturality {K K'} g := by
        ext a
        apply ULift.ext
        rcases X with ⟨⟨X⟩⟩
        rcases Y with ⟨⟨Y⟩⟩
        change closedHomOriginal d X K'.unop Y
            (((tensorAction d).map (γ.map g.unop)).app ((weakEquivalences C).Q.obj X) ≫ a.down) =
          γ.map g.unop ≫ closedHomOriginal d X K.unop Y a.down
        rw [tensorAction_map_original, tensorWeightMap_app]
        change closedHomOriginal d X K'.unop Y
            ((weakEquivalences C).Q.map (pointedTensorMap (𝟙 ((leftFrame d).obj X)) g.unop) ≫ a.down) =
          γ.map g.unop ≫ closedHomOriginal d X K.unop Y a.down
        exact closedHomEquiv_original_weight d X g.unop Y a.down }
  let τ : F₁ ⟶ F₂ := Localization.liftNatTrans γ.op (weakEquivalences PointedSSet.{vC}).op
    (γ.op ⋙ F₁) (γ.op ⋙ F₂) F₁ F₂ τ₀
  have hτ (K : PointedSSet.{vC}) : τ.app (Opposite.op (γ.obj K)) =
      ↾fun a => ULift.up (closedHomEquiv d X (γ.obj K) Y a.down) := by
    change (Localization.liftNatTrans γ.op (weakEquivalences PointedSSet.{vC}).op
      (γ.op ⋙ F₁) (γ.op ⋙ F₂) F₁ F₂ τ₀).app (γ.op.obj (Opposite.op K)) = _
    rw [Localization.liftNatTrans_app]
    rfl
  rcases K with ⟨⟨K⟩⟩
  rcases L with ⟨⟨L⟩⟩
  let hLift : F₁.obj (Opposite.op (γ.obj L)) := by
    change ULift.{max uC (vC + 1)} ((((tensorAction d).obj (γ.obj L)).obj X) ⟶ Y)
    exact ULift.up h
  have hn := τ.naturality_apply k.op hLift
  change (τ.app (Opposite.op (γ.obj K))) (ULift.up (((tensorAction d).map k).app X ≫ h)) =
    ULift.up (k ≫ ((τ.app (Opposite.op (γ.obj L))) (ULift.up h)).down) at hn
  rw [hτ K, hτ L] at hn
  exact congrArg ULift.down hn

/-- The genuine closed Hom function is natural in every coefficient Ho source arrow. -/
theorem closedHomEquiv_source {X X' : (weakEquivalences C).Localization} (f : X ⟶ X')
    (K : PointedSpaceHo.{vC}) (Y : (weakEquivalences C).Localization)
    (h : ((tensorAction d).obj K).obj X' ⟶ Y) :
    closedHomEquiv d X K Y (((tensorAction d).obj K).map f ≫ h) =
      closedHomEquiv d X' K Y h ≫ ((mappingHo d).map f.op).app Y := by
  let γ := (weakEquivalences C).Q
  let F₁ := ((tensorAction d).obj K).op ⋙ uliftYoneda.{max uC (vC + 1)}.obj Y
  let F₂ := (mappingHo d).flip.obj Y ⋙ uliftCoyoneda.{max uC (vC + 1)}.obj (Opposite.op K)
  let τ₀ : γ.op ⋙ F₁ ⟶ γ.op ⋙ F₂ :=
    { app X := ↾fun a => ULift.up (closedHomEquiv d (γ.obj X.unop) K Y a.down)
      naturality {X X'} g := by
        ext a
        apply ULift.ext
        rcases K with ⟨⟨K⟩⟩
        rcases Y with ⟨⟨Y⟩⟩
        change closedHomOriginal d X'.unop K Y
            ((tensorHo d K).map (γ.map g.unop) ≫ a.down) =
          closedHomOriginal d X.unop K Y a.down ≫ ((mappingHo d).map (γ.map g.unop).op).app (γ.obj Y)
        rw [tensorHo_map]
        change closedHomOriginal d X'.unop K Y
            (γ.map (pointedTensorMap ((leftFrame d).map g.unop) (𝟙 K)) ≫ a.down) =
          closedHomOriginal d X.unop K Y a.down ≫ ((mappingHo d).map (γ.map g.unop).op).app (γ.obj Y)
        exact closedHomEquiv_original_source d g.unop K Y a.down }
  let τ : F₁ ⟶ F₂ := Localization.liftNatTrans γ.op (weakEquivalences C).op
    (γ.op ⋙ F₁) (γ.op ⋙ F₂) F₁ F₂ τ₀
  have hτ (X : C) : τ.app (Opposite.op (γ.obj X)) =
      ↾fun a => ULift.up (closedHomEquiv d (γ.obj X) K Y a.down) := by
    change (Localization.liftNatTrans γ.op (weakEquivalences C).op
      (γ.op ⋙ F₁) (γ.op ⋙ F₂) F₁ F₂ τ₀).app (γ.op.obj (Opposite.op X)) = _
    rw [Localization.liftNatTrans_app]
    rfl
  rcases X with ⟨⟨X⟩⟩
  rcases X' with ⟨⟨X'⟩⟩
  let hLift : F₁.obj (Opposite.op (γ.obj X')) := by
    change ULift.{max uC (vC + 1)} ((((tensorAction d).obj K).obj (γ.obj X')) ⟶ Y)
    exact ULift.up h
  have hn := τ.naturality_apply f.op hLift
  change (τ.app (Opposite.op (γ.obj X))) (ULift.up (((tensorAction d).obj K).map f ≫ h)) =
    ULift.up (((τ.app (Opposite.op (γ.obj X'))) (ULift.up h)).down ≫ ((mappingHo d).map f.op).app Y) at hn
  rw [hτ X, hτ X'] at hn
  exact congrArg ULift.down hn

/-- The genuine closed Hom function is natural in every coefficient Ho target arrow. -/
theorem closedHomEquiv_target (X : (weakEquivalences C).Localization) (K : PointedSpaceHo.{vC})
    {Y Y' : (weakEquivalences C).Localization} (g : Y ⟶ Y')
    (h : ((tensorAction d).obj K).obj X ⟶ Y) :
    closedHomEquiv d X K Y' (h ≫ g) =
      closedHomEquiv d X K Y h ≫ ((mappingHo d).obj (Opposite.op X)).map g := by
  let γ := (weakEquivalences C).Q
  let F₁ := uliftCoyoneda.{max uC (vC + 1)}.obj (Opposite.op (((tensorAction d).obj K).obj X))
  let F₂ := (mappingHo d).obj (Opposite.op X) ⋙ uliftCoyoneda.{max uC (vC + 1)}.obj (Opposite.op K)
  let τ₀ : γ ⋙ F₁ ⟶ γ ⋙ F₂ :=
    { app Y := ↾fun a => ULift.up (closedHomEquiv d X K (γ.obj Y) a.down)
      naturality {Y Y'} g := by
        ext a
        apply ULift.ext
        rcases X with ⟨⟨X⟩⟩
        rcases K with ⟨⟨K⟩⟩
        change closedHomOriginal d X K Y' (a.down ≫ γ.map g) =
          closedHomOriginal d X K Y a.down ≫ ((mappingHo d).obj (Opposite.op (γ.obj X))).map (γ.map g)
        exact closedHomEquiv_original_target d X K g a.down }
  let τ : F₁ ⟶ F₂ := Localization.liftNatTrans γ (weakEquivalences C)
    (γ ⋙ F₁) (γ ⋙ F₂) F₁ F₂ τ₀
  have hτ (Y : C) : τ.app (γ.obj Y) = ↾fun a => ULift.up (closedHomEquiv d X K (γ.obj Y) a.down) := by
    change (Localization.liftNatTrans γ (weakEquivalences C)
      (γ ⋙ F₁) (γ ⋙ F₂) F₁ F₂ τ₀).app (γ.obj Y) = _
    rw [Localization.liftNatTrans_app]
    rfl
  rcases Y with ⟨⟨Y⟩⟩
  rcases Y' with ⟨⟨Y'⟩⟩
  let hLift : F₁.obj (γ.obj Y) := by
    change ULift.{max uC (vC + 1)} ((((tensorAction d).obj K).obj X) ⟶ γ.obj Y)
    exact ULift.up h
  have hn := τ.naturality_apply g hLift
  change (τ.app (γ.obj Y')) (ULift.up (h ≫ g)) =
    ULift.up (((τ.app (γ.obj Y)) (ULift.up h)).down ≫ ((mappingHo d).obj (Opposite.op X)).map g) at hn
  rw [hτ Y, hτ Y'] at hn
  exact congrArg ULift.down hn

/-- The original tensor and genuine HFC form the full closed scalar adjunction on every Ho object and arrow. -/
def closedAdjunction (X : (weakEquivalences C).Localization) :
    (tensorAction d).flip.obj X ⊣ (mappingHo d).obj (Opposite.op X) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun K Y => closedHomEquiv d X K Y
      homEquiv_naturality_left_symm := by
        intro K L Y k h
        apply (closedHomEquiv d X K Y).injective
        rw [Equiv.apply_symm_apply]
        change k ≫ h = closedHomEquiv d X K Y
          (((tensorAction d).map k).app X ≫ (closedHomEquiv d X L Y).symm h)
        rw [closedHomEquiv_weight, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro K Y Y' h g
        exact closedHomEquiv_target d X K g h }

end Weights
end HomotopicalAlgebra.PointedFramingAction

universe v

namespace HomotopicalAlgebra.PointedFramingAction.ScalarStructure

open MonoidalCategory
open scoped MonoidalCategory SSet.modelCategoryQuillen

/-- The same actual pointed simplicial smash tensor on the original Under carrier. -/
abbrev smashMonoidal : MonoidalCategory PointedSSet.{v} :=
  Pointed.smashMonoidalCategory (Δ[0] : SSet.{v}) SSet.stdSimplex.isTerminalObj₀

/-- The canonical symmetry of that same pointed scalar tensor. -/
abbrev smashSymmetric : @SymmetricCategory PointedSSet.{v} _ smashMonoidal :=
  Pointed.smashSymmetricCategory (Δ[0] : SSet.{v}) SSet.stdSimplex.isTerminalObj₀

/-- The canonical based internal Hom of that same pointed scalar tensor. -/
abbrev smashClosed : @MonoidalClosed PointedSSet.{v} _ smashMonoidal :=
  Pointed.smashMonoidalClosed (Δ[0] : SSet.{v}) SSet.stdSimplex.isTerminalObj₀

/-- The original created pointed Kan--Quillen model satisfies the actual smash model axioms. -/
theorem smashModel :
    let _ := smashMonoidal.{v}
    let _ := smashSymmetric.{v}
    let _ := smashClosed.{v}
    IsClosedSymmetricMonoidalModelCategory PointedSSet.{v} := by
  let _ := smashMonoidal.{v}
  let _ := smashSymmetric.{v}
  let _ := smashClosed.{v}
  exact underSmashIsClosedSymmetricMonoidalModelCategory (Δ[0] : SSet.{v}) SSet.stdSimplex.isTerminalObj₀

/-- Any original weak scalar arrow remains weak after smash with any actual pointed weight. -/
theorem smashWeakLeft (K : PointedSSet.{v}) {A B : PointedSSet.{v}} (f : A ⟶ B)
    (hf : weakEquivalences PointedSSet.{v} f) :
    let _ := smashMonoidal.{v}
    weakEquivalences PointedSSet.{v} (K ◁ f) := by
  let _ := smashMonoidal.{v}
  let _ := smashSymmetric.{v}
  let _ := smashClosed.{v}
  let _ := smashModel.{v}
  let _ := pointedSSet_isCofibrant K
  let _ := pointedSSet_isCofibrant A
  let _ := pointedSSet_isCofibrant B
  let _ : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  let _ := ihomAdjunction_isQuillenAdjunction_of_isCofibrant K
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := ihom.adjunction K) f)

/-- The original pointed symmetry gives weak preservation in the other scalar tensor variable. -/
theorem smashWeakRight {A B : PointedSSet.{v}} (f : A ⟶ B)
    (hf : weakEquivalences PointedSSet.{v} f) (K : PointedSSet.{v}) :
    let _ := smashMonoidal.{v}
    weakEquivalences PointedSSet.{v} (f ▷ K) := by
  let _ := smashMonoidal.{v}
  let _ := smashSymmetric.{v}
  let e : CategoryTheory.Arrow.mk (f ▷ K) ≅ CategoryTheory.Arrow.mk (K ◁ f) :=
    CategoryTheory.Arrow.isoMk (β_ A K) (β_ B K) (BraidedCategory.braiding_naturality_left f K).symm
  exact ((weakEquivalences PointedSSet.{v}).arrow_mk_iso_iff e).mpr (smashWeakLeft K f hf)

/-- Actual scalar weak equivalences form a monoidal morphism property for the original smash product. -/
theorem weakSmashMonoidal :
    let _ := smashMonoidal.{v}
    (weakEquivalences PointedSSet.{v}).IsMonoidal := by
  let _ := smashMonoidal.{v}
  apply MorphismProperty.IsMonoidal.mk'
  intro A B K L f g hf hg
  rw [MonoidalCategory.tensorHom_def]
  exact (weakEquivalences PointedSSet.{v}).comp_mem _ _ (smashWeakRight f hf K) (smashWeakLeft B g hg)

/-- The actual homotopy category of pointed simplicial sets has the canonical localized smash tensor and coherence. -/
@[instance_reducible]
def monoidalHo : MonoidalCategory PointedSpaceHo.{v} := by
  let _ := smashMonoidal.{v}
  let _ := weakSmashMonoidal.{v}
  exact inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal pointedProjection (weakEquivalences PointedSSet.{v})
      (Iso.refl (pointedProjection.obj (𝟙_ PointedSSet.{v})))))

/-- The original pointed weak localization is strong monoidal for those same scalar tensors. -/
@[instance_reducible]
def projectionMonoidal :
    let _ := smashMonoidal.{v}
    let _ := monoidalHo.{v}
    pointedProjection.{v}.Monoidal := by
  let _ := smashMonoidal.{v}
  let _ := weakSmashMonoidal.{v}
  let _ := monoidalHo.{v}
  exact inferInstanceAs ((Localization.Monoidal.toMonoidalCategory pointedProjection
    (weakEquivalences PointedSSet.{v}) (Iso.refl (pointedProjection.obj (𝟙_ PointedSSet.{v})))).Monoidal)

/-- Every pair of original weights retains the actual localized smash comparison. -/
def tensorator (K L : PointedSSet.{v}) :
    let _ := smashMonoidal.{v}
    let _ := monoidalHo.{v}
    pointedProjection.obj K ⊗ pointedProjection.obj L ≅ pointedProjection.obj (K ⊗ L) := by
  let _ := smashMonoidal.{v}
  let _ := weakSmashMonoidal.{v}
  let _ := monoidalHo.{v}
  exact Localization.Monoidal.μ pointedProjection (weakEquivalences PointedSSet.{v})
    (Iso.refl (pointedProjection.obj (𝟙_ PointedSSet.{v}))) K L

end HomotopicalAlgebra.PointedFramingAction.ScalarStructure

section PointedActionPromotionPointedDensity

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe uC_PointedDensity vC_PointedDensity
open CategoryTheory Limits Simplicial

namespace HomotopicalAlgebra.PointedFramingAction.FrameTensorFubini

section FreeBasepoint

/-- The freely based scalar functor on the original simplicial-set carrier. -/
abbrev freeBasepoint : SSet.{vC_PointedDensity} ⥤ PointedSSet.{vC_PointedDensity} :=
  Under.costar (Δ[0] : SSet.{vC_PointedDensity})

/-- The original one-point based object, initial in the pointed scalar category. -/
abbrev scalarPoint : PointedSSet.{vC_PointedDensity} := Under.mk (𝟙 (Δ[0] : SSet.{vC_PointedDensity}))

/-- The actual collapse is the original inverse free-basepoint Hom function. -/
def freeBasepointCollapse : freeBasepoint.obj (Δ[0] : SSet.{vC_PointedDensity}) ⟶ scalarPoint.{vC_PointedDensity} :=
  ((Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv (Δ[0] : SSet.{vC_PointedDensity})
    scalarPoint).symm (𝟙 (Δ[0] : SSet.{vC_PointedDensity}))

/-- The original free-basepoint counit on the full input object. -/
def freeBasepointCounit (L : PointedSSet.{vC_PointedDensity}) : freeBasepoint.obj L.right ⟶ L :=
  ((Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv L.right L).symm (𝟙 L.right)

/-- The counit used in the presentation is the original adjunction counit. -/
theorem freeBasepointCounit_eq_counit (L : PointedSSet.{vC_PointedDensity}) :
    freeBasepointCounit L = (Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).counit.app L :=
  Adjunction.homEquiv_symm_id _ _

/-- All original pointed maps preserve the entire free-basepoint counit. -/
@[reassoc]
theorem freeBasepointCounit_naturality {K L : PointedSSet.{vC_PointedDensity}} (k : K ⟶ L) :
    freeBasepoint.map k.right ≫ freeBasepointCounit L = freeBasepointCounit K ≫ k := by
  rw [freeBasepointCounit_eq_counit, freeBasepointCounit_eq_counit]
  exact (Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).counit.naturality k

/-- The actual selected-point leg in the original free-basepoint pushout. -/
def scalarPointLeg (L : PointedSSet.{vC_PointedDensity}) : scalarPoint.{vC_PointedDensity} ⟶ L :=
  Under.homMk L.hom (by simp)

/-- The whole free-basepoint collapse square retains the original selected-point map. -/
theorem freeBasepointSquare (L : PointedSSet.{vC_PointedDensity}) :
    freeBasepoint.map L.hom ≫ freeBasepointCounit L =
      freeBasepointCollapse ≫ scalarPointLeg L := by
  apply ((Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  change L.hom ≫ (Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv L.right L
      (((Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv L.right L).symm (𝟙 L.right)) =
    (Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv (Δ[0] : SSet.{vC_PointedDensity}) scalarPoint
      (((Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv (Δ[0] : SSet.{vC_PointedDensity})
        scalarPoint).symm (𝟙 (Δ[0] : SSet.{vC_PointedDensity}))) ≫ L.hom
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Category.comp_id, Category.id_comp]

/-- The actual mediator uses the same original free-basepoint Hom function. -/
def freeBasepointDesc (L Z : PointedSSet.{vC_PointedDensity})
    (f : freeBasepoint.obj L.right ⟶ Z) (g : scalarPoint.{vC_PointedDensity} ⟶ Z)
    (h : freeBasepoint.map L.hom ≫ f = freeBasepointCollapse ≫ g) : L ⟶ Z :=
  Under.homMk ((Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv L.right Z f) (by
    have hh := congrArg ((Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv _ _) h
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at hh
    change L.hom ≫ (Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv _ _ f =
      (Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv (Δ[0] : SSet.{vC_PointedDensity}) scalarPoint
        (((Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv (Δ[0] : SSet.{vC_PointedDensity})
          scalarPoint).symm (𝟙 (Δ[0] : SSet.{vC_PointedDensity}))) ≫ g.right at hh
    rw [Equiv.apply_symm_apply, Category.id_comp] at hh
    have hg := g.w
    change (𝟙 (Δ[0] : SSet.{vC_PointedDensity})) ≫ g.right = Z.hom at hg
    exact hh.trans ((Category.id_comp g.right).symm.trans hg))

/-- The entire freely based source leg reads back from the actual mediator. -/
@[reassoc]
theorem freeBasepointDesc_left (L Z : PointedSSet.{vC_PointedDensity})
    (f : freeBasepoint.obj L.right ⟶ Z) (g : scalarPoint.{vC_PointedDensity} ⟶ Z)
    (h : freeBasepoint.map L.hom ≫ f = freeBasepointCollapse ≫ g) :
    freeBasepointCounit L ≫ freeBasepointDesc L Z f g h = f := by
  apply ((Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  change (Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv L.right L
      (((Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv L.right L).symm (𝟙 L.right)) ≫
      ((Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv L.right Z f) = _
  rw [Equiv.apply_symm_apply, Category.id_comp]

/-- The original selected-point leg is retained by the mediator. -/
@[reassoc]
theorem freeBasepointDesc_right (L Z : PointedSSet.{vC_PointedDensity})
    (f : freeBasepoint.obj L.right ⟶ Z) (g : scalarPoint.{vC_PointedDensity} ⟶ Z)
    (h : freeBasepoint.map L.hom ≫ f = freeBasepointCollapse ≫ g) :
    scalarPointLeg L ≫ freeBasepointDesc L Z f g h = g :=
  Under.mkIdInitial.hom_ext _ _

/-- The original free-basepoint collapse cocone is colimiting on the full original scalar object. -/
def freeBasepointIsColimit (L : PointedSSet.{vC_PointedDensity}) :
    IsColimit (PushoutCocone.mk (freeBasepointCounit L) (scalarPointLeg L) (freeBasepointSquare L)) :=
  PushoutCocone.IsColimit.mk _
    (fun s => freeBasepointDesc L s.pt s.inl s.inr s.condition)
    (fun s => freeBasepointDesc_left L s.pt s.inl s.inr s.condition)
    (fun s => freeBasepointDesc_right L s.pt s.inl s.inr s.condition)
    (fun s m hm _ => by
      apply Under.UnderMorphism.ext
      have h := congrArg ((Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv _ _) hm
      rw [Adjunction.homEquiv_naturality_right] at h
      change (Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv L.right L
          (((Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv L.right L).symm (𝟙 L.right)) ≫
            m.right = _ at h
      rw [Equiv.apply_symm_apply, Category.id_comp] at h
      change m.right = (Under.costarAdjForget (Δ[0] : SSet.{vC_PointedDensity})).homEquiv L.right s.pt s.inl
      exact h)

/-- The same original counit and selected-point maps form the genuine scalar pushout. -/
theorem freeBasepointIsPushout (L : PointedSSet.{vC_PointedDensity}) :
    IsPushout (freeBasepoint.map L.hom) freeBasepointCollapse
      (freeBasepointCounit L) (scalarPointLeg L) :=
  IsPushout.of_isColimit (freeBasepointIsColimit L)

end FreeBasepoint

section Density
variable {C : Type uC_PointedDensity} [Category.{vC_PointedDensity} C] [HasColimitsOfSize.{0, vC_PointedDensity} C]

/-- The original full simplex density cocone after an arbitrary scalar functor. -/
@[implicit_reducible]
def densityCocone (F : SSet.{vC_PointedDensity} ⥤ C) (K : SSet.{vC_PointedDensity}) :
    Cocone (tensorDiagram (SSet.stdSimplex ⋙ F) K) :=
  F.mapCocone (Presheaf.coconeOfRepresentable K)

/-- The entire original density universal property is preserved by the scalar functor. -/
def densityIsColimit (F : SSet.{vC_PointedDensity} ⥤ C) (K : SSet.{vC_PointedDensity})
    [PreservesColimitsOfSize.{0, vC_PointedDensity} F] : IsColimit (densityCocone F K) :=
  isColimitOfPreserves F (Presheaf.colimitOfRepresentable K)

/-- The actual full coend on standard simplices is the same original scalar functor. -/
def densityIso (F : SSet.{vC_PointedDensity} ⥤ C) (K : SSet.{vC_PointedDensity})
    [PreservesColimitsOfSize.{0, vC_PointedDensity} F] : tensor (SSet.stdSimplex ⋙ F) K ≅ F.obj K :=
  (tensorIsColimit (SSet.stdSimplex ⋙ F) K).coconePointUniqueUpToIso (densityIsColimit F K)

/-- Every original simplex injection reads back the original scalar map. -/
@[reassoc]
theorem densityIso_injection (F : SSet.{vC_PointedDensity} ⥤ C) (K : SSet.{vC_PointedDensity})
    [PreservesColimitsOfSize.{0, vC_PointedDensity} F] (n : SimplexCategoryᵒᵖ) (x : K.obj n) :
    tensorInjection (SSet.stdSimplex ⋙ F) K n x ≫ (densityIso F K).hom =
      F.map (SSet.yonedaEquiv.symm x) :=
  (tensorIsColimit (SSet.stdSimplex ⋙ F) K).comp_coconePointUniqueUpToIso_hom
    (densityIsColimit F K) (Opposite.op (K.elementsMk n x))

/-- The complete coend comparison is natural in every original scalar functor and weight map. -/
@[reassoc]
theorem densityIso_naturality {F G : SSet.{vC_PointedDensity} ⥤ C}
    [PreservesColimitsOfSize.{0, vC_PointedDensity} F] [PreservesColimitsOfSize.{0, vC_PointedDensity} G]
    (a : F ⟶ G) {K L : SSet.{vC_PointedDensity}} (k : K ⟶ L) :
    tensorMap (Functor.whiskerLeft SSet.stdSimplex a) k ≫ (densityIso G L).hom =
      (densityIso F K).hom ≫ a.app K ≫ G.map k := by
  apply tensor_hom_ext (SSet.stdSimplex ⋙ F) K
  intro n x
  rw [← Category.assoc, tensorInjection_tensorMap, Category.assoc, densityIso_injection,
    ← Category.assoc, ← Category.assoc, densityIso_injection]
  rw [Functor.whiskerLeft_app, a.naturality, Category.assoc, ← G.map_comp,
    SSet.yonedaEquiv_symm_comp]


end Density

section PointedDensity
variable {C : Type uC_PointedDensity} [Category.{vC_PointedDensity} C] [HasZeroObject C]
  [HasColimitsOfSize.{0, vC_PointedDensity} C] [HasPushouts C]
/-- The same original zero object supplies the coefficient zero maps. -/
local instance coefficientZeroMorphisms6 : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject
open scoped ZeroObject

/-- The genuine image of the original one-point scalar object is the original zero object. -/
def pointZeroIso (F : PointedSSet.{vC_PointedDensity} ⥤ C) [F.IsLeftAdjoint] : F.obj
  scalarPoint.{vC_PointedDensity} ≅ (0 : C) :=
  ((Under.mkIdInitial (X := (Δ[0] : SSet.{vC_PointedDensity}))).isInitialObj F).uniqueUpToIso
    HasZeroObject.zeroIsInitial

omit [HasZeroObject C] [HasPushouts C] in
/-- The full coend comparison retains the complete original selected-point scalar arrow. -/
theorem densityIso_basepoint (F : PointedSSet.{vC_PointedDensity} ⥤ C) [F.IsLeftAdjoint] (L :
  PointedSSet.{vC_PointedDensity}) :
    tensorMap (𝟙 (SSet.stdSimplex ⋙ (freeBasepoint ⋙ F))) L.hom ≫
        (densityIso (freeBasepoint ⋙ F) L.right).hom =
      (densityIso (freeBasepoint ⋙ F) (Δ[0] : SSet.{vC_PointedDensity})).hom ≫ F.map (freeBasepoint.map L.hom) := by
  have h := densityIso_naturality (𝟙 (freeBasepoint ⋙ F)) L.hom
  have hi : Functor.whiskerLeft SSet.stdSimplex (𝟙 (freeBasepoint ⋙ F)) =
      𝟙 (SSet.stdSimplex ⋙ (freeBasepoint ⋙ F)) := by
    ext n
    rfl
  rw [hi] at h
  simpa only [NatTrans.id_app, Category.id_comp, Functor.comp_map] using h

/-- The original pointed coend pushout maps to the genuine image of the scalar collapse pushout. -/
def pointedDensityPushoutMap (F : PointedSSet.{vC_PointedDensity} ⥤ C) [F.IsLeftAdjoint] (L :
  PointedSSet.{vC_PointedDensity}) :
    pointedTensor (SSet.stdSimplex ⋙ (freeBasepoint ⋙ F)) L ⟶
      pushout (F.map (freeBasepoint.map L.hom)) (F.map freeBasepointCollapse) :=
  pushout.map _ _ _ _
    (densityIso (freeBasepoint ⋙ F) L.right).hom (pointZeroIso F).inv
    (densityIso (freeBasepoint ⋙ F) (Δ[0] : SSet.{vC_PointedDensity})).hom
    (densityIso_basepoint F L)
    (by
      apply (cancel_mono (pointZeroIso F).hom).mp
      exact HasZeroObject.zeroIsTerminal.hom_ext _ _)

/-- Every comparison leg of the actual coend pushout is an isomorphism. -/
instance pointedDensityPushoutMap_isIso (F : PointedSSet.{vC_PointedDensity} ⥤ C) [F.IsLeftAdjoint]
    (L : PointedSSet.{vC_PointedDensity}) : IsIso (pointedDensityPushoutMap F L) :=
  by
    unfold pointedDensityPushoutMap
    infer_instance

/-- The actual full pointed coend on freely based standard simplices is the same original scalar functor. -/
def pointedDensityIso (F : PointedSSet.{vC_PointedDensity} ⥤ C) [F.IsLeftAdjoint] (L :
  PointedSSet.{vC_PointedDensity}) :
    pointedTensor (SSet.stdSimplex ⋙ (freeBasepoint ⋙ F)) L ≅ F.obj L :=
  asIso (pointedDensityPushoutMap F L) ≪≫
    ((freeBasepointIsPushout L).map F).isoPushout.symm

/-- The original full quotient leg of the pointed coend reads back through the actual scalar counit. -/
@[reassoc]
theorem pointedDensityIso_quotient (F : PointedSSet.{vC_PointedDensity} ⥤ C) [F.IsLeftAdjoint]
    (L : PointedSSet.{vC_PointedDensity}) :
    pointedTensorQuotient (SSet.stdSimplex ⋙ (freeBasepoint ⋙ F)) L ≫ (pointedDensityIso F L).hom =
      (densityIso (freeBasepoint ⋙ F) L.right).hom ≫ F.map (freeBasepointCounit L) := by
  change pushout.inl _ _ ≫ (pointedDensityPushoutMap F L ≫
      ((freeBasepointIsPushout L).map F).isoPushout.inv) = _
  rw [← Category.assoc]
  unfold pointedDensityPushoutMap
  rw [pushout.map, pushout.inl_desc, Category.assoc, IsPushout.inl_isoPushout_inv]

/-- The original zero leg is retained by the full pointed coend comparison. -/
@[reassoc]
theorem pointedDensityIso_zero (F : PointedSSet.{vC_PointedDensity} ⥤ C) [F.IsLeftAdjoint]
    (L : PointedSSet.{vC_PointedDensity}) :
    pointedTensorZeroLeg (SSet.stdSimplex ⋙ (freeBasepoint ⋙ F)) L ≫ (pointedDensityIso F L).hom = 0 :=
  HasZeroObject.zeroIsInitial.hom_ext _ _

/-- Every original simplex and the full pointed quotient retain their original scalar composite. -/
@[reassoc]
theorem pointedDensityIso_injection (F : PointedSSet.{vC_PointedDensity} ⥤ C) [F.IsLeftAdjoint]
    (L : PointedSSet.{vC_PointedDensity}) (n : SimplexCategoryᵒᵖ) (x : L.right.obj n) :
    tensorInjection (SSet.stdSimplex ⋙ (freeBasepoint ⋙ F)) L.right n x ≫
        pointedTensorQuotient (SSet.stdSimplex ⋙ (freeBasepoint ⋙ F)) L ≫
          (pointedDensityIso F L).hom =
      F.map (freeBasepoint.map (SSet.yonedaEquiv.symm x) ≫ freeBasepointCounit L) := by
  rw [pointedDensityIso_quotient, ← Category.assoc, densityIso_injection]
  exact (F.map_comp _ _).symm

/-- The complete pointed coend isomorphism retains every original functor transformation and scalar map. -/
@[reassoc]
theorem pointedDensityIso_naturality {F G : PointedSSet.{vC_PointedDensity} ⥤ C} [F.IsLeftAdjoint] [G.IsLeftAdjoint]
    (a : F ⟶ G) {K L : PointedSSet.{vC_PointedDensity}} (k : K ⟶ L) :
    pointedTensorMap (Functor.whiskerLeft SSet.stdSimplex (Functor.whiskerLeft freeBasepoint a)) k ≫
        (pointedDensityIso G L).hom =
      (pointedDensityIso F K).hom ≫ a.app K ≫ G.map k := by
  have hc :
      (Functor.whiskerLeft freeBasepoint a).app K.right ≫ G.map (freeBasepoint.map k.right) ≫
          G.map (freeBasepointCounit L) =
        F.map (freeBasepointCounit K) ≫ a.app K ≫ G.map k := by
    change a.app (freeBasepoint.obj K.right) ≫ G.map (freeBasepoint.map k.right) ≫
        G.map (freeBasepointCounit L) = _
    rw [← G.map_comp, freeBasepointCounit_naturality, G.map_comp,
      ← Category.assoc, ← a.naturality, Category.assoc]
  apply pushout.hom_ext
  · change pointedTensorQuotient (SSet.stdSimplex ⋙ (freeBasepoint ⋙ F)) K ≫
        (pointedTensorMap (Functor.whiskerLeft SSet.stdSimplex (Functor.whiskerLeft freeBasepoint a)) k ≫
          (pointedDensityIso G L).hom) =
      pointedTensorQuotient (SSet.stdSimplex ⋙ (freeBasepoint ⋙ F)) K ≫
        ((pointedDensityIso F K).hom ≫ a.app K ≫ G.map k)
    rw [← Category.assoc, pointedTensorMap_quotient, Category.assoc, pointedDensityIso_quotient]
    rw [← Category.assoc (pointedTensorQuotient _ K), pointedDensityIso_quotient]
    rw [← Category.assoc, densityIso_naturality]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun f => (densityIso (freeBasepoint ⋙ F) K.right).hom ≫ f) hc
  · exact HasZeroObject.zeroIsInitial.hom_ext _ _

end PointedDensity
end HomotopicalAlgebra.PointedFramingAction.FrameTensorFubini

end PointedActionPromotionPointedDensity


section PointedActionPromotionWeightedFrameFubini

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe uC_WeightedFrameFubini vC_WeightedFrameFubini
open CategoryTheory Limits MorphismProperty Simplicial MonoidalCategory
open scoped SSet.modelCategoryQuillen MonoidalCategory

namespace HomotopicalAlgebra.PointedFramingAction.FrameTensorFubini

/-- Use the original pointed simplicial smash monoidal structure. -/
local instance pointedScalarMonoidal7 : MonoidalCategory PointedSSet.{vC_WeightedFrameFubini} :=
  ScalarStructure.smashMonoidal
/-- Use the actual pointed smash symmetry. -/
local instance pointedScalarSymmetric8 : SymmetricCategory PointedSSet.{vC_WeightedFrameFubini} :=
  ScalarStructure.smashSymmetric
/-- Use the original pointed scalar internal Hom. -/
local instance pointedScalarClosed9 : MonoidalClosed PointedSSet.{vC_WeightedFrameFubini} := ScalarStructure.smashClosed
/-- Use the original pointed Kan--Quillen smash model. -/
local instance pointedScalarModel10 : IsClosedSymmetricMonoidalModelCategory
  PointedSSet.{vC_WeightedFrameFubini} := ScalarStructure.smashModel

/-- The original freely based scalar functor on every actual simplicial set and map. -/
abbrev freePoint : SSet.{vC_WeightedFrameFubini} ⥤ PointedSSet.{vC_WeightedFrameFubini} :=
  Under.costar (Δ[0] : SSet.{vC_WeightedFrameFubini})

/-- The created pointed model classes make the original free-basepoint adjunction Quillen. -/
theorem freePoint_isQuillen : (Under.costarAdjForget (Δ[0] : SSet.{vC_WeightedFrameFubini})).IsQuillenAdjunction := by
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y f hf
    exact hf
  · intro X Y f hf
    exact hf

variable {C : Type uC_WeightedFrameFubini} [Category.{vC_WeightedFrameFubini} C] [ModelCategory C] [HasZeroObject C]
  [HasColimitsOfSize.{0, vC_WeightedFrameFubini} C]

/-- The actual fixed-weight pointed scalar functor followed by the full original frame tensor. -/
abbrev weightedPointedFunctor (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini}) :
  PointedSSet.{vC_WeightedFrameFubini} ⥤ C :=
  tensorLeft K ⋙ pointedTensorBifunctor.obj A

/-- The full original scalar internal-Hom and frame adjunctions give the genuine weighted adjunction. -/
def weightedPointedAdjunction (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini}) :
    weightedPointedFunctor A K ⊣ pointedLeftHomFunctor A ⋙ ihom K :=
  (ihom.adjunction K).comp (pointedTensorHomAdjunction A)

/-- Both original frame and scalar arrows act on every weight of the actual weighted tensor functor. -/
def weightedPointedMap {A B : CosimplicialObject C} (a : A ⟶ B)
    {K K' : PointedSSet.{vC_WeightedFrameFubini}} (k : K ⟶ K') :
    weightedPointedFunctor A K ⟶ weightedPointedFunctor B K' where
  app L := pointedTensorMap a (k ⊗ₘ 𝟙 L)
  naturality {L M} l := by
    change pointedTensorMap (𝟙 A) (K ◁ l) ≫ pointedTensorMap a (k ⊗ₘ 𝟙 M) =
      pointedTensorMap a (k ⊗ₘ 𝟙 L) ≫ pointedTensorMap (𝟙 B) (K' ◁ l)
    rw [← pointedTensorMap_comp, ← pointedTensorMap_comp, Category.id_comp, Category.comp_id]
    congr 1
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_id]
    exact MonoidalCategory.whisker_exchange k l

/-- Every entire coefficient transformation has exactly its original tensor-map component. -/
theorem weightedPointedMap_app {A B : CosimplicialObject C} (a : A ⟶ B)
    {K K' : PointedSSet.{vC_WeightedFrameFubini}} (k : K ⟶ K') (L : PointedSSet.{vC_WeightedFrameFubini}) :
    (weightedPointedMap a k).app L = pointedTensorMap a (k ⊗ₘ 𝟙 L) := rfl

/-- The actual weighted tensor transformations preserve both original identity maps. -/
theorem weightedPointedMap_id (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini}) :
    weightedPointedMap (𝟙 A) (𝟙 K) = 𝟙 (weightedPointedFunctor A K) := by
  ext L
  change pointedTensorMap (𝟙 A) (𝟙 K ⊗ₘ 𝟙 L) = 𝟙 _
  rw [MonoidalCategory.id_tensorHom_id, pointedTensorMap_id]

/-- Both original composable frame and scalar maps retain their full composition law. -/
theorem weightedPointedMap_comp {A B D : CosimplicialObject C} (a : A ⟶ B) (b : B ⟶ D)
    {K K' K'' : PointedSSet.{vC_WeightedFrameFubini}} (k : K ⟶ K') (l : K' ⟶ K'') :
    weightedPointedMap (a ≫ b) (k ≫ l) = weightedPointedMap a k ≫ weightedPointedMap b l := by
  ext L
  change pointedTensorMap (a ≫ b) ((k ≫ l) ⊗ₘ 𝟙 L) =
    pointedTensorMap a (k ⊗ₘ 𝟙 L) ≫ pointedTensorMap b (l ⊗ₘ 𝟙 L)
  rw [← pointedTensorMap_comp, MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

/-- The original unpointed standard simplices enter through the actual free-basepoint functor. -/
abbrev weightedFunctor (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini}) :
  SSet.{vC_WeightedFrameFubini} ⥤ C :=
  freePoint ⋙ weightedPointedFunctor A K

/-- The entire weighted simplex adjunction is composed from the same original source adjunctions. -/
def weightedAdjunction (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini}) :
    weightedFunctor A K ⊣ pointedLeftHomFunctor A ⋙ ihom K ⋙ Under.forget (Δ[0] : SSet.{vC_WeightedFrameFubini}) :=
  (Under.costarAdjForget (Δ[0] : SSet.{vC_WeightedFrameFubini})).comp (weightedPointedAdjunction A K)

/-- The genuine arbitrary-weight cosimplicial object on every original standard simplex. -/
abbrev frame (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini}) : CosimplicialObject C :=
  SSet.stdSimplex ⋙ weightedFunctor A K

theorem frame_obj (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini}) (n : SimplexCategory) :
    (frame A K).obj n = pointedTensor A (K ⊗ freePoint.obj (SSet.stdSimplex.obj n)) := rfl

theorem frame_map (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini})
    {n m : SimplexCategory} (f : n ⟶ m) :
    (frame A K).map f = (pointedTensorBifunctor.obj A).map (K ◁ freePoint.map (SSet.stdSimplex.map f)) := rfl

/-- The original complete frame and scalar transformation on every original standard simplex. -/
def frameMap {A B : CosimplicialObject C} (a : A ⟶ B)
    {K K' : PointedSSet.{vC_WeightedFrameFubini}} (k : K ⟶ K') : frame A K ⟶ frame B K' :=
  Functor.whiskerLeft SSet.stdSimplex (Functor.whiskerLeft freePoint (weightedPointedMap a k))

/-- The complete weighted-frame component is its original tensor map at the freely based simplex. -/
theorem frameMap_app {A B : CosimplicialObject C} (a : A ⟶ B)
    {K K' : PointedSSet.{vC_WeightedFrameFubini}} (k : K ⟶ K') (n : SimplexCategory) :
    (frameMap a k).app n = pointedTensorMap a (k ⊗ₘ 𝟙 (freePoint.obj (SSet.stdSimplex.obj n))) := rfl

/-- Every original identity on the whole weighted frame is retained. -/
theorem frameMap_id (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini}) :
    frameMap (𝟙 A) (𝟙 K) = 𝟙 (frame A K) := by
  ext n
  change pointedTensorMap (𝟙 A) (𝟙 K ⊗ₘ 𝟙 _) = 𝟙 _
  rw [MonoidalCategory.id_tensorHom_id, pointedTensorMap_id]

/-- The whole weighted-frame transformations preserve both original compositions. -/
theorem frameMap_comp {A B D : CosimplicialObject C} (a : A ⟶ B) (b : B ⟶ D)
    {K K' K'' : PointedSSet.{vC_WeightedFrameFubini}} (k : K ⟶ K') (l : K' ⟶ K'') :
    frameMap (a ≫ b) (k ≫ l) = frameMap a k ≫ frameMap b l := by
  ext n
  exact congrArg (fun a => a.app (freePoint.obj (SSet.stdSimplex.obj n)))
    (weightedPointedMap_comp a b k l)

/-- The genuine full coend Fubini isomorphism on the original arbitrary weighted frame. -/
def fubiniIso (A : CosimplicialObject C) (K L : PointedSSet.{vC_WeightedFrameFubini}) :
    pointedTensor (frame A K) L ≅ pointedTensor A (K ⊗ L) := by
  let _ : (weightedPointedFunctor A K).IsLeftAdjoint := (weightedPointedAdjunction A K).isLeftAdjoint
  exact pointedDensityIso (weightedPointedFunctor A K) L

/-- The original quotient leg of coend Fubini retains the exact full density and scalar counit word. -/
@[reassoc]
theorem fubiniIso_quotient (A : CosimplicialObject C) (K L : PointedSSet.{vC_WeightedFrameFubini}) :
    pointedTensorQuotient (frame A K) L ≫ (fubiniIso A K L).hom =
      letI := (weightedPointedAdjunction A K).isLeftAdjoint
      (densityIso (weightedFunctor A K) L.right).hom ≫
        pointedTensorMap (𝟙 A) (K ◁ (freeBasepointCounit L)) := by
  let _ : (weightedPointedFunctor A K).IsLeftAdjoint := (weightedPointedAdjunction A K).isLeftAdjoint
  exact pointedDensityIso_quotient (weightedPointedFunctor A K) L

/-- Every original simplex injection and quotient reads back the actual Fubini scalar composite. -/
@[reassoc]
theorem fubiniIso_injection (A : CosimplicialObject C) (K L : PointedSSet.{vC_WeightedFrameFubini})
    (n : SimplexCategoryᵒᵖ) (x : L.right.obj n) :
    tensorInjection (frame A K) L.right n x ≫ pointedTensorQuotient (frame A K) L ≫
        (fubiniIso A K L).hom =
      pointedTensorMap (𝟙 A)
        (K ◁ (freePoint.map (SSet.yonedaEquiv.symm x) ≫ freeBasepointCounit L)) := by
  let _ : (weightedPointedFunctor A K).IsLeftAdjoint := (weightedPointedAdjunction A K).isLeftAdjoint
  exact pointedDensityIso_injection (weightedPointedFunctor A K) L n x

/-- Coend Fubini is natural in every original frame and both original scalar arrows. -/
@[reassoc]
theorem fubiniIso_naturality {A B : CosimplicialObject C} (a : A ⟶ B)
    {K K' L L' : PointedSSet.{vC_WeightedFrameFubini}} (k : K ⟶ K') (l : L ⟶ L') :
    pointedTensorMap (frameMap a k) l ≫ (fubiniIso B K' L').hom =
      (fubiniIso A K L).hom ≫ pointedTensorMap a (k ⊗ₘ l) := by
  let _ : (weightedPointedFunctor A K).IsLeftAdjoint := (weightedPointedAdjunction A K).isLeftAdjoint
  let _ : (weightedPointedFunctor B K').IsLeftAdjoint := (weightedPointedAdjunction B K').isLeftAdjoint
  have h := pointedDensityIso_naturality (weightedPointedMap a k) l
  change pointedTensorMap (frameMap a k) l ≫ (fubiniIso B K' L').hom =
    (fubiniIso A K L).hom ≫ pointedTensorMap a (k ⊗ₘ 𝟙 L) ≫ pointedTensorMap (𝟙 B) (K' ◁ l) at h
  rw [← pointedTensorMap_comp, Category.comp_id] at h
  have hs : (k ⊗ₘ 𝟙 L) ≫ (K' ◁ l) = k ⊗ₘ l := by
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_def]
  rw [hs] at h
  exact h

/-- Coend Fubini is an actual natural isomorphism on every original pointed weight. -/
def fubiniFunctorIso (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini}) :
    pointedTensorBifunctor.obj (frame A K) ≅ weightedPointedFunctor A K :=
  NatIso.ofComponents (fubiniIso A K) (by
    intro L L' l
    have h := fubiniIso_naturality (𝟙 A) (𝟙 K) l
    rw [frameMap_id, MonoidalCategory.id_tensorHom] at h
    exact h)

/-- The actual point-set associator between the two complete weighted scalar functors. -/
def weightedPointedAssociatorIso (A : CosimplicialObject C) (K L : PointedSSet.{vC_WeightedFrameFubini}) :
    weightedPointedFunctor (frame A K) L ≅ weightedPointedFunctor A (K ⊗ L) :=
  Functor.isoWhiskerLeft (tensorLeft L) (fubiniFunctorIso A K) ≪≫
    (Functor.associator (tensorLeft L) (tensorLeft K) (pointedTensorBifunctor.obj A)).symm ≪≫
      Functor.isoWhiskerRight (MonoidalCategory.tensorLeftTensor K L).symm
        (pointedTensorBifunctor.obj A)

/-- Every associator component retains the actual Fubini word and the inverse original scalar associator. -/
theorem weightedPointedAssociatorIso_hom_app (A : CosimplicialObject C) (K L M : PointedSSet.{vC_WeightedFrameFubini}) :
    (weightedPointedAssociatorIso A K L).hom.app M =
      (fubiniIso A K (L ⊗ M)).hom ≫ pointedTensorMap (𝟙 A) (α_ K L M).inv := by
  simp [weightedPointedAssociatorIso, fubiniFunctorIso, MonoidalCategory.tensorLeftTensor]
  rfl

/-- The original complete weighted-functor associator is natural in every frame and both original scalar maps. -/
@[reassoc]
theorem weightedPointedAssociatorIso_naturality {A B : CosimplicialObject C} (a : A ⟶ B)
    {K K' L L' : PointedSSet.{vC_WeightedFrameFubini}} (k : K ⟶ K') (l : L ⟶ L') :
    weightedPointedMap (frameMap a k) l ≫ (weightedPointedAssociatorIso B K' L').hom =
      (weightedPointedAssociatorIso A K L).hom ≫ weightedPointedMap a (k ⊗ₘ l) := by
  ext M
  dsimp only [weightedPointedFunctor, Functor.comp_obj, Functor.comp_map,
    MonoidalCategory.tensorLeft, MonoidalCategory.curriedTensor, pointedTensorBifunctor]
  change pointedTensorMap (frameMap a k) (l ⊗ₘ 𝟙 M) ≫
      (weightedPointedAssociatorIso B K' L').hom.app M =
    (weightedPointedAssociatorIso A K L).hom.app M ≫ pointedTensorMap a ((k ⊗ₘ l) ⊗ₘ 𝟙 M)
  rw [weightedPointedAssociatorIso_hom_app, weightedPointedAssociatorIso_hom_app]
  erw [fubiniIso_naturality_assoc, Category.assoc]
  have hs : pointedTensorMap a (k ⊗ₘ (l ⊗ₘ 𝟙 M)) ≫ pointedTensorMap (𝟙 B) (α_ K' L' M).inv =
      pointedTensorMap (𝟙 A) (α_ K L M).inv ≫ pointedTensorMap a ((k ⊗ₘ l) ⊗ₘ 𝟙 M) := by
    rw [← pointedTensorMap_comp, ← pointedTensorMap_comp, Category.comp_id, Category.id_comp]
    congr 1
    exact MonoidalCategory.associator_inv_naturality k l (𝟙 M)
  erw [hs, Category.assoc]
  exact (Category.assoc _ _ _).symm

/-- The genuine iterated weighted frame is naturally the frame of the original scalar smash product. -/
def frameAssociatorIso (A : CosimplicialObject C) (K L : PointedSSet.{vC_WeightedFrameFubini}) :
    frame (frame A K) L ≅ frame A (K ⊗ L) :=
  Functor.isoWhiskerLeft (SSet.stdSimplex ⋙ freePoint) (weightedPointedAssociatorIso A K L)

/-- Every entire iterated-frame associator retains the original Fubini and scalar-associator maps. -/
theorem frameAssociatorIso_hom_app (A : CosimplicialObject C) (K L : PointedSSet.{vC_WeightedFrameFubini})
    (n : SimplexCategory) :
    (frameAssociatorIso A K L).hom.app n =
      (fubiniIso A K (L ⊗ freePoint.obj (SSet.stdSimplex.obj n))).hom ≫
        pointedTensorMap (𝟙 A) (α_ K L (freePoint.obj (SSet.stdSimplex.obj n))).inv :=
  weightedPointedAssociatorIso_hom_app A K L _

/-- The whole iterated-frame associator retains all original frame and scalar naturalities. -/
@[reassoc]
theorem frameAssociatorIso_naturality {A B : CosimplicialObject C} (a : A ⟶ B)
    {K K' L L' : PointedSSet.{vC_WeightedFrameFubini}} (k : K ⟶ K') (l : L ⟶ L') :
    frameMap (frameMap a k) l ≫ (frameAssociatorIso B K' L').hom =
      (frameAssociatorIso A K L).hom ≫ frameMap a (k ⊗ₘ l) := by
  ext n
  exact congrArg (fun τ => τ.app (freePoint.obj (SSet.stdSimplex.obj n)))
    (weightedPointedAssociatorIso_naturality a k l)

/-- The two entire original coend-associativity words coincide before localization. -/
@[reassoc]
theorem fubiniIso_associativity (A : CosimplicialObject C) (K L M : PointedSSet.{vC_WeightedFrameFubini}) :
    pointedTensorMap (frameAssociatorIso A K L).hom (𝟙 M) ≫
        (fubiniIso A (K ⊗ L) M).hom ≫ pointedTensorMap (𝟙 A) (α_ K L M).hom =
      (fubiniIso (frame A K) L M).hom ≫ (fubiniIso A K (L ⊗ M)).hom := by
  let _ : (weightedPointedFunctor (frame A K) L).IsLeftAdjoint :=
    (weightedPointedAdjunction (frame A K) L).isLeftAdjoint
  let _ : (weightedPointedFunctor A (K ⊗ L)).IsLeftAdjoint :=
    (weightedPointedAdjunction A (K ⊗ L)).isLeftAdjoint
  have h := pointedDensityIso_naturality (weightedPointedAssociatorIso A K L).hom (𝟙 M)
  dsimp only [weightedPointedFunctor, Functor.comp_obj, Functor.comp_map,
    MonoidalCategory.tensorLeft, MonoidalCategory.curriedTensor, pointedTensorBifunctor] at h
  change pointedTensorMap (frameAssociatorIso A K L).hom (𝟙 M) ≫
      (fubiniIso A (K ⊗ L) M).hom =
    (fubiniIso (frame A K) L M).hom ≫ (weightedPointedAssociatorIso A K L).hom.app M ≫
      (weightedPointedFunctor A (K ⊗ L)).map (𝟙 M) at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id, weightedPointedAssociatorIso_hom_app] at h
  have hh := congrArg (fun f => f ≫ pointedTensorMap (𝟙 A) (α_ K L M).hom) h
  have hc : pointedTensorMap (𝟙 A) (α_ K L M).inv ≫ pointedTensorMap (𝟙 A) (α_ K L M).hom =
      𝟙 (pointedTensor A (K ⊗ (L ⊗ M))) := by
    rw [← pointedTensorMap_comp, Category.id_comp, Iso.inv_hom_id, pointedTensorMap_id]
  calc
    _ = (pointedTensorMap (frameAssociatorIso A K L).hom (𝟙 M) ≫
        (fubiniIso A (K ⊗ L) M).hom) ≫ pointedTensorMap (𝟙 A) (α_ K L M).hom :=
      (Category.assoc _ _ _).symm
    _ = ((fubiniIso (frame A K) L M).hom ≫ ((fubiniIso A K (L ⊗ M)).hom ≫
        pointedTensorMap (𝟙 A) (α_ K L M).inv)) ≫ pointedTensorMap (𝟙 A) (α_ K L M).hom := hh
    _ = (fubiniIso (frame A K) L M).hom ≫ (fubiniIso A K (L ⊗ M)).hom ≫
        (pointedTensorMap (𝟙 A) (α_ K L M).inv ≫ pointedTensorMap (𝟙 A) (α_ K L M).hom) :=
      (Category.assoc _ _ _).trans (congrArg (fun f => (fubiniIso (frame A K) L M).hom ≫ f)
        (Category.assoc _ _ _))
    _ = _ := by rw [hc, Category.comp_id]


/-- The genuine weighted frame has the original weighted tensor as its degree-zero object. -/
def frameZeroIso (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini}) :
    (frame A K).obj ⦋0⦌ ≅ pointedTensor A K :=
  (tensorUnitIso (frame A K)).symm ≪≫ fubiniIso A K pointedUnit ≪≫
    (pointedTensorBifunctor.obj A).mapIso (ρ_ K)

/-- The entire original degree-zero comparison retains its actual unit, Fubini and scalar-unitor word. -/
theorem frameZeroIso_hom (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini}) :
    (frameZeroIso A K).hom = (tensorUnitIso (frame A K)).inv ≫ (fubiniIso A K pointedUnit).hom ≫
      pointedTensorMap (𝟙 A) (ρ_ K).hom := rfl

/-- Every original frame and scalar map preserves the entire original weighted degree-zero word. -/
@[reassoc]
theorem frameZeroIso_naturality {A B : CosimplicialObject C} (a : A ⟶ B)
    {K K' : PointedSSet.{vC_WeightedFrameFubini}} (k : K ⟶ K') :
    (frameMap a k).app ⦋0⦌ ≫ (frameZeroIso B K').hom =
      (frameZeroIso A K).hom ≫ pointedTensorMap a k := by
  have hu : (frameMap a k).app ⦋0⦌ ≫ (tensorUnitIso (frame B K')).inv =
      (tensorUnitIso (frame A K)).inv ≫ pointedTensorMap (frameMap a k) (𝟙 pointedUnit) := by
    apply (cancel_mono (tensorUnitIso (frame B K')).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [tensorUnitIso_naturality, Iso.inv_hom_id_assoc]
  have hs : pointedTensorMap a (k ⊗ₘ 𝟙 pointedUnit) ≫ pointedTensorMap (𝟙 B) (ρ_ K').hom =
      pointedTensorMap (𝟙 A) (ρ_ K).hom ≫ pointedTensorMap a k := by
    rw [← pointedTensorMap_comp, ← pointedTensorMap_comp, Category.comp_id, Category.id_comp]
    congr 1
    rw [MonoidalCategory.tensorHom_id]
    exact MonoidalCategory.rightUnitor_naturality k
  rw [frameZeroIso_hom, frameZeroIso_hom]
  rw [← Category.assoc ((frameMap a k).app ⦋0⦌) (tensorUnitIso (frame B K')).inv, hu]
  simp only [Category.assoc]
  rw [fubiniIso_naturality_assoc, hs]

/-- The full Fubini word at the scalar unit agrees with the actual weighted frame-zero comparison. -/
@[reassoc]
theorem fubiniIso_right_unit (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini}) :
    (tensorUnitIso (frame A K)).hom ≫ (frameZeroIso A K).hom =
      (fubiniIso A K pointedUnit).hom ≫ pointedTensorMap (𝟙 A) (ρ_ K).hom := by
  rw [frameZeroIso_hom]
  simp only [Iso.hom_inv_id_assoc]

/-- The entire iterated-frame associator retains the same original degree-zero Fubini comparison. -/
@[reassoc]
theorem frameAssociatorIso_zero (A : CosimplicialObject C) (K L : PointedSSet.{vC_WeightedFrameFubini}) :
    (frameAssociatorIso A K L).hom.app ⦋0⦌ ≫ (frameZeroIso A (K ⊗ L)).hom =
      (frameZeroIso (frame A K) L).hom ≫ (fubiniIso A K L).hom := by
  have hn : pointedTensorMap (𝟙 (frame A K)) (ρ_ L).hom ≫ (fubiniIso A K L).hom =
      (fubiniIso A K (L ⊗ pointedUnit)).hom ≫ pointedTensorMap (𝟙 A) (K ◁ (ρ_ L).hom) := by
    have h := fubiniIso_naturality (𝟙 A) (𝟙 K) (ρ_ L).hom
    rw [frameMap_id, MonoidalCategory.id_tensorHom] at h
    exact h
  have hc : pointedTensorMap (𝟙 A) (α_ K L pointedUnit).hom ≫
      pointedTensorMap (𝟙 A) (K ◁ (ρ_ L).hom) = pointedTensorMap (𝟙 A) (ρ_ (K ⊗ L)).hom := by
    rw [← pointedTensorMap_comp, Category.id_comp]
    exact congrArg (fun f => pointedTensorMap (𝟙 A) f) (MonoidalCategory.rightUnitor_tensor_hom K L).symm
  apply (cancel_epi (tensorUnitIso (frame (frame A K) L)).hom).mp
  rw [← Category.assoc, ← tensorUnitIso_naturality]
  rw [Category.assoc, fubiniIso_right_unit, fubiniIso_right_unit_assoc, hn]
  have h := congrArg (fun f => f ≫ pointedTensorMap (𝟙 A) (K ◁ (ρ_ L).hom))
    (fubiniIso_associativity A K L pointedUnit)
  calc
    _ = (pointedTensorMap (frameAssociatorIso A K L).hom (𝟙 pointedUnit) ≫
        (fubiniIso A (K ⊗ L) pointedUnit).hom ≫ pointedTensorMap (𝟙 A) (α_ K L pointedUnit).hom) ≫
          pointedTensorMap (𝟙 A) (K ◁ (ρ_ L).hom) := by
      simp only [Category.assoc]
      rw [hc]
    _ = ((fubiniIso (frame A K) L pointedUnit).hom ≫ (fubiniIso A K (L ⊗ pointedUnit)).hom) ≫
        pointedTensorMap (𝟙 A) (K ◁ (ρ_ L).hom) := h
    _ = _ := Category.assoc _ _ _

/-- Actual scalar cofibrancy and the full original frame Quillen laws prove the entire weighted adjunction Quillen. -/
theorem weightedAdjunction_isQuillen (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_WeightedFrameFubini}) : (weightedAdjunction A K).IsQuillenAdjunction := by
  let : IsCofibrant K := pointedSSet_isCofibrant K
  let : (ihom.adjunction K).IsQuillenAdjunction := ihomAdjunction_isQuillenAdjunction_of_isCofibrant K
  let : (pointedTensorHomAdjunction A).IsQuillenAdjunction := pointedTensorHomAdjunction_isQuillen A hA hW
  let : (weightedPointedAdjunction A K).IsQuillenAdjunction := Adjunction.IsQuillenAdjunction.comp (adj :=
    ihom.adjunction K) (pointedTensorHomAdjunction A)
  let : (Under.costarAdjForget (Δ[0] : SSet.{vC_WeightedFrameFubini})).IsQuillenAdjunction := freePoint_isQuillen
  exact Adjunction.IsQuillenAdjunction.comp (adj := Under.costarAdjForget (Δ[0] : SSet.{vC_WeightedFrameFubini}))
    (weightedPointedAdjunction A K)

omit [ModelCategory C] [HasZeroObject C] [HasColimitsOfSize.{0, vC_WeightedFrameFubini} C] in
/-- The complete actual standard-boundary cocone after an arbitrary original scalar functor. -/
@[implicit_reducible]
def mappedBoundaryCocone (F : SSet.{vC_WeightedFrameFubini} ⥤ C) (n : SimplexCategory) :
    Cocone (SimplexCategory.reedy.latchingDiagram (SSet.stdSimplex ⋙ F) n) :=
  F.mapCocone (SSet.StandardSimplexBoundaryColimit.boundaryCocone n)

omit [ModelCategory C] [HasZeroObject C] [HasColimitsOfSize.{0, vC_WeightedFrameFubini} C] in
/-- Preserving the actual boundary colimit retains its complete caller universal property. -/
def mappedBoundaryIsColimit (F : SSet.{vC_WeightedFrameFubini} ⥤ C) (n : SimplexCategory)
    [PreservesColimitsOfShape (SimplexCategory.reedy.Latching n) F] :
    IsColimit (mappedBoundaryCocone F n) :=
  isColimitOfPreserves F (SSet.StandardSimplexBoundaryColimit.isColimit n)

/-- The full original boundary cocone is carried through the actual free, smash and frame tensor functors. -/
abbrev latchingCocone (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini}) (n : SimplexCategory) :=
  mappedBoundaryCocone (weightedFunctor A K) n

/-- Genuine left-adjoint preservation proves this same complete caller boundary cocone colimiting. -/
def latchingIsColimit (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini}) (n : SimplexCategory) :
    IsColimit (latchingCocone A K n) := by
  let : PreservesColimitsOfSize.{0, 0} (weightedFunctor A K) := (weightedAdjunction A K).leftAdjoint_preservesColimits
  exact mappedBoundaryIsColimit (weightedFunctor A K) n

/-- Every original proper face retains its actual weighted boundary coefficient map. -/
@[reassoc]
theorem latchingCocone_ι (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini}) (n : SimplexCategory)
    (a : SimplexCategory.reedy.Latching n) :
    (latchingCocone A K n).ι.app a ≫ (weightedFunctor A K).map (SSet.boundary n.len).ι =
      (frame A K).map (SimplexCategory.reedy.latchingArrow a) := by
  change (weightedFunctor A K).map ((SSet.StandardSimplexBoundaryColimit.boundaryCocone n).ι.app a) ≫
      (weightedFunctor A K).map (SSet.boundary n.len).ι = _
  rw [← Functor.map_comp, SSet.StandardSimplexBoundaryColimit.boundaryCocone_ι]
  rfl

/-- The complete original caller latching arrow is the actual weighted standard-boundary inclusion. -/
theorem latchingMapWith_eq (A : CosimplicialObject C) (K : PointedSSet.{vC_WeightedFrameFubini}) (n : SimplexCategory) :
    SimplexCategory.reedy.latchingMapWith (frame A K) n (latchingCocone A K n) (latchingIsColimit A K n) =
      (weightedFunctor A K).map (SSet.boundary n.len).ι := by
  apply (latchingIsColimit A K n).hom_ext
  intro a
  rw [ReedyStructure.latchingMapWith_ι, latchingCocone_ι]

/-- Every complete caller latching colimit retains the entire original weighted boundary arrow. -/
theorem latchingMapWith_cofibration (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_WeightedFrameFubini}) (n : SimplexCategory)
    (c : Cocone (SimplexCategory.reedy.latchingDiagram (frame A K) n)) (hc : IsColimit c) :
    cofibrations C (SimplexCategory.reedy.latchingMapWith (frame A K) n c hc) := by
  let : (weightedAdjunction A K).IsQuillenAdjunction := weightedAdjunction_isQuillen A hA hW K
  let e := (latchingIsColimit A K n).coconePointUniqueUpToIso hc
  have he : (weightedFunctor A K).map (SSet.boundary n.len).ι =
      e.hom ≫ SimplexCategory.reedy.latchingMapWith (frame A K) n c hc := by
    apply (latchingIsColimit A K n).hom_ext
    intro a
    rw [← Category.assoc, (latchingIsColimit A K n).comp_coconePointUniqueUpToIso_hom hc a,
      ReedyStructure.latchingMapWith_ι, latchingCocone_ι]
  have hb : cofibrations C ((weightedFunctor A K).map (SSet.boundary n.len).ι) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrations (adj := weightedAdjunction A K) _
      ((cofibration_iff _).mp (SSet.modelCategoryQuillen.cofibration_of_mono (SSet.boundary n.len).ι))
  rw [he] at hb
  exact ((cofibrations C).cancel_left_of_respectsIso _ _).mp hb

/-- All genuine canonical latching maps of the arbitrary-weight frame are cofibrations. -/
theorem latching_cofibration (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_WeightedFrameFubini}) (n : SimplexCategory) :
    cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy (frame A K) n) :=
  latchingMapWith_cofibration A hA hW K n (colimit.cocone _) (colimit.isColimit _)

/-- Every original simplex operator gives a weak structure map of the genuine arbitrary-weight frame. -/
theorem frame_map_weak (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_WeightedFrameFubini}) {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C ((frame A K).map f) := by
  let : (weightedAdjunction A K).IsQuillenAdjunction := weightedAdjunction_isQuillen A hA hW K
  let : IsCofibrant (SSet.stdSimplex.obj n : SSet.{vC_WeightedFrameFubini}) :=
    CompatibleCotensorFraming.simplicial_isCofibrant _
  let : IsCofibrant (SSet.stdSimplex.obj m : SSet.{vC_WeightedFrameFubini}) :=
    CompatibleCotensorFraming.simplicial_isCofibrant _
  let : WeakEquivalence (SSet.stdSimplex.map f) := SSet.StandardSimplexWeakMaps.map_weak f
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := weightedAdjunction A K)
      (SSet.stdSimplex.map f))

end HomotopicalAlgebra.PointedFramingAction.FrameTensorFubini

end PointedActionPromotionWeightedFrameFubini


section PointedActionPromotionRepresentableUnit

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe uC_RepresentableUnit vC_RepresentableUnit
open CategoryTheory Limits Simplicial MonoidalCategory
open scoped MonoidalCategory ZeroObject

namespace HomotopicalAlgebra.PointedFramingAction.FrameTensorFubini

section Representable
variable {C : Type uC_RepresentableUnit} [Category.{vC_RepresentableUnit} C] [HasZeroObject C]
  [HasColimitsOfSize.{0, vC_RepresentableUnit} C] [HasPushouts C]
/-- The same original zero object supplies the coefficient zero maps. -/
local instance coefficientZeroMorphisms11 : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject

/-- The actual full pointed tensor at a freely based simplex represents its original frame coefficient. -/
def representableHomEquiv (A : CosimplicialObject C) (n : SimplexCategory) (Y : C) :
    (pointedTensor A (freeBasepoint.obj (SSet.stdSimplex.obj n)) ⟶ Y) ≃ (A.obj n ⟶ Y) :=
  (pointedTensorHomEquiv A (freeBasepoint.obj (SSet.stdSimplex.obj n)) Y).trans
    (((Under.costarAdjForget (Δ[0] : SSet.{vC_RepresentableUnit})).homEquiv (SSet.stdSimplex.obj n) (pointedLeftHom
      A Y)).trans
      SSet.yonedaEquiv)

/-- The entire representable tensor Hom function is the original pointed transpose followed by coYoneda. -/
theorem representableHomEquiv_apply (A : CosimplicialObject C) (n : SimplexCategory) (Y : C)
    (f : pointedTensor A (freeBasepoint.obj (SSet.stdSimplex.obj n)) ⟶ Y) :
    representableHomEquiv A n Y f =
      SSet.yonedaEquiv ((Under.costarAdjForget (Δ[0] : SSet.{vC_RepresentableUnit})).homEquiv (SSet.stdSimplex.obj n)
        (pointedLeftHom A Y) (pointedTensorHomEquiv A (freeBasepoint.obj (SSet.stdSimplex.obj n)) Y f)) := rfl

/-- The complete representable tensor transpose retains every original target map. -/
theorem representableHomEquiv_target (A : CosimplicialObject C) (n : SimplexCategory)
    {Y Y' : C} (g : Y ⟶ Y') (f : pointedTensor A (freeBasepoint.obj (SSet.stdSimplex.obj n)) ⟶ Y) :
    representableHomEquiv A n Y' (f ≫ g) = representableHomEquiv A n Y f ≫ g := by
  rw [representableHomEquiv_apply, representableHomEquiv_apply, pointedTensorHomEquiv_target]
  have h := (Under.costarAdjForget (Δ[0] : SSet.{vC_RepresentableUnit})).homEquiv_naturality_right
    (pointedTensorHomEquiv A (freeBasepoint.obj (SSet.stdSimplex.obj n)) Y f)
    ((pointedLeftHomFunctor A).map g)
  exact (congrArg SSet.yonedaEquiv h).trans (by rw [SSet.yonedaEquiv_comp]; rfl)

/-- The complete representable Hom function retains every original full frame map. -/
theorem representableHomEquiv_frame {A B : CosimplicialObject C} (a : A ⟶ B)
    (n : SimplexCategory) (Y : C)
    (f : pointedTensor B (freeBasepoint.obj (SSet.stdSimplex.obj n)) ⟶ Y) :
    representableHomEquiv A n Y
      (pointedTensorMap a (𝟙 (freeBasepoint.obj (SSet.stdSimplex.obj n))) ≫ f) =
      a.app n ≫ representableHomEquiv B n Y f := by
  rw [representableHomEquiv_apply, representableHomEquiv_apply, pointedTensorHomEquiv_source]
  have h := (Under.costarAdjForget (Δ[0] : SSet.{vC_RepresentableUnit})).homEquiv_naturality_right
    (pointedTensorHomEquiv B (freeBasepoint.obj (SSet.stdSimplex.obj n)) Y f)
    (pointedHomPrecomp a ((SimplicialObject.const C).obj Y))
  exact (congrArg SSet.yonedaEquiv h).trans (by rw [SSet.yonedaEquiv_comp]; rfl)

/-- The original standard-simplex operator is retained by the entire representable tensor transpose. -/
theorem representableHomEquiv_operator (A : CosimplicialObject C) {n m : SimplexCategory}
    (f : n ⟶ m) (Y : C)
    (h : pointedTensor A (freeBasepoint.obj (SSet.stdSimplex.obj m)) ⟶ Y) :
    representableHomEquiv A n Y
      (pointedTensorMap (𝟙 A) (freeBasepoint.map (SSet.stdSimplex.map f)) ≫ h) =
      A.map f ≫ representableHomEquiv A m Y h := by
  rw [representableHomEquiv_apply, representableHomEquiv_apply, pointedTensorHomEquiv_parameter]
  have hh := (Under.costarAdjForget (Δ[0] : SSet.{vC_RepresentableUnit})).homEquiv_naturality_left
    (SSet.stdSimplex.map f)
    (pointedTensorHomEquiv A (freeBasepoint.obj (SSet.stdSimplex.obj m)) Y h)
  exact (congrArg SSet.yonedaEquiv hh).trans (by
    rw [← SSet.yonedaEquiv_naturality]
    exact ResolutionHomComplex.left_map_apply A Y f.op _)

/-- The actual tensor at a freely based simplex is the same original frame coefficient, with both inverse maps. -/
def representableTensorIso (A : CosimplicialObject C) (n : SimplexCategory) :
    pointedTensor A (freeBasepoint.obj (SSet.stdSimplex.obj n)) ≅ A.obj n where
  hom := (representableHomEquiv A n (A.obj n)).symm (𝟙 _)
  inv := representableHomEquiv A n (pointedTensor A (freeBasepoint.obj (SSet.stdSimplex.obj n))) (𝟙 _)
  hom_inv_id := by
    apply (representableHomEquiv A n (pointedTensor A (freeBasepoint.obj (SSet.stdSimplex.obj n)))).injective
    rw [representableHomEquiv_target, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    have h := representableHomEquiv_target A n ((representableHomEquiv A n (A.obj n)).symm (𝟙 _))
      (𝟙 (pointedTensor A (freeBasepoint.obj (SSet.stdSimplex.obj n))))
    rw [Category.id_comp, Equiv.apply_symm_apply] at h
    exact h.symm

/-- Every original frame transformation preserves the entire representable tensor comparison. -/
@[reassoc]
theorem representableTensorIso_frame {A B : CosimplicialObject C} (a : A ⟶ B) (n : SimplexCategory) :
    pointedTensorMap a (𝟙 (freeBasepoint.obj (SSet.stdSimplex.obj n))) ≫ (representableTensorIso B n).hom =
      (representableTensorIso A n).hom ≫ a.app n := by
  apply (representableHomEquiv A n (B.obj n)).injective
  rw [representableHomEquiv_frame, representableHomEquiv_target]
  change a.app n ≫ representableHomEquiv B n (B.obj n)
      ((representableHomEquiv B n (B.obj n)).symm (𝟙 _)) =
    representableHomEquiv A n (A.obj n) ((representableHomEquiv A n (A.obj n)).symm (𝟙 _)) ≫ a.app n
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Category.comp_id, Category.id_comp]

/-- Every original simplex operator preserves the entire representable tensor comparison. -/
@[reassoc]
theorem representableTensorIso_operator (A : CosimplicialObject C) {n m : SimplexCategory}
    (f : n ⟶ m) :
    pointedTensorMap (𝟙 A) (freeBasepoint.map (SSet.stdSimplex.map f)) ≫ (representableTensorIso A m).hom =
      (representableTensorIso A n).hom ≫ A.map f := by
  apply (representableHomEquiv A n (A.obj m)).injective
  rw [representableHomEquiv_operator, representableHomEquiv_target]
  change A.map f ≫ representableHomEquiv A m (A.obj m)
      ((representableHomEquiv A m (A.obj m)).symm (𝟙 _)) =
    representableHomEquiv A n (A.obj n) ((representableHomEquiv A n (A.obj n)).symm (𝟙 _)) ≫ A.map f
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Category.comp_id, Category.id_comp]

/-- The original full frame is its representable tensor presentation, naturally in every degree. -/
def representableFrameIso (A : CosimplicialObject C) :
    SSet.stdSimplex ⋙ (freeBasepoint ⋙ pointedTensorBifunctor.obj A) ≅ A :=
  NatIso.ofComponents (representableTensorIso A) (fun {_ _} f => representableTensorIso_operator A f)

/-- The original free-basepoint counit has the original identity as its transpose. -/
theorem freeBasepointCounit_transpose (K : PointedSSet.{vC_RepresentableUnit}) :
    (Under.costarAdjForget (Δ[0] : SSet.{vC_RepresentableUnit})).homEquiv K.right K
      (freeBasepointCounit K) = 𝟙 K.right :=
  ((Under.costarAdjForget (Δ[0] : SSet.{vC_RepresentableUnit})).homEquiv K.right K).apply_symm_apply _

/-- The entire representable transpose at an arbitrary scalar simplex retains its original coend injection. -/
theorem representableHomEquiv_generator (A : CosimplicialObject C) (n : SimplexCategory)
    (K : PointedSSet.{vC_RepresentableUnit}) (x : K.right.obj (Opposite.op n)) :
    representableHomEquiv A n (pointedTensor A K)
      (pointedTensorMap (𝟙 A)
        (freeBasepoint.map (SSet.yonedaEquiv.symm x) ≫ freeBasepointCounit K)) =
      tensorInjection A K.right (Opposite.op n) x ≫ pointedTensorQuotient A K := by
  let r := pointedTensorHomEquiv A K (pointedTensor A K) (𝟙 _)
  have hc : (Under.costarAdjForget (Δ[0] : SSet.{vC_RepresentableUnit})).homEquiv K.right (pointedLeftHom A
    (pointedTensor A K))
      (freeBasepointCounit K ≫ r) = r.right := by
    rw [Adjunction.homEquiv_naturality_right, freeBasepointCounit_transpose]
    exact Category.id_comp _
  have ht := pointedTensorHomEquiv_parameter A
    (freeBasepoint.map (SSet.yonedaEquiv.symm x) ≫ freeBasepointCounit K) (pointedTensor A K) (𝟙 _)
  rw [Category.comp_id] at ht
  rw [representableHomEquiv_apply, ht]
  have hh : (Under.costarAdjForget (Δ[0] : SSet.{vC_RepresentableUnit})).homEquiv (SSet.stdSimplex.obj n)
      (pointedLeftHom A (pointedTensor A K))
      ((freeBasepoint.map (SSet.yonedaEquiv.symm x) ≫ freeBasepointCounit K) ≫ r) =
      SSet.yonedaEquiv.symm x ≫ r.right :=
    (congrArg ((Under.costarAdjForget (Δ[0] : SSet.{vC_RepresentableUnit})).homEquiv (SSet.stdSimplex.obj n)
      (pointedLeftHom A (pointedTensor A K))) (Category.assoc _ _ _)).trans
      (((Under.costarAdjForget (Δ[0] : SSet.{vC_RepresentableUnit})).homEquiv_naturality_left
        (SSet.yonedaEquiv.symm x) (freeBasepointCounit K ≫ r)).trans
          (congrArg (fun h => SSet.yonedaEquiv.symm x ≫ h) hc))
  exact (congrArg SSet.yonedaEquiv hh).trans (by
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact congrArg (fun f => tensorInjection A K.right (Opposite.op n) x ≫ f)
      (Category.comp_id (pointedTensorQuotient A K)))

/-- Every original scalar simplex reads back through both actual representable tensor maps. -/
@[reassoc]
theorem representableTensorIso_generator (A : CosimplicialObject C) (n : SimplexCategory)
    (K : PointedSSet.{vC_RepresentableUnit}) (x : K.right.obj (Opposite.op n)) :
    pointedTensorMap (𝟙 A)
        (freeBasepoint.map (SSet.yonedaEquiv.symm x) ≫ freeBasepointCounit K) =
      (representableTensorIso A n).hom ≫ tensorInjection A K.right (Opposite.op n) x ≫
        pointedTensorQuotient A K := by
  apply (representableHomEquiv A n (pointedTensor A K)).injective
  rw [representableHomEquiv_generator, representableHomEquiv_target]
  change _ = representableHomEquiv A n (A.obj n) ((representableHomEquiv A n (A.obj n)).symm (𝟙 _)) ≫ _
  rw [Equiv.apply_symm_apply, Category.id_comp]

/-- The complete pointed density comparison is induced by the actual original representable-frame maps. -/
theorem pointedDensityIso_representable (A : CosimplicialObject C) (K : PointedSSet.{vC_RepresentableUnit}) :
    letI := (pointedTensorHomAdjunction A).isLeftAdjoint
    (pointedDensityIso (pointedTensorBifunctor.obj A) K).hom =
      pointedTensorMap (representableFrameIso A).hom (𝟙 K) := by
  let _ : (pointedTensorBifunctor.obj A).IsLeftAdjoint := (pointedTensorHomAdjunction A).isLeftAdjoint
  apply pushout.hom_ext
  · apply tensor_hom_ext (SSet.stdSimplex ⋙ (freeBasepoint ⋙ pointedTensorBifunctor.obj A)) K.right
    intro n x
    change tensorInjection _ K.right n x ≫ pointedTensorQuotient _ K ≫
        (pointedDensityIso (pointedTensorBifunctor.obj A) K).hom =
      tensorInjection _ K.right n x ≫ pointedTensorQuotient _ K ≫
        pointedTensorMap (representableFrameIso A).hom (𝟙 K)
    rw [pointedDensityIso_injection, pointedTensorMap_quotient, ← Category.assoc,
      tensorInjection_tensorMap]
    change pointedTensorMap (𝟙 A)
        (freeBasepoint.map (SSet.yonedaEquiv.symm x) ≫ freeBasepointCounit K) =
      ((representableTensorIso A n.unop).hom ≫ tensorInjection A K.right n x) ≫ pointedTensorQuotient A K
    exact (representableTensorIso_generator A n.unop K x).trans (Category.assoc _ _ _).symm
  · exact HasZeroObject.zeroIsInitial.hom_ext _ _

end Representable

section FrameUnit
variable {C : Type uC_RepresentableUnit} [Category.{vC_RepresentableUnit} C] [ModelCategory C] [HasZeroObject C]
  [HasColimitsOfSize.{0, vC_RepresentableUnit} C]
/-- Use the original pointed simplicial smash monoidal structure. -/
local instance pointedScalarMonoidal12 : MonoidalCategory PointedSSet.{vC_RepresentableUnit} :=
  ScalarStructure.smashMonoidal

/-- The genuine left scalar unitor gives the entire actual weighted tensor functor its unit isomorphism. -/
def weightedPointedUnitIso (A : CosimplicialObject C) :
    weightedPointedFunctor A pointedUnit.{vC_RepresentableUnit} ≅ pointedTensorBifunctor.obj A :=
  NatIso.ofComponents (fun K => (pointedTensorBifunctor.obj A).mapIso (λ_ K)) (by
    intro K L k
    change (pointedTensorBifunctor.obj A).map (pointedUnit ◁ k) ≫
        (pointedTensorBifunctor.obj A).map (λ_ L).hom =
      (pointedTensorBifunctor.obj A).map (λ_ K).hom ≫ (pointedTensorBifunctor.obj A).map k
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (pointedTensorBifunctor.obj A).map (MonoidalCategory.leftUnitor_naturality k))

/-- The whole unit weighted frame is naturally the same original frame in every degree. -/
def frameUnitIso (A : CosimplicialObject C) : frame A pointedUnit.{vC_RepresentableUnit} ≅ A :=
  Functor.isoWhiskerLeft (SSet.stdSimplex ⋙ freeBasepoint) (weightedPointedUnitIso A) ≪≫
    representableFrameIso A

/-- Each unit-frame component retains its entire original scalar-unitor and representable tensor word. -/
theorem frameUnitIso_hom_app (A : CosimplicialObject C) (n : SimplexCategory) :
    (frameUnitIso A).hom.app n =
      pointedTensorMap (𝟙 A) (λ_ (freeBasepoint.obj (SSet.stdSimplex.obj n))).hom ≫
        (representableTensorIso A n).hom := rfl

/-- The complete unit-frame isomorphism preserves every original full frame map. -/
@[reassoc]
theorem frameUnitIso_naturality {A B : CosimplicialObject C} (a : A ⟶ B) :
    frameMap a (𝟙 pointedUnit.{vC_RepresentableUnit}) ≫ (frameUnitIso B).hom = (frameUnitIso A).hom ≫ a := by
  ext n
  rw [NatTrans.comp_app, NatTrans.comp_app, frameMap_app, frameUnitIso_hom_app, frameUnitIso_hom_app,
    MonoidalCategory.id_tensorHom_id]
  have h : pointedTensorMap a (𝟙 (pointedUnit ⊗ freeBasepoint.obj (SSet.stdSimplex.obj n))) ≫
        pointedTensorMap (𝟙 B) (λ_ (freeBasepoint.obj (SSet.stdSimplex.obj n))).hom =
      pointedTensorMap (𝟙 A) (λ_ (freeBasepoint.obj (SSet.stdSimplex.obj n))).hom ≫
        pointedTensorMap a (𝟙 (freeBasepoint.obj (SSet.stdSimplex.obj n))) := by
    rw [← pointedTensorMap_comp, ← pointedTensorMap_comp, Category.comp_id, Category.id_comp,
      Category.id_comp, Category.comp_id]
  erw [← Category.assoc, h, Category.assoc, representableTensorIso_frame]
  exact (Category.assoc _ _ _).symm

/-- The entire left unit Fubini word is induced by the original unit-frame comparison. -/
@[reassoc]
theorem fubiniIso_left_unit (A : CosimplicialObject C) (K : PointedSSet.{vC_RepresentableUnit}) :
    pointedTensorMap (frameUnitIso A).hom (𝟙 K) =
      (fubiniIso A pointedUnit K).hom ≫ pointedTensorMap (𝟙 A) (λ_ K).hom := by
  let _ : (weightedPointedFunctor A pointedUnit).IsLeftAdjoint :=
    (weightedPointedAdjunction A pointedUnit).isLeftAdjoint
  let _ : (pointedTensorBifunctor.obj A).IsLeftAdjoint := (pointedTensorHomAdjunction A).isLeftAdjoint
  have h := pointedDensityIso_naturality (weightedPointedUnitIso A).hom (𝟙 K)
  change pointedTensorMap
      (Functor.whiskerLeft SSet.stdSimplex (Functor.whiskerLeft freeBasepoint (weightedPointedUnitIso A).hom))
      (𝟙 K) ≫ (pointedDensityIso (pointedTensorBifunctor.obj A) K).hom =
    (fubiniIso A pointedUnit K).hom ≫ (weightedPointedUnitIso A).hom.app K ≫
      (pointedTensorBifunctor.obj A).map (𝟙 K) at h
  erw [pointedDensityIso_representable, CategoryTheory.Functor.map_id, Category.comp_id] at h
  erw [← pointedTensorMap_comp, Category.id_comp] at h
  exact h

/-- The original unit-frame degree-zero map retains the actual ordinary tensor unit comparison. -/
@[reassoc]
theorem frameUnitIso_zero (A : CosimplicialObject C) :
    (frameUnitIso A).hom.app ⦋0⦌ = (frameZeroIso A pointedUnit.{vC_RepresentableUnit}).hom ≫ (tensorUnitIso A).hom := by
  have hu := tensorUnitIso_naturality (frameUnitIso A).hom
  rw [fubiniIso_left_unit] at hu
  have he : (λ_ pointedUnit.{vC_RepresentableUnit}).hom = (ρ_ pointedUnit.{vC_RepresentableUnit}).hom :=
    MonoidalCategory.unitors_equal
  rw [he] at hu
  apply (cancel_epi (tensorUnitIso (frame A pointedUnit)).hom).mp
  rw [← Category.assoc, fubiniIso_right_unit]
  exact hu.symm

end FrameUnit
end HomotopicalAlgebra.PointedFramingAction.FrameTensorFubini

end PointedActionPromotionRepresentableUnit


section PointedActionPromotionFrameDerivedComparison

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe uC_FrameDerivedComparison vC_FrameDerivedComparison
open CategoryTheory Limits MorphismProperty Simplicial
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.PointedFramingAction.FrameDerivedComparison

variable {C : Type uC_FrameDerivedComparison} [Category.{vC_FrameDerivedComparison} C] [ModelCategory C]
  [HasZeroObject C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

/-- The actual right resolution supplies the left-to-two-sided HFC comparison. -/
def toTwoSided (A : CosimplicialObject C) (Y : C) :
    pointedLeftHom A (d.R.obj Y) ⟶ pointedHom A ((rightFrame d).obj Y) :=
  pointedHomPostcomp A ((rightResolution d).app Y)

/-- The canonical degree-zero augmentation supplies the actual other comparison leg. -/
def fromZero (A : CosimplicialObject C) (Y : C) :
    pointedRightHom (A.obj ⦋0⦌) ((rightFrame d).obj Y) ⟶
      pointedHom A ((rightFrame d).obj Y) :=
  pointedHomPrecomp (FrameCoherence.augmentation A) ((rightFrame d).obj Y)

/-- The unchanged original Q counit acts on the whole degree-zero right HFC. -/
def zeroToChosen (A : CosimplicialObject C) (Y : C) :
    pointedRightHom (A.obj ⦋0⦌) ((rightFrame d).obj Y) ⟶ pointedRightSpace d (A.obj ⦋0⦌) Y :=
  pointedHomPrecomp ((CosimplicialObject.const C).map (d.q.app (A.obj ⦋0⦌)))
    ((rightFrame d).obj Y)

theorem toTwoSided_weak (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n)) (Y : C) :
    weakEquivalences PointedSSet.{vC_FrameDerivedComparison} (toTwoSided d A Y) := by
  change weakEquivalences SSet.{vC_FrameDerivedComparison}
    (ResolutionHomComplex.fromCoaugmentation A ((rightResolution d).app Y))
  let _ : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  exact (weakEquivalence_iff _).mp
    (GeneratedFrameHomComparison.fromCoaugmentation_weak A ((rightFrame d).obj Y)
      ((rightResolution d).app Y) hA (rightFrame_matching_fibration d Y)
      (rightResolution_weak d Y))

theorem fromZero_weak (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f)) (Y : C) :
    weakEquivalences PointedSSet.{vC_FrameDerivedComparison} (fromZero d A Y) := by
  change weakEquivalences SSet.{vC_FrameDerivedComparison}
    (ResolutionHomComplex.fromAugmentation (FrameCoherence.augmentation A) ((rightFrame d).obj Y))
  let _ : IsCofibrant (A.obj ⦋0⦌) := LeftFrameHomWeakEquivalence.coefficient_isCofibrant A hA ⦋0⦌
  exact (weakEquivalence_iff _).mp
    (GeneratedFrameHomComparison.fromAugmentation_weak A ((rightFrame d).obj Y)
      (FrameCoherence.augmentation A) hA (rightFrame_matching_fibration d Y)
      (FrameCoherence.augmentation_weak A hW))

theorem zeroToChosen_weak (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n)) (Y : C) :
    weakEquivalences PointedSSet.{vC_FrameDerivedComparison} (zeroToChosen d A Y) := by
  change weakEquivalences SSet.{vC_FrameDerivedComparison}
    (RightFrameHomBoundary.precomp (d.q.app (A.obj ⦋0⦌)) ((rightFrame d).obj Y))
  let _ : IsCofibrant (A.obj ⦋0⦌) := LeftFrameHomWeakEquivalence.coefficient_isCofibrant A hA ⦋0⦌
  let _ : IsCofibrant ((𝟭 C).obj (A.obj ⦋0⦌)) :=
    LeftFrameHomWeakEquivalence.coefficient_isCofibrant A hA ⦋0⦌
  let _ : IsCofibrant (d.Q.obj (A.obj ⦋0⦌)) := d.q_cofibrant _
  let _ : WeakEquivalence (d.q.app (A.obj ⦋0⦌)) := (weakEquivalence_iff _).mpr (d.q_trivialFibration _).2
  exact (weakEquivalence_iff _).mp
    (RightFrameHomBoundary.precomp_weak _ _ (rightFrame_matching_fibration d Y))

/-- The canonical comparison consists of three actual HFC maps, with only its weak leg inverted. -/
def hfcIso (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f)) (Y : C) :
    pointedProjection.obj (pointedLeftHom A (d.R.obj Y)) ≅ pointedRightHoSpace d (A.obj ⦋0⦌) Y := by
  let _ : IsIso (pointedProjection.map (toTwoSided d A Y)) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC_FrameDerivedComparison}) _
      (toTwoSided_weak d A hA Y)
  let _ : IsIso (pointedProjection.map (fromZero d A Y)) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC_FrameDerivedComparison}) _
      (fromZero_weak d A hA hW Y)
  let _ : IsIso (pointedProjection.map (zeroToChosen d A Y)) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC_FrameDerivedComparison}) _
      (zeroToChosen_weak d A hA Y)
  exact asIso (pointedProjection.map (toTwoSided d A Y)) ≪≫
    (asIso (pointedProjection.map (fromZero d A Y))).symm ≪≫
      asIso (pointedProjection.map (zeroToChosen d A Y))

theorem toTwoSided_target (A : CosimplicialObject C) {Y Y' : C} (g : Y ⟶ Y') :
    pointedHomPostcomp A ((SimplicialObject.const C).map (d.R.map g)) ≫ toTwoSided d A Y' =
      toTwoSided d A Y ≫ pointedHomPostcomp A ((rightFrame d).map g) := by
  unfold toTwoSided
  rw [← pointedHomPostcomp_comp, ← pointedHomPostcomp_comp]
  exact congrArg (pointedHomPostcomp A) ((rightResolution d).naturality g)

theorem fromZero_target (A : CosimplicialObject C) {Y Y' : C} (g : Y ⟶ Y') :
    pointedHomPostcomp ((CosimplicialObject.const C).obj (A.obj ⦋0⦌)) ((rightFrame d).map g) ≫
        fromZero d A Y' =
      fromZero d A Y ≫ pointedHomPostcomp A ((rightFrame d).map g) :=
  (pointedHomPrecomp_postcomp (FrameCoherence.augmentation A) ((rightFrame d).map g)).symm

theorem zeroToChosen_target (A : CosimplicialObject C) {Y Y' : C} (g : Y ⟶ Y') :
    pointedHomPostcomp ((CosimplicialObject.const C).obj (A.obj ⦋0⦌)) ((rightFrame d).map g) ≫
        zeroToChosen d A Y' =
      zeroToChosen d A Y ≫ pointedRightTargetMap d (A.obj ⦋0⦌) g :=
  (pointedHomPrecomp_postcomp ((CosimplicialObject.const C).map (d.q.app (A.obj ⦋0⦌)))
    ((rightFrame d).map g)).symm

/-- The complete HFC word retains every original target arrow. -/
theorem hfcIso_target (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    {Y Y' : C} (g : Y ⟶ Y') :
    pointedProjection.map (pointedHomPostcomp A ((SimplicialObject.const C).map (d.R.map g))) ≫
        (hfcIso d A hA hW Y').hom =
      (hfcIso d A hA hW Y).hom ≫ pointedProjection.map (pointedRightTargetMap d (A.obj ⦋0⦌) g) := by
  let _ : IsIso (pointedProjection.map (fromZero d A Y)) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC_FrameDerivedComparison}) _
      (fromZero_weak d A hA hW Y)
  let _ : IsIso (pointedProjection.map (fromZero d A Y')) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC_FrameDerivedComparison}) _
      (fromZero_weak d A hA hW Y')
  have hρ := congrArg pointedProjection.map (toTwoSided_target d A g)
  have hα := congrArg pointedProjection.map (fromZero_target d A g)
  have hq := congrArg pointedProjection.map (zeroToChosen_target d A g)
  simp only [Functor.map_comp] at hρ hα hq
  have hi : pointedProjection.map (pointedHomPostcomp A ((rightFrame d).map g)) ≫
        inv (pointedProjection.map (fromZero d A Y')) =
      inv (pointedProjection.map (fromZero d A Y)) ≫
        pointedProjection.map (pointedHomPostcomp
          ((CosimplicialObject.const C).obj (A.obj ⦋0⦌)) ((rightFrame d).map g)) := by
    apply (cancel_epi (pointedProjection.map (fromZero d A Y))).mp
    rw [← Category.assoc, ← hα, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id, IsIso.hom_inv_id_assoc]
  change _ ≫ (pointedProjection.map (toTwoSided d A Y') ≫
      inv (pointedProjection.map (fromZero d A Y')) ≫ pointedProjection.map (zeroToChosen d A Y')) =
    (pointedProjection.map (toTwoSided d A Y) ≫
      inv (pointedProjection.map (fromZero d A Y)) ≫ pointedProjection.map (zeroToChosen d A Y)) ≫ _
  calc
    _ = (pointedProjection.map (toTwoSided d A Y) ≫
        pointedProjection.map (pointedHomPostcomp A ((rightFrame d).map g))) ≫
      inv (pointedProjection.map (fromZero d A Y')) ≫ pointedProjection.map (zeroToChosen d A Y') := by
        rw [← Category.assoc, hρ]
    _ = pointedProjection.map (toTwoSided d A Y) ≫
      (inv (pointedProjection.map (fromZero d A Y)) ≫
        pointedProjection.map (pointedHomPostcomp
          ((CosimplicialObject.const C).obj (A.obj ⦋0⦌)) ((rightFrame d).map g))) ≫
        pointedProjection.map (zeroToChosen d A Y') := by
          simpa only [Category.assoc] using congrArg
            (fun z => pointedProjection.map (toTwoSided d A Y) ≫ z ≫
              pointedProjection.map (zeroToChosen d A Y')) hi
    _ = _ := by
      simp only [Category.assoc]
      rw [hq]

theorem toTwoSided_source {A B : CosimplicialObject C} (a : A ⟶ B) (Y : C) :
    pointedHomPrecomp a ((SimplicialObject.const C).obj (d.R.obj Y)) ≫ toTwoSided d A Y =
      toTwoSided d B Y ≫ pointedHomPrecomp a ((rightFrame d).obj Y) :=
  pointedHomPrecomp_postcomp a ((rightResolution d).app Y)

theorem fromZero_source {A B : CosimplicialObject C} (a : A ⟶ B) (Y : C) :
    pointedHomPrecomp ((CosimplicialObject.const C).map (a.app ⦋0⦌)) ((rightFrame d).obj Y) ≫
        fromZero d A Y =
      fromZero d B Y ≫ pointedHomPrecomp a ((rightFrame d).obj Y) := by
  unfold fromZero
  rw [← pointedHomPrecomp_comp, ← pointedHomPrecomp_comp, FrameCoherence.augmentation_square]

theorem zeroToChosen_source {A B : CosimplicialObject C} (a : A ⟶ B) (Y : C) :
    pointedHomPrecomp ((CosimplicialObject.const C).map (a.app ⦋0⦌)) ((rightFrame d).obj Y) ≫
        zeroToChosen d A Y =
      zeroToChosen d B Y ≫ pointedRightSourceMap d (a.app ⦋0⦌) Y := by
  unfold zeroToChosen pointedRightSourceMap
  rw [← pointedHomPrecomp_comp, ← pointedHomPrecomp_comp,
    ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun f => pointedHomPrecomp ((CosimplicialObject.const C).map f) ((rightFrame d).obj Y))
    (d.q.naturality (a.app ⦋0⦌)).symm

/-- The genuine comparison is natural in an entire frame map, through its original degree-zero arrow. -/
theorem hfcIso_source {A B : CosimplicialObject C}
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hWA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hB : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy B n))
    (hWB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (a : A ⟶ B) (Y : C) :
    pointedProjection.map (pointedHomPrecomp a ((SimplicialObject.const C).obj (d.R.obj Y))) ≫
        (hfcIso d A hA hWA Y).hom =
      (hfcIso d B hB hWB Y).hom ≫ pointedProjection.map (pointedRightSourceMap d (a.app ⦋0⦌) Y) := by
  let _ : IsIso (pointedProjection.map (fromZero d A Y)) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC_FrameDerivedComparison}) _
      (fromZero_weak d A hA hWA Y)
  let _ : IsIso (pointedProjection.map (fromZero d B Y)) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC_FrameDerivedComparison}) _
      (fromZero_weak d B hB hWB Y)
  have hρ := congrArg pointedProjection.map (toTwoSided_source d a Y)
  have hα := congrArg pointedProjection.map (fromZero_source d a Y)
  have hq := congrArg pointedProjection.map (zeroToChosen_source d a Y)
  simp only [Functor.map_comp] at hρ hα hq
  have hi : pointedProjection.map (pointedHomPrecomp a ((rightFrame d).obj Y)) ≫
        inv (pointedProjection.map (fromZero d A Y)) =
      inv (pointedProjection.map (fromZero d B Y)) ≫
        pointedProjection.map (pointedHomPrecomp
          ((CosimplicialObject.const C).map (a.app ⦋0⦌)) ((rightFrame d).obj Y)) := by
    apply (cancel_epi (pointedProjection.map (fromZero d B Y))).mp
    rw [← Category.assoc, ← hα, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id, IsIso.hom_inv_id_assoc]
  change _ ≫ (pointedProjection.map (toTwoSided d A Y) ≫
      inv (pointedProjection.map (fromZero d A Y)) ≫ pointedProjection.map (zeroToChosen d A Y)) =
    (pointedProjection.map (toTwoSided d B Y) ≫
      inv (pointedProjection.map (fromZero d B Y)) ≫ pointedProjection.map (zeroToChosen d B Y)) ≫ _
  calc
    _ = (pointedProjection.map (toTwoSided d B Y) ≫
        pointedProjection.map (pointedHomPrecomp a ((rightFrame d).obj Y))) ≫
      inv (pointedProjection.map (fromZero d A Y)) ≫ pointedProjection.map (zeroToChosen d A Y) := by
        rw [← Category.assoc, hρ]
    _ = pointedProjection.map (toTwoSided d B Y) ≫
      (inv (pointedProjection.map (fromZero d B Y)) ≫
        pointedProjection.map (pointedHomPrecomp
          ((CosimplicialObject.const C).map (a.app ⦋0⦌)) ((rightFrame d).obj Y))) ≫
        pointedProjection.map (zeroToChosen d A Y) := by
          simpa only [Category.assoc] using congrArg
            (fun z => pointedProjection.map (toTwoSided d B Y) ≫ z ≫
              pointedProjection.map (zeroToChosen d A Y)) hi
    _ = _ := by
      simp only [Category.assoc]
      rw [hq]

/-- Equality of coefficient Ho arrows gives equality of the complete original right HFC source maps. -/
theorem chosenRightSource_eq_of_ho {U V : C} (f g : U ⟶ V)
    (hfg : (weakEquivalences C).Q.map f = (weakEquivalences C).Q.map g) (Y : C) :
    pointedProjection.map (pointedRightSourceMap d f Y) =
      pointedProjection.map (pointedRightSourceMap d g Y) := by
  apply (cancel_epi (mappingHoOriginalIso d V Y).hom).mp
  rw [← mappingHoOriginalIso_source, ← mappingHoOriginalIso_source, hfg]

/-- Actual right-frame precomposition from a cofibrant source depends only on the coefficient Ho arrow. -/
theorem rightPrecomp_eq_of_ho {U V : C} [IsCofibrant U] (f g : U ⟶ V)
    (hfg : (weakEquivalences C).Q.map f = (weakEquivalences C).Q.map g) (Y : C) :
    pointedProjection.map (pointedHomPrecomp ((CosimplicialObject.const C).map f) ((rightFrame d).obj Y)) =
      pointedProjection.map (pointedHomPrecomp ((CosimplicialObject.const C).map g) ((rightFrame d).obj Y)) := by
  let qU := pointedHomPrecomp ((CosimplicialObject.const C).map (d.q.app U)) ((rightFrame d).obj Y)
  have hqU : weakEquivalences PointedSSet.{vC_FrameDerivedComparison} qU := by
    change weakEquivalences SSet.{vC_FrameDerivedComparison} (RightFrameHomBoundary.precomp (d.q.app U)
      ((rightFrame d).obj Y))
    let _ : IsCofibrant ((𝟭 C).obj U) := inferInstanceAs (IsCofibrant U)
    let _ : IsCofibrant (d.Q.obj U) := d.q_cofibrant U
    let _ : WeakEquivalence (d.q.app U) := (weakEquivalence_iff _).mpr (d.q_trivialFibration U).2
    exact (weakEquivalence_iff _).mp
      (RightFrameHomBoundary.precomp_weak _ _ (rightFrame_matching_fibration d Y))
  let _ : IsIso (pointedProjection.map qU) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC_FrameDerivedComparison}) _ hqU
  apply (cancel_mono (pointedProjection.map qU)).mp
  have hf := zeroToChosen_source d ((CosimplicialObject.const C).map f) Y
  have hg := zeroToChosen_source d ((CosimplicialObject.const C).map g) Y
  have hfs := congrArg pointedProjection.map hf
  have hgs := congrArg pointedProjection.map hg
  simp only [Functor.map_comp, Functor.const_map_app] at hfs hgs
  change pointedProjection.map (pointedHomPrecomp ((CosimplicialObject.const C).map f) ((rightFrame d).obj Y)) ≫
      pointedProjection.map (zeroToChosen d ((CosimplicialObject.const C).obj U) Y) =
    pointedProjection.map (pointedHomPrecomp ((CosimplicialObject.const C).map g) ((rightFrame d).obj Y)) ≫
      pointedProjection.map (zeroToChosen d ((CosimplicialObject.const C).obj U) Y)
  rw [hfs, hgs, chosenRightSource_eq_of_ho d f g hfg Y]

section Tensor
variable [HasColimitsOfSize.{0, vC_FrameDerivedComparison} C]

/-- The arbitrary-frame tensor transpose retains the full original R target map. -/
theorem tensorHomEquivHo_target (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_FrameDerivedComparison}) {Y Y' : C} (g : Y ⟶ Y')
    (h : (weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj A).obj K) ⟶ (weakEquivalences C).Q.obj Y) :
    FrameCoherence.tensorHomEquivHo d A hA hW K Y' (h ≫ (weakEquivalences C).Q.map g) =
      FrameCoherence.tensorHomEquivHo d A hA hW K Y h ≫
        pointedProjection.map (pointedHomPostcomp A ((SimplicialObject.const C).map (d.R.map g))) := by
  let _ : (pointedTensorHomAdjunction A).IsQuillenAdjunction := pointedTensorHomAdjunction_isQuillen A hA hW
  let _ : IsCofibrant K := pointedSSet_isCofibrant K
  let _ : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  let _ : IsFibrant (d.R.obj Y') := d.r_fibrant Y'
  let _ : IsCofibrant ((pointedTensorBifunctor.obj A).obj K) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := pointedTensorHomAdjunction A) inferInstance
  obtain ⟨f, hf⟩ := map_surjective_of_isLocalization (weakEquivalences C).Q _ _
    (h ≫ (rHomotopyIso d Y).hom)
  simp only [FrameCoherence.tensorHomEquivHo, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Category.id_comp]
  change QuillenOrdinaryHoHom.homEquiv (pointedTensorHomAdjunction A) K (d.R.obj Y')
      ((h ≫ (weakEquivalences C).Q.map g) ≫ (rHomotopyIso d Y').hom) =
    QuillenOrdinaryHoHom.homEquiv (pointedTensorHomAdjunction A) K (d.R.obj Y)
      (h ≫ (rHomotopyIso d Y).hom) ≫ _
  rw [Category.assoc, rHomotopyIso_naturality, ← Category.assoc, ← hf,
    ← Functor.map_comp, QuillenOrdinaryHoHom.homEquiv_map, QuillenOrdinaryHoHom.homEquiv_map]
  change pointedProjection.map ((pointedTensorHomAdjunction A).homEquiv K (d.R.obj Y') (f ≫ d.R.map g)) =
    pointedProjection.map ((pointedTensorHomAdjunction A).homEquiv K (d.R.obj Y) f) ≫
      pointedProjection.map ((pointedLeftHomFunctor A).map (d.R.map g))
  rw [← Functor.map_comp]
  exact congrArg pointedProjection.map ((pointedTensorHomAdjunction A).homEquiv_naturality_right f (d.R.map g))

/-- The arbitrary-frame tensor transpose retains every original pointed weight arrow. -/
theorem tensorHomEquivHo_weight (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    {K L : PointedSSet.{vC_FrameDerivedComparison}} (k : K ⟶ L) (Y : C)
    (h : (weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj A).obj L) ⟶ (weakEquivalences C).Q.obj Y) :
    FrameCoherence.tensorHomEquivHo d A hA hW K Y
        ((weakEquivalences C).Q.map ((pointedTensorBifunctor.obj A).map k) ≫ h) =
      pointedProjection.map k ≫ FrameCoherence.tensorHomEquivHo d A hA hW L Y h := by
  let _ : (pointedTensorHomAdjunction A).IsQuillenAdjunction := pointedTensorHomAdjunction_isQuillen A hA hW
  let _ : IsCofibrant K := pointedSSet_isCofibrant K
  let _ : IsCofibrant L := pointedSSet_isCofibrant L
  let _ : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  let _ : IsCofibrant ((pointedTensorBifunctor.obj A).obj L) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := pointedTensorHomAdjunction A) inferInstance
  obtain ⟨f, hf⟩ := map_surjective_of_isLocalization (weakEquivalences C).Q _ _
    (h ≫ (rHomotopyIso d Y).hom)
  simp only [FrameCoherence.tensorHomEquivHo, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Category.id_comp]
  rw [Category.assoc, ← hf, ← Functor.map_comp,
    QuillenOrdinaryHoHom.homEquiv_map, QuillenOrdinaryHoHom.homEquiv_map]
  change pointedProjection.map ((pointedTensorHomAdjunction A).homEquiv K (d.R.obj Y)
      ((pointedTensorBifunctor.obj A).map k ≫ f)) =
    pointedProjection.map k ≫ pointedProjection.map ((pointedTensorHomAdjunction A).homEquiv L (d.R.obj Y) f)
  rw [← Functor.map_comp]
  exact congrArg pointedProjection.map ((pointedTensorHomAdjunction A).homEquiv_naturality_left k f)

/-- Every arbitrary cofibrant frame represents the same actual derived mapping HFC at its original degree zero. -/
def frameHomEquiv (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_FrameDerivedComparison}) (Y : C) :
    ((weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj A).obj K) ⟶ (weakEquivalences C).Q.obj Y) ≃
      (pointedProjection.obj K ⟶
        ((mappingHo d).obj (Opposite.op ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)))).obj
          ((weakEquivalences C).Q.obj Y)) :=
  (FrameCoherence.tensorHomEquivHo d A hA hW K Y).trans
    (Iso.homCongr (Iso.refl _) ((hfcIso d A hA hW Y) ≪≫ (mappingHoOriginalIso d (A.obj ⦋0⦌) Y).symm))

theorem frameHomEquiv_apply (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_FrameDerivedComparison}) (Y : C)
    (h : (weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj A).obj K) ⟶ (weakEquivalences C).Q.obj Y) :
    frameHomEquiv d A hA hW K Y h =
      FrameCoherence.tensorHomEquivHo d A hA hW K Y h ≫ (hfcIso d A hA hW Y).hom ≫
        (mappingHoOriginalIso d (A.obj ⦋0⦌) Y).inv := by
  simp only [frameHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Category.id_comp, Iso.trans_hom, Iso.symm_hom]

theorem frameHomEquiv_weight (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    {K L : PointedSSet.{vC_FrameDerivedComparison}} (k : K ⟶ L) (Y : C)
    (h : (weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj A).obj L) ⟶ (weakEquivalences C).Q.obj Y) :
    frameHomEquiv d A hA hW K Y ((weakEquivalences C).Q.map ((pointedTensorBifunctor.obj A).map k) ≫ h) =
      pointedProjection.map k ≫ frameHomEquiv d A hA hW L Y h := by
  rw [frameHomEquiv_apply, frameHomEquiv_apply, tensorHomEquivHo_weight]
  simp only [Category.assoc]

theorem frameHomEquiv_target (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_FrameDerivedComparison}) {Y Y' : C} (g : Y ⟶ Y')
    (h : (weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj A).obj K) ⟶ (weakEquivalences C).Q.obj Y) :
    frameHomEquiv d A hA hW K Y' (h ≫ (weakEquivalences C).Q.map g) =
      frameHomEquiv d A hA hW K Y h ≫
        ((mappingHo d).obj (Opposite.op ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)))).map
          ((weakEquivalences C).Q.map g) := by
  rw [frameHomEquiv_apply, frameHomEquiv_apply, tensorHomEquivHo_target]
  have hn : pointedProjection.map (pointedHomPostcomp A ((SimplicialObject.const C).map (d.R.map g))) ≫
      (hfcIso d A hA hW Y').hom ≫ (mappingHoOriginalIso d (A.obj ⦋0⦌) Y').inv =
    (hfcIso d A hA hW Y).hom ≫ (mappingHoOriginalIso d (A.obj ⦋0⦌) Y).inv ≫
      ((mappingHo d).obj (Opposite.op ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)))).map
        ((weakEquivalences C).Q.map g) := by
    rw [← Category.assoc, hfcIso_target, Category.assoc, mappingHoOriginalIso_target_inv]
  simpa only [Category.assoc] using congrArg
    (fun z => FrameCoherence.tensorHomEquivHo d A hA hW K Y h ≫ z) hn

/-- Frame transposition depends on the original degree-zero map in the coefficient homotopy category. -/
theorem frameHomEquiv_source {A B : CosimplicialObject C}
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hWA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hB : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy B n))
    (hWB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (a : A ⟶ B) (K : PointedSSet.{vC_FrameDerivedComparison}) (Y : C)
    (h : (weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj B).obj K) ⟶ (weakEquivalences C).Q.obj Y) :
    frameHomEquiv d A hA hWA K Y
        ((weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K) ≫ h) =
      frameHomEquiv d B hB hWB K Y h ≫
        ((mappingHo d).map ((weakEquivalences C).Q.map (a.app ⦋0⦌)).op).app ((weakEquivalences C).Q.obj Y) := by
  rw [frameHomEquiv_apply, frameHomEquiv_apply, FrameCoherence.tensorHomEquivHo_source]
  have hn : pointedProjection.map (pointedHomPrecomp a ((SimplicialObject.const C).obj (d.R.obj Y))) ≫
      (hfcIso d A hA hWA Y).hom ≫ (mappingHoOriginalIso d (A.obj ⦋0⦌) Y).inv =
    (hfcIso d B hB hWB Y).hom ≫ (mappingHoOriginalIso d (B.obj ⦋0⦌) Y).inv ≫
      ((mappingHo d).map ((weakEquivalences C).Q.map (a.app ⦋0⦌)).op).app ((weakEquivalences C).Q.obj Y) := by
    rw [← Category.assoc, hfcIso_source, Category.assoc, mappingHoOriginalIso_source_inv]
  simpa only [Category.assoc] using congrArg
    (fun z => FrameCoherence.tensorHomEquivHo d B hB hWB K Y h ≫ z) hn

include d in
/-- All original frame tensor maps are determined by the degree-zero arrow in Ho(C), including formal inverse
relations. -/
theorem tensorMap_eq_of_hoDegreeZero {A B : CosimplicialObject C}
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hWA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hB : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy B n))
    (hWB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (a b : A ⟶ B)
    (hab : (weakEquivalences C).Q.map (a.app ⦋0⦌) = (weakEquivalences C).Q.map (b.app ⦋0⦌))
    (K : PointedSSet.{vC_FrameDerivedComparison}) :
    (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K) =
      (weakEquivalences C).Q.map ((pointedTensorBifunctor.map b).app K) := by
  apply (frameHomEquiv d A hA hWA K ((pointedTensorBifunctor.obj B).obj K)).injective
  have ha := frameHomEquiv_source d hA hWA hB hWB a K ((pointedTensorBifunctor.obj B).obj K) (𝟙 _)
  have hb := frameHomEquiv_source d hA hWA hB hWB b K ((pointedTensorBifunctor.obj B).obj K) (𝟙 _)
  simp only [Category.comp_id] at ha hb
  rw [ha, hb, hab]

section Closed
variable [HasLimitsOfSize.{0, vC_FrameDerivedComparison} C]

/-- The actual closed Hom functions identify an arbitrary frame tensor with the chosen derived tensor. -/
def canonicalHomEquiv (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_FrameDerivedComparison}) (Y : C) :
    ((weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj A).obj K) ⟶ (weakEquivalences C).Q.obj Y) ≃
      (((tensorAction d).obj (pointedProjection.obj K)).obj ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)) ⟶
        (weakEquivalences C).Q.obj Y) :=
  (frameHomEquiv d A hA hW K Y).trans
    (closedHomEquiv d ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)) (pointedProjection.obj K)
      ((weakEquivalences C).Q.obj Y)).symm

theorem canonicalHomEquiv_target (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_FrameDerivedComparison}) {Y Y' : C} (g : Y ⟶ Y')
    (h : (weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj A).obj K) ⟶ (weakEquivalences C).Q.obj Y) :
    canonicalHomEquiv d A hA hW K Y' (h ≫ (weakEquivalences C).Q.map g) =
      canonicalHomEquiv d A hA hW K Y h ≫ (weakEquivalences C).Q.map g := by
  apply (closedHomEquiv d ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)) (pointedProjection.obj K)
    ((weakEquivalences C).Q.obj Y')).injective
  change closedHomEquiv d _ _ _ ((closedHomEquiv d _ _ _).symm
    (frameHomEquiv d A hA hW K Y' (h ≫ (weakEquivalences C).Q.map g))) =
    closedHomEquiv d _ _ _ ((closedHomEquiv d _ _ _).symm (frameHomEquiv d A hA hW K Y h) ≫
      (weakEquivalences C).Q.map g)
  rw [Equiv.apply_symm_apply, closedHomEquiv_target, Equiv.apply_symm_apply, frameHomEquiv_target]

/-- The canonical Hom comparison keeps the entire source frame map and its original Ho degree-zero arrow. -/
theorem canonicalHomEquiv_source {A B : CosimplicialObject C}
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hWA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hB : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy B n))
    (hWB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (a : A ⟶ B) (K : PointedSSet.{vC_FrameDerivedComparison}) (Y : C)
    (h : (weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj B).obj K) ⟶ (weakEquivalences C).Q.obj Y) :
    canonicalHomEquiv d A hA hWA K Y
        ((weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K) ≫ h) =
      ((tensorAction d).obj (pointedProjection.obj K)).map ((weakEquivalences C).Q.map (a.app ⦋0⦌)) ≫
        canonicalHomEquiv d B hB hWB K Y h := by
  apply (closedHomEquiv d ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)) (pointedProjection.obj K)
    ((weakEquivalences C).Q.obj Y)).injective
  change closedHomEquiv d _ _ _ ((closedHomEquiv d _ _ _).symm
      (frameHomEquiv d A hA hWA K Y ((weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K) ≫ h))) =
    closedHomEquiv d _ _ _ (((tensorAction d).obj (pointedProjection.obj K)).map
      ((weakEquivalences C).Q.map (a.app ⦋0⦌)) ≫
        (closedHomEquiv d _ _ _).symm (frameHomEquiv d B hB hWB K Y h))
  rw [Equiv.apply_symm_apply, closedHomEquiv_source, Equiv.apply_symm_apply, frameHomEquiv_source]

/-- The canonical Hom comparison retains every original weight arrow. -/
theorem canonicalHomEquiv_weight (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    {K L : PointedSSet.{vC_FrameDerivedComparison}} (k : K ⟶ L) (Y : C)
    (h : (weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj A).obj L) ⟶ (weakEquivalences C).Q.obj Y) :
    canonicalHomEquiv d A hA hW K Y
        ((weakEquivalences C).Q.map ((pointedTensorBifunctor.obj A).map k) ≫ h) =
      ((tensorAction d).map (pointedProjection.map k)).app ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)) ≫
        canonicalHomEquiv d A hA hW L Y h := by
  apply (closedHomEquiv d ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)) (pointedProjection.obj K)
    ((weakEquivalences C).Q.obj Y)).injective
  change closedHomEquiv d _ _ _ ((closedHomEquiv d _ _ _).symm
      (frameHomEquiv d A hA hW K Y ((weakEquivalences C).Q.map ((pointedTensorBifunctor.obj A).map k) ≫ h))) =
    closedHomEquiv d _ _ _ (((tensorAction d).map (pointedProjection.map k)).app
      ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)) ≫
        (closedHomEquiv d _ _ _).symm (frameHomEquiv d A hA hW L Y h))
  rw [Equiv.apply_symm_apply, closedHomEquiv_weight, Equiv.apply_symm_apply, frameHomEquiv_weight]

/-- The original-target Hom comparison is an isomorphism between the two actual lifted coyoneda functors. -/
def originalCoyonedaIso (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_FrameDerivedComparison}) :
    (weakEquivalences C).Q ⋙ uliftCoyoneda.{max uC_FrameDerivedComparison (vC_FrameDerivedComparison + 1)}.obj
      (Opposite.op ((weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj A).obj K))) ≅
    (weakEquivalences C).Q ⋙ uliftCoyoneda.{max uC_FrameDerivedComparison (vC_FrameDerivedComparison + 1)}.obj
      (Opposite.op (((tensorAction d).obj (pointedProjection.obj K)).obj
        ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)))) :=
  NatIso.ofComponents (fun Y =>
    (Equiv.ulift.trans ((canonicalHomEquiv d A hA hW K Y).trans Equiv.ulift.symm)).toIso)
    (fun {_ _} g => by
      apply ConcreteCategory.hom_ext
      intro h
      apply ULift.ext
      exact canonicalHomEquiv_target d A hA hW K g h.down)

/-- Localization and fully faithful lifted coyoneda construct the actual canonical tensor comparison. -/
def canonicalIso (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_FrameDerivedComparison}) :
    (weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj A).obj K) ≅
      ((tensorAction d).obj (pointedProjection.obj K)).obj ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)) :=
  ((uliftCoyoneda.{max uC_FrameDerivedComparison (vC_FrameDerivedComparison + 1)} (C := (weakEquivalences
    C).Localization)).preimageIso
    ((Localization.fullyFaithfulWhiskeringLeft (weakEquivalences C).Q (weakEquivalences C)
      (Type (max uC_FrameDerivedComparison (vC_FrameDerivedComparison + 1)))).preimageIso (originalCoyonedaIso d
        A hA hW K)).symm).unop

/-- The actual comparison is characterized by its complete original Hom equivalence. -/
theorem canonicalIso_hom_comp (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_FrameDerivedComparison}) (Y : C)
    (h : ((tensorAction d).obj (pointedProjection.obj K)).obj ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)) ⟶
      (weakEquivalences C).Q.obj Y) :
    (canonicalIso d A hA hW K).hom ≫ h = (canonicalHomEquiv d A hA hW K Y).symm h := by
  let J := originalCoyonedaIso d A hA hW K
  let hL := Localization.fullyFaithfulWhiskeringLeft (weakEquivalences C).Q (weakEquivalences C)
    (Type (max uC_FrameDerivedComparison (vC_FrameDerivedComparison + 1)))
  let e := hL.preimageIso J
  have hy := Functor.map_preimage
    (uliftCoyoneda.{max uC_FrameDerivedComparison (vC_FrameDerivedComparison + 1)} (C := (weakEquivalences
      C).Localization)) e.inv
  have hl := hL.map_preimage J.inv
  have hx := congrArg (fun τ => (τ.app ((weakEquivalences C).Q.obj Y)) (ULift.up h)) hy
  have hz := congrArg (fun τ => (τ.app Y) (ULift.up h)) hl
  have he := congrArg ULift.down (hx.trans hz)
  change (canonicalIso d A hA hW K).hom ≫ h = (canonicalHomEquiv d A hA hW K Y).symm h at he
  exact he

/-- The canonical comparison retains all frame maps and all original degree-zero arrows. -/
theorem canonicalIso_source {A B : CosimplicialObject C}
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hWA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hB : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy B n))
    (hWB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (a : A ⟶ B) (K : PointedSSet.{vC_FrameDerivedComparison}) :
    (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K) ≫ (canonicalIso d B hB hWB K).hom =
      (canonicalIso d A hA hWA K).hom ≫
        ((tensorAction d).obj (pointedProjection.obj K)).map ((weakEquivalences C).Q.map (a.app ⦋0⦌)) := by
  let Y := (framedTensor d K).obj (B.obj ⦋0⦌)
  let t := ((tensorAction d).obj (pointedProjection.obj K)).map ((weakEquivalences C).Q.map (a.app ⦋0⦌))
  have hAcomp := canonicalIso_hom_comp d A hA hWA K Y t
  have hBcomp := canonicalIso_hom_comp d B hB hWB K Y (𝟙 _)
  have hBcomp' := (Category.comp_id ((canonicalIso d B hB hWB K).hom)).symm.trans hBcomp
  let eA := canonicalHomEquiv d A hA hWA K Y
  let eB := canonicalHomEquiv d B hB hWB K Y
  have hBId : eB (canonicalIso d B hB hWB K).hom = 𝟙 _ :=
    (congrArg eB hBcomp').trans (eB.apply_symm_apply _)
  have hs : eA ((weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K) ≫
      (canonicalIso d B hB hWB K).hom) = t :=
    (canonicalHomEquiv_source d hA hWA hB hWB a K Y (canonicalIso d B hB hWB K).hom).trans
      ((congrArg (fun z => t ≫ z) hBId).trans (Category.comp_id t))
  have hr := (eA.symm_apply_apply ((weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K) ≫
    (canonicalIso d B hB hWB K).hom)).symm.trans (congrArg eA.symm hs)
  exact hr.trans hAcomp.symm

/-- The canonical comparison is natural on the entire original pointed scalar functor. -/
theorem canonicalIso_weight (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    {K L : PointedSSet.{vC_FrameDerivedComparison}} (k : K ⟶ L) :
    (weakEquivalences C).Q.map ((pointedTensorBifunctor.obj A).map k) ≫ (canonicalIso d A hA hW L).hom =
      (canonicalIso d A hA hW K).hom ≫
        ((tensorAction d).map (pointedProjection.map k)).app ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)) := by
  let Y := (framedTensor d L).obj (A.obj ⦋0⦌)
  let t := ((tensorAction d).map (pointedProjection.map k)).app ((weakEquivalences C).Q.obj (A.obj ⦋0⦌))
  have hKcomp := canonicalIso_hom_comp d A hA hW K Y t
  have hLcomp := canonicalIso_hom_comp d A hA hW L Y (𝟙 _)
  have hLcomp' := (Category.comp_id ((canonicalIso d A hA hW L).hom)).symm.trans hLcomp
  let eK := canonicalHomEquiv d A hA hW K Y
  let eL := canonicalHomEquiv d A hA hW L Y
  have hLId : eL (canonicalIso d A hA hW L).hom = 𝟙 _ :=
    (congrArg eL hLcomp').trans (eL.apply_symm_apply _)
  have hs : eK ((weakEquivalences C).Q.map ((pointedTensorBifunctor.obj A).map k) ≫
      (canonicalIso d A hA hW L).hom) = t :=
    (canonicalHomEquiv_weight d A hA hW k Y (canonicalIso d A hA hW L).hom).trans
      ((congrArg (fun z => t ≫ z) hLId).trans (Category.comp_id t))
  have hr := (eK.symm_apply_apply ((weakEquivalences C).Q.map ((pointedTensorBifunctor.obj A).map k) ≫
    (canonicalIso d A hA hW L).hom)).symm.trans (congrArg eK.symm hs)
  exact hr.trans hKcomp.symm

omit [HasLimitsOfSize.{0, vC_FrameDerivedComparison} C] in
/-- The genuine arbitrary-frame Quillen tensor preserves every original scalar weak equivalence. -/
theorem scalarTensor_inverts (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f)) :
    (weakEquivalences PointedSSet.{vC_FrameDerivedComparison}).IsInvertedBy (pointedTensorBifunctor.obj A ⋙
      (weakEquivalences C).Q) := by
  intro K L k hk
  let _ : (pointedTensorHomAdjunction A).IsQuillenAdjunction := pointedTensorHomAdjunction_isQuillen A hA hW
  let _ : IsCofibrant K := pointedSSet_isCofibrant K
  let _ : IsCofibrant L := pointedSSet_isCofibrant L
  let _ : WeakEquivalence k := (weakEquivalence_iff _).mpr hk
  exact Localization.inverts (weakEquivalences C).Q (weakEquivalences C) _
    ((weakEquivalence_iff _).mp
      (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := pointedTensorHomAdjunction A) k))

/-- Every arbitrary cofibrant frame has its original tensor on all scalar Ho objects and arrows. -/
def scalarTensorHo (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f)) :
    PointedSpaceHo.{vC_FrameDerivedComparison} ⥤ (weakEquivalences C).Localization :=
  Localization.Construction.lift (pointedTensorBifunctor.obj A ⋙ (weakEquivalences C).Q)
    (scalarTensor_inverts A hA hW)

omit [HasLimitsOfSize.{0, vC_FrameDerivedComparison} C] in
theorem scalarTensorHo_projection (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f)) :
    pointedProjection ⋙ scalarTensorHo A hA hW = pointedTensorBifunctor.obj A ⋙ (weakEquivalences C).Q :=
  Localization.Construction.fac _ _

omit [HasLimitsOfSize.{0, vC_FrameDerivedComparison} C] in
/-- The exact original arbitrary-frame scalar tensor has its canonical localization lifting. -/
instance scalarTensorHoLifting (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f)) :
    Localization.Lifting pointedProjection (weakEquivalences PointedSSet.{vC_FrameDerivedComparison})
      (pointedTensorBifunctor.obj A ⋙ (weakEquivalences C).Q) (scalarTensorHo A hA hW) :=
  ⟨eqToIso (scalarTensorHo_projection A hA hW)⟩

omit [HasLimitsOfSize.{0, vC_FrameDerivedComparison} C] in
theorem scalarTensorHo_map (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    {K L : PointedSSet.{vC_FrameDerivedComparison}} (k : K ⟶ L) :
    (scalarTensorHo A hA hW).map (pointedProjection.map k) =
      (weakEquivalences C).Q.map ((pointedTensorBifunctor.obj A).map k) :=
  Functor.congr_hom (scalarTensorHo_projection A hA hW) k

/-- The entire canonical arbitrary-frame comparison is natural on all scalar Ho arrows, including formal inverses. -/
def scalarTensorHoIso (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f)) :
    scalarTensorHo A hA hW ≅ (tensorAction d).flip.obj ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)) :=
  Localization.liftNatIso pointedProjection (weakEquivalences PointedSSet.{vC_FrameDerivedComparison})
    (pointedTensorBifunctor.obj A ⋙ (weakEquivalences C).Q)
    (pointedProjection ⋙ (tensorAction d).flip.obj ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)))
    (scalarTensorHo A hA hW) ((tensorAction d).flip.obj ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)))
    (NatIso.ofComponents (canonicalIso d A hA hW)
      (fun {_ _} k => canonicalIso_weight d A hA hW k))

/-- The natural scalar Ho comparison retains exactly the original HFC-defined component. -/
theorem scalarTensorHoIso_hom_original (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f)) (K :
      PointedSSet.{vC_FrameDerivedComparison}) :
    (scalarTensorHoIso d A hA hW).hom.app (pointedProjection.obj K) = (canonicalIso d A hA hW K).hom := by
  unfold scalarTensorHoIso
  rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change (eqToHom (scalarTensorHo_projection A hA hW)).app K ≫
    (canonicalIso d A hA hW K).hom ≫ 𝟙 _ = (canonicalIso d A hA hW K).hom
  rw [eqToHom_app]
  have he := eqToHom_refl ((weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj A).obj K))
    (congrArg (fun F => F.obj K) (scalarTensorHo_projection A hA hW))
  exact (congrArg (fun z => z ≫ (canonicalIso d A hA hW K).hom ≫ 𝟙 _) he).trans
    ((Category.id_comp ((canonicalIso d A hA hW K).hom ≫ 𝟙 _)).trans
      (Category.comp_id (canonicalIso d A hA hW K).hom))

/-- An actual entire frame map acts naturally on every scalar Ho object and arrow. -/
def scalarTensorHoFrameMap {A B : CosimplicialObject C}
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hWA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hB : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy B n))
    (hWB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (a : A ⟶ B) : scalarTensorHo A hA hWA ⟶ scalarTensorHo B hB hWB :=
  (scalarTensorHoIso d A hA hWA).hom ≫
    (tensorAction d).flip.map ((weakEquivalences C).Q.map (a.app ⦋0⦌)) ≫
      (scalarTensorHoIso d B hB hWB).inv

/-- The full scalar Ho frame map is exactly the original localized point-set tensor map. -/
theorem scalarTensorHoFrameMap_original {A B : CosimplicialObject C}
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hWA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hB : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy B n))
    (hWB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (a : A ⟶ B) (K : PointedSSet.{vC_FrameDerivedComparison}) :
    (scalarTensorHoFrameMap d hA hWA hB hWB a).app (pointedProjection.obj K) =
      (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K) := by
  let sa := (scalarTensorHoIso d A hA hWA).app (pointedProjection.obj K)
  let sb := (scalarTensorHoIso d B hB hWB).app (pointedProjection.obj K)
  let t := ((tensorAction d).obj (pointedProjection.obj K)).map ((weakEquivalences C).Q.map (a.app ⦋0⦌))
  have ea : sa = canonicalIso d A hA hWA K := Iso.ext (scalarTensorHoIso_hom_original d A hA hWA K)
  have eb : sb = canonicalIso d B hB hWB K := Iso.ext (scalarTensorHoIso_hom_original d B hB hWB K)
  have hh := canonicalIso_source d hA hWA hB hWB a K
  have hb : (canonicalIso d A hA hWA K).hom ≫ t ≫ (canonicalIso d B hB hWB K).inv =
      (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K) := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (canonicalIso d B hB hWB K).inv) hh.symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K) ≫ z)
            (canonicalIso d B hB hWB K).hom_inv_id).trans (Category.comp_id _))))
  change sa.hom ≫ t ≫ sb.inv = _
  exact (congrArg (fun e => e.hom ≫ t ≫ sb.inv) ea).trans
    ((congrArg (fun e => (canonicalIso d A hA hWA K).hom ≫ t ≫ e.inv) eb).trans hb)

/-- The full scalar comparison keeps the same complete natural frame transformation. -/
theorem scalarTensorHoIso_source {A B : CosimplicialObject C}
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hWA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hB : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy B n))
    (hWB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (a : A ⟶ B) :
    scalarTensorHoFrameMap d hA hWA hB hWB a ≫ (scalarTensorHoIso d B hB hWB).hom =
      (scalarTensorHoIso d A hA hWA).hom ≫
        (tensorAction d).flip.map ((weakEquivalences C).Q.map (a.app ⦋0⦌)) := by
  unfold scalarTensorHoFrameMap
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Closed

end Tensor

end HomotopicalAlgebra.PointedFramingAction.FrameDerivedComparison

end PointedActionPromotionFrameDerivedComparison


section PointedActionPromotionFrameMapExistence

set_option autoImplicit false

universe uC_FrameMapExistence vC_FrameMapExistence
open CategoryTheory Limits MorphismProperty Simplicial

namespace HomotopicalAlgebra.PointedFramingAction.FrameCoherence

variable {C : Type uC_FrameMapExistence} [Category.{vC_FrameMapExistence} C] [ModelCategory C]

/-- The original evaluation counit includes every actual degree-zero vertex in the frame. -/
def fromFree (A : CosimplicialObject C) :
    FramingEndpoints.leftFree.obj (A.obj ⦋0⦌) ⟶ A :=
  (evaluationAdjunctionRight C ⦋0⦌).counit.app A

/-- Each original vertex summand retains the actual corresponding frame structure map. -/
@[reassoc]
theorem fromFree_ι (A : CosimplicialObject C) (n : SimplexCategory) (g : ⦋0⦌ ⟶ n) :
    Sigma.ι (fun _ : ⦋0⦌ ⟶ n => A.obj ⦋0⦌) g ≫ (fromFree A).app n = A.map g := by
  simp [fromFree, evaluationAdjunctionRight]

/-- The original free-vertex counit in degree zero is the original endpoint fold isomorphism. -/
theorem fromFree_zero (A : CosimplicialObject C) :
    (fromFree A).app ⦋0⦌ = (FramingEndpoints.leftDegreeZeroIso (C := C)).hom.app (A.obj ⦋0⦌) := by
  apply Sigma.hom_ext
  intro g
  have hg : g = 𝟙 ⦋0⦌ := SimplexCategory.hom_zero_zero g
  subst g
  rw [fromFree_ι, FramingEndpoints.leftDegreeZeroIso_hom, FramingEndpoints.cosimplicialFold_ι,
    A.map_id]

/-- The actual original free-vertex counit is an isomorphism in the least degree. -/
instance fromFree_zero_isIso (A : CosimplicialObject C) : IsIso ((fromFree A).app ⦋0⦌) := by
  rw [fromFree_zero]
  infer_instance

/-- The entire original free-vertex counit retains the canonical augmentation fold. -/
theorem fromFree_augmentation (A : CosimplicialObject C) :
    fromFree A ≫ augmentation A = (FramingEndpoints.cosimplicialFold (C := C)).app (A.obj ⦋0⦌) := by
  ext n
  apply Sigma.hom_ext
  intro g
  rw [NatTrans.comp_app]
  have hg : g ≫ SimplexCategory.isTerminalZero.from n = 𝟙 ⦋0⦌ :=
    SimplexCategory.isTerminalZero.hom_ext _ _
  calc
    _ = (Sigma.ι (fun _ : ⦋0⦌ ⟶ n => A.obj ⦋0⦌) g ≫ (fromFree A).app n) ≫
        (augmentation A).app n := (Category.assoc _ _ _).symm
    _ = A.map g ≫ A.map (SimplexCategory.isTerminalZero.from n) :=
      congrArg (fun z => z ≫ (augmentation A).app n) (fromFree_ι A n g)
    _ = A.map (g ≫ SimplexCategory.isTerminalZero.from n) := (A.map_comp _ _).symm
    _ = 𝟙 _ := by rw [hg, A.map_id]
    _ = _ := (FramingEndpoints.cosimplicialFold_ι _ n g).symm

/-- Every latching corner of the same original free-vertex counit is a cofibration
when the actual frame has cofibrant latching maps. -/
theorem fromFree_latching_cofibration (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (n : SimplexCategory) :
    cofibrations C (ReedyStructure.latchingCorner SimplexCategory.reedy (fromFree A) n) := by
  by_cases hn : n.len = 0
  · have he : n = ⦋0⦌ := SimplexCategory.ext hn
    subst n
    let F := FramingEndpoints.leftFree.obj (A.obj ⦋0⦌)
    let c := colimMap (SimplexCategory.reedy.latchingTransformation (fromFree A) ⦋0⦌)
    let _ : IsIso c := isIso_of_isInitial
      (isColimitEquivIsInitialOfIsEmpty C (colimit.cocone _) (colimit.isColimit _))
      (isColimitEquivIsInitialOfIsEmpty C (colimit.cocone _) (colimit.isColimit _)) c
    let i := pushout.inl (ReedyStructure.latchingMap SimplexCategory.reedy F ⦋0⦌) c
    let _ : IsIso i := by dsimp [i]; infer_instance
    apply ((cofibrations C).cancel_left_of_respectsIso i _).mp
    rw [ReedyStructure.latchingCorner_inl]
    exact (cofibrations C).of_isIso _
  · let F := FramingEndpoints.leftFree.obj (A.obj ⦋0⦌)
    let _ : IsIso (ReedyStructure.latchingMap SimplexCategory.reedy F n) :=
      FramingEndpoints.leftFreeLatchingMap_isIso (A.obj ⦋0⦌) n (Nat.pos_of_ne_zero hn)
    let i := pushout.inr (ReedyStructure.latchingMap SimplexCategory.reedy F n)
      (colimMap (SimplexCategory.reedy.latchingTransformation (fromFree A) n))
    let _ : IsIso i := by dsimp [i]; infer_instance
    apply ((cofibrations C).cancel_left_of_respectsIso i _).mp
    rw [ReedyStructure.latchingCorner_inr]
    exact hA n

variable (d : GeneratedFunctorialReplacements.Data (C := C))

/-- The same original chosen resolution has every actual trivial-fibration matching corner. -/
theorem originalResolution_matching_trivialFibration (Z : C) (n : SimplexCategory) :
    trivialFibrations C (ReedyStructure.matchingCorner SimplexCategory.reedy ((leftResolution d).app Z) n) := by
  exact (ReedyStructure.EvaluationCorners.matching_mem_iff
    SimplexCategory.reedy (leftFactor d).p Z n (trivialFibrations C)).mp ((leftFactor d).hp n Z)

/-- The same original factories provide a frame map covering every actual coefficient arrow,
without an assumption that arbitrary lifts are functorial. -/
theorem exists_map_to_chosen (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (Z : C) (f : A.obj ⦋0⦌ ⟶ Z) :
    ∃ a : A ⟶ (leftFrame d).obj Z,
      a ≫ (PointedFramingAction.augmentation d).app Z = augmentation A ≫ (CosimplicialObject.const C).map f := by
  let _ : IsCofibrant (A.obj ⦋0⦌) := LeftFrameHomWeakEquivalence.coefficient_isCofibrant A hA ⦋0⦌
  let sq : CommSq (initial.to (d.Q.obj Z)) (initial.to (A.obj ⦋0⦌)) (d.q.app Z) f :=
    ⟨initial.hom_ext _ _⟩
  let _ : HasLiftingProperty (initial.to (A.obj ⦋0⦌)) (d.q.app Z) :=
    hasLiftingProperty_of_wfs (initial.to (A.obj ⦋0⦌)) (d.q.app Z)
      ((cofibration_iff _).mp ((isCofibrant_iff_of_isInitial _ initialIsInitial).mp inferInstance))
      (d.q_trivialFibration Z)
  let s := sq.lift
  have hs : s ≫ d.q.app Z = f := sq.fac_right
  let t : FramingEndpoints.leftFree.obj (A.obj ⦋0⦌) ⟶ (leftFrame d).obj Z :=
    FramingEndpoints.leftFree.map s ≫ (fromLeftFree d).app Z
  let b : A ⟶ (CosimplicialObject.const C).obj (d.Q.obj Z) :=
    augmentation A ≫ (CosimplicialObject.const C).map s
  have hsq : CommSq t (fromFree A) ((leftResolution d).app Z) b := by
    constructor
    dsimp [t, b]
    have hp : (fromLeftFree d).app Z ≫ (leftResolution d).app Z =
        (FramingEndpoints.cosimplicialFold (C := C)).app (d.Q.obj Z) :=
      congrArg (fun τ => τ.app Z) (left_fac d)
    calc
      _ = FramingEndpoints.leftFree.map s ≫
          ((fromLeftFree d).app Z ≫ (leftResolution d).app Z) := Category.assoc _ _ _
      _ = FramingEndpoints.leftFree.map s ≫
          (FramingEndpoints.cosimplicialFold (C := C)).app (d.Q.obj Z) := by rw [hp]
      _ = (FramingEndpoints.cosimplicialFold (C := C)).app (A.obj ⦋0⦌) ≫
          (CosimplicialObject.const C).map s :=
        (FramingEndpoints.cosimplicialFold (C := C)).naturality s
      _ = (fromFree A ≫ augmentation A) ≫ (CosimplicialObject.const C).map s := by
        rw [fromFree_augmentation]
      _ = _ := Category.assoc _ _ _
  let l := ReedyLifting.liftStruct SimplexCategory.reedy (fromFree A) ((leftResolution d).app Z) hsq
    (fromFree_latching_cofibration A hA) (originalResolution_matching_trivialFibration d Z)
  refine ⟨l.l, ?_⟩
  have hl : l.l ≫ (leftResolution d).app Z = b := l.fac_right
  calc
    _ = l.l ≫ ((leftResolution d).app Z ≫ (CosimplicialObject.const C).map (d.q.app Z)) := by
      apply congrArg (fun z => l.l ≫ z)
      ext n
      exact PointedFramingAction.augmentation_app d Z n
    _ = (l.l ≫ (leftResolution d).app Z) ≫ (CosimplicialObject.const C).map (d.q.app Z) :=
      (Category.assoc _ _ _).symm
    _ = b ≫ (CosimplicialObject.const C).map (d.q.app Z) := by rw [hl]
    _ = augmentation A ≫ (CosimplicialObject.const C).map f := by
      dsimp [b]
      rw [Category.assoc, ← Functor.map_comp, hs]

end HomotopicalAlgebra.PointedFramingAction.FrameCoherence

end PointedActionPromotionFrameMapExistence


section PointedActionPromotionFrameNormalization

set_option autoImplicit false

universe uC_FrameNormalization vC_FrameNormalization
open CategoryTheory Limits MorphismProperty Simplicial
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.PointedFramingAction.FrameDerivedComparison

variable {C : Type uC_FrameNormalization} [Category.{vC_FrameNormalization} C] [ModelCategory C] [HasZeroObject C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

omit [HasZeroObject C] in
/-- The original chosen resolution is the canonical augmentation followed by
its unchanged original degree-zero isomorphism. -/
theorem chosenResolution_augmentation (X : C) :
    (leftResolution d).app X = FrameCoherence.augmentation ((leftFrame d).obj X) ≫
      (CosimplicialObject.const C).map ((leftZeroIso d).hom.app X) := by
  ext n
  have h := ((leftResolution d).app X).naturality (SimplexCategory.isTerminalZero.from n)
  change ((leftFrame d).obj X).map (SimplexCategory.isTerminalZero.from n) ≫
      ((leftResolution d).app X).app ⦋0⦌ = ((leftResolution d).app X).app n ≫ 𝟙 _ at h
  rw [Category.comp_id] at h
  exact h.symm.trans (congrArg
    (fun z => ((leftFrame d).obj X).map (SimplexCategory.isTerminalZero.from n) ≫ z)
    (leftZeroIso_hom d X).symm)

omit [HasZeroObject C] in
/-- Naturality of the actual Q counit identifies the two original cofibrant-source
coefficient maps needed to normalize the chosen-frame HFC word. -/
theorem chosenZero_Q_map (X : C) :
    (weakEquivalences C).Q.map (d.Q.map (((augmentation d).app X).app ⦋0⦌)) =
      (weakEquivalences C).Q.map
        (d.q.app (((leftFrame d).obj X).obj ⦋0⦌) ≫ (leftZeroIso d).hom.app X) := by
  let α := ((augmentation d).app X).app ⦋0⦌
  let _ : IsIso ((weakEquivalences C).Q.map (d.q.app X)) :=
    Localization.inverts (weakEquivalences C).Q (weakEquivalences C) _ (d.q_trivialFibration X).2
  have hα : α = (leftZeroIso d).hom.app X ≫ d.q.app X := augmentation_zero d X
  have hn := congrArg (weakEquivalences C).Q.map (d.q.naturality α)
  simp only [Functor.map_comp] at hn
  apply (cancel_mono ((weakEquivalences C).Q.map (d.q.app X))).mp
  calc
    _ = (weakEquivalences C).Q.map (d.q.app (((leftFrame d).obj X).obj ⦋0⦌)) ≫
        (weakEquivalences C).Q.map α := hn
    _ = _ := by rw [hα, Functor.map_comp, Functor.map_comp, Category.assoc]

/-- For a chosen frame, the canonical three-leg HFC comparison retains the original
left/right HFC comparison and the same original zero-degree augmentation arrow. -/
theorem hfcIso_chosen (X Y : C) :
    (hfcIso d ((leftFrame d).obj X) (leftFrame_latching_cofibration d X)
      (leftFrame_map_weak d X) Y).hom =
    (pointedLeftRightIso d X Y).hom ≫
      pointedProjection.map (pointedRightSourceMap d (((augmentation d).app X).app ⦋0⦌) Y) := by
  let A := (leftFrame d).obj X
  let θ := (leftZeroIso d).hom.app X
  let α := ((augmentation d).app X).app ⦋0⦌
  let t := pointedHomPrecomp ((CosimplicialObject.const C).map θ) ((rightFrame d).obj Y)
  have ht : t ≫ fromZero d A Y = pointedRightToTwoSided d X Y := by
    change pointedHomPrecomp ((CosimplicialObject.const C).map θ) ((rightFrame d).obj Y) ≫
        pointedHomPrecomp (FrameCoherence.augmentation A) ((rightFrame d).obj Y) =
      pointedHomPrecomp ((leftResolution d).app X) ((rightFrame d).obj Y)
    rw [← pointedHomPrecomp_comp, ← chosenResolution_augmentation]
  have hR := congrArg pointedProjection.map ht
  simp only [Functor.map_comp] at hR
  let _ : IsCofibrant (d.Q.obj (A.obj ⦋0⦌)) := d.q_cofibrant _
  have hq := rightPrecomp_eq_of_ho d (d.Q.map α) (d.q.app (A.obj ⦋0⦌) ≫ θ)
    (chosenZero_Q_map d X) Y
  have hQ : pointedProjection.map (pointedRightSourceMap d α Y) =
      pointedProjection.map t ≫ pointedProjection.map (zeroToChosen d A Y) := by
    calc
      _ = pointedProjection.map
          (pointedHomPrecomp ((CosimplicialObject.const C).map (d.q.app (A.obj ⦋0⦌) ≫ θ))
            ((rightFrame d).obj Y)) := hq
      _ = pointedProjection.map (t ≫ zeroToChosen d A Y) := by
        apply congrArg pointedProjection.map
        dsimp [t, zeroToChosen]
        rw [Functor.map_comp, pointedHomPrecomp_comp]
      _ = _ := pointedProjection.map_comp _ _
  let _ : IsIso (pointedProjection.map (fromZero d A Y)) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC_FrameNormalization}) _
      (fromZero_weak d A (leftFrame_latching_cofibration d X) (leftFrame_map_weak d X) Y)
  let _ : IsIso (pointedProjection.map (pointedRightToTwoSided d X Y)) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC_FrameNormalization}) _
      (pointedRightToTwoSided_weak d X Y)
  have hi : inv (pointedProjection.map (pointedRightToTwoSided d X Y)) ≫ pointedProjection.map t =
      inv (pointedProjection.map (fromZero d A Y)) := by
    apply (cancel_mono (pointedProjection.map (fromZero d A Y))).mp
    rw [Category.assoc, hR, IsIso.inv_hom_id, IsIso.inv_hom_id]
  change pointedProjection.map (toTwoSided d A Y) ≫
      inv (pointedProjection.map (fromZero d A Y)) ≫ pointedProjection.map (zeroToChosen d A Y) =
    (pointedProjection.map (toTwoSided d A Y) ≫
      inv (pointedProjection.map (pointedRightToTwoSided d X Y))) ≫
        pointedProjection.map (pointedRightSourceMap d α Y)
  calc
    _ = pointedProjection.map (toTwoSided d A Y) ≫
        (inv (pointedProjection.map (pointedRightToTwoSided d X Y)) ≫ pointedProjection.map t) ≫
          pointedProjection.map (zeroToChosen d A Y) := by rw [hi]
    _ = (pointedProjection.map (toTwoSided d A Y) ≫
        inv (pointedProjection.map (pointedRightToTwoSided d X Y))) ≫
          (pointedProjection.map t ≫ pointedProjection.map (zeroToChosen d A Y)) := by
      simp only [Category.assoc]
    _ = _ := by rw [← hQ]

section Tensor
variable [HasColimitsOfSize.{0, vC_FrameNormalization} C] [HasLimitsOfSize.{0, vC_FrameNormalization} C]

/-- The chosen-frame Hom comparison is the original closed Hom function followed by
the original zero-degree augmentation source map. -/
theorem frameHomEquiv_chosen (X : C) (K : PointedSSet.{vC_FrameNormalization}) (Y : C)
    (h : (weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj ((leftFrame d).obj X)).obj K) ⟶
      (weakEquivalences C).Q.obj Y) :
    frameHomEquiv d ((leftFrame d).obj X) (leftFrame_latching_cofibration d X)
        (leftFrame_map_weak d X) K Y h =
      closedHomEquiv d ((weakEquivalences C).Q.obj X) (pointedProjection.obj K)
          ((weakEquivalences C).Q.obj Y) h ≫
        ((mappingHo d).map ((weakEquivalences C).Q.map (((augmentation d).app X).app ⦋0⦌)).op).app
          ((weakEquivalences C).Q.obj Y) := by
  have ht : FrameCoherence.tensorHomEquivHo d ((leftFrame d).obj X)
      (leftFrame_latching_cofibration d X) (leftFrame_map_weak d X) K Y h =
      pointedTensorHoHomEquiv d X K Y (h ≫ (rHomotopyIso d Y).hom) :=
    FrameCoherence.tensorHomEquivHo_apply d _ _ _ K Y h
  have hf := frameHomEquiv_apply d ((leftFrame d).obj X) (leftFrame_latching_cofibration d X)
    (leftFrame_map_weak d X) K Y h
  have hh := hfcIso_chosen d X Y
  have hc := closedHomOriginal_apply d X K Y h
  let α : ((leftFrame d).obj X).obj ⦋0⦌ ⟶ X := ((augmentation d).app X).app ⦋0⦌
  have hs := mappingHoOriginalIso_source_inv d α Y
  calc
    _ = _ := hf
    _ = pointedTensorHoHomEquiv d X K Y (h ≫ (rHomotopyIso d Y).hom) ≫
        (pointedLeftRightIso d X Y).hom ≫
          pointedProjection.map (pointedRightSourceMap d (((augmentation d).app X).app ⦋0⦌) Y) ≫
            (mappingHoOriginalIso d (((leftFrame d).obj X).obj ⦋0⦌) Y).inv := by
      rw [ht, hh]
      simp only [Category.assoc]
    _ = (pointedTensorHoHomEquiv d X K Y (h ≫ (rHomotopyIso d Y).hom) ≫
        (pointedLeftRightIso d X Y).hom ≫ (mappingHoOriginalIso d X Y).inv) ≫
          ((mappingHo d).map ((weakEquivalences C).Q.map (((augmentation d).app X).app ⦋0⦌)).op).app
            ((weakEquivalences C).Q.obj Y) := by
      simpa only [Category.assoc] using congrArg
        (fun z => pointedTensorHoHomEquiv d X K Y (h ≫ (rHomotopyIso d Y).hom) ≫
          (pointedLeftRightIso d X Y).hom ≫ z) hs
    _ = _ := congrArg (fun z => z ≫
      ((mappingHo d).map ((weakEquivalences C).Q.map (((augmentation d).app X).app ⦋0⦌)).op).app
        ((weakEquivalences C).Q.obj Y)) hc.symm

/-- The actual canonical tensor comparison for a chosen frame is normalized by
the same original frame-zero and Q augmentation word. -/
theorem canonicalIso_chosen (X : C) (K : PointedSSet.{vC_FrameNormalization}) :
    (canonicalIso d ((leftFrame d).obj X) (leftFrame_latching_cofibration d X)
        (leftFrame_map_weak d X) K).hom ≫
      ((tensorAction d).obj (pointedProjection.obj K)).map
        ((weakEquivalences C).Q.map (((augmentation d).app X).app ⦋0⦌)) =
      𝟙 ((weakEquivalences C).Q.obj ((pointedTensorBifunctor.obj ((leftFrame d).obj X)).obj K)) := by
  let A := (leftFrame d).obj X
  let Y := (pointedTensorBifunctor.obj A).obj K
  let α : A.obj ⦋0⦌ ⟶ X := ((augmentation d).app X).app ⦋0⦌
  let t := ((tensorAction d).obj (pointedProjection.obj K)).map ((weakEquivalences C).Q.map α)
  let e := canonicalHomEquiv d A (leftFrame_latching_cofibration d X) (leftFrame_map_weak d X) K Y
  have hf := frameHomEquiv_chosen d X K Y (𝟙 _)
  have hc := closedHomEquiv_source d ((weakEquivalences C).Q.map α)
    (pointedProjection.obj K) ((weakEquivalences C).Q.obj Y) (𝟙 _)
  have hc' := (congrArg (closedHomEquiv d ((weakEquivalences C).Q.obj (A.obj ⦋0⦌))
    (pointedProjection.obj K) ((weakEquivalences C).Q.obj Y)) (Category.comp_id t)).symm.trans hc
  have he : e (𝟙 _) = t := by
    apply (closedHomEquiv d ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)) (pointedProjection.obj K)
      ((weakEquivalences C).Q.obj Y)).injective
    exact (Equiv.apply_symm_apply _ (frameHomEquiv d A (leftFrame_latching_cofibration d X)
      (leftFrame_map_weak d X) K Y (𝟙 _))).trans (hf.trans hc'.symm)
  have hp := canonicalIso_hom_comp d A (leftFrame_latching_cofibration d X) (leftFrame_map_weak d X) K Y t
  exact hp.trans ((congrArg e.symm he.symm).trans (e.symm_apply_apply (𝟙 _)))

/-- Every actual map to a chosen frame that covers the given coefficient arrow
is its full canonical tensor comparison followed by the original derived coefficient map. -/
theorem canonicalIso_represents_map (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (g : n ⟶ m), weakEquivalences C (A.map g))
    (X : C) (f : A.obj ⦋0⦌ ⟶ X) (a : A ⟶ (leftFrame d).obj X)
    (ha : a ≫ (augmentation d).app X = FrameCoherence.augmentation A ≫ (CosimplicialObject.const C).map f)
    (K : PointedSSet.{vC_FrameNormalization}) :
    (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K) =
      (canonicalIso d A hA hW K).hom ≫
        ((tensorAction d).obj (pointedProjection.obj K)).map ((weakEquivalences C).Q.map f) := by
  have hz := congrArg (fun τ => τ.app ⦋0⦌) ha
  have hi : SimplexCategory.isTerminalZero.from ⦋0⦌ = 𝟙 ⦋0⦌ := SimplexCategory.hom_zero_zero _
  have hAug : (FrameCoherence.augmentation A).app ⦋0⦌ = 𝟙 (A.obj ⦋0⦌) :=
    (congrArg A.map hi).trans (A.map_id _)
  have hzero : a.app ⦋0⦌ ≫ ((augmentation d).app X).app ⦋0⦌ = f :=
    hz.trans ((congrArg (fun z => z ≫ f) hAug).trans (Category.id_comp f))
  have hs := canonicalIso_source d hA hW (leftFrame_latching_cofibration d X) (leftFrame_map_weak d X) a K
  let T := (tensorAction d).obj (pointedProjection.obj K)
  let t := (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K)
  let u := (canonicalIso d ((leftFrame d).obj X) (leftFrame_latching_cofibration d X) (leftFrame_map_weak d X) K).hom
  let α : ((leftFrame d).obj X).obj ⦋0⦌ ⟶ X := ((augmentation d).app X).app ⦋0⦌
  let p := T.map ((weakEquivalences C).Q.map α)
  have hn : u ≫ p = 𝟙 _ := canonicalIso_chosen d X K
  have hc := congrArg (fun z => z ≫ p) hs
  have hm : T.map ((weakEquivalences C).Q.map (a.app ⦋0⦌)) ≫ p =
      T.map ((weakEquivalences C).Q.map f) :=
    (T.map_comp _ _).symm.trans
      ((congrArg T.map ((weakEquivalences C).Q.map_comp _ _).symm).trans
        (congrArg (fun z => T.map ((weakEquivalences C).Q.map z)) hzero))
  exact (Category.comp_id t).symm.trans
    ((congrArg (fun z => t ≫ z) hn.symm).trans
      ((Category.assoc t u p).symm.trans
        (hc.trans ((Category.assoc _ _ p).trans
          (congrArg (fun z => (canonicalIso d A hA hW K).hom ≫ z) hm)))))

/-- One actual comparison map of frames represents the canonical tensor comparison
simultaneously at every original pointed weight. -/
theorem exists_canonical_frame_map (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (g : n ⟶ m), weakEquivalences C (A.map g)) :
    ∃ a : A ⟶ (leftFrame d).obj (A.obj ⦋0⦌),
      a ≫ (augmentation d).app (A.obj ⦋0⦌) = FrameCoherence.augmentation A ∧
      ∀ K : PointedSSet.{vC_FrameNormalization},
        (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app K) = (canonicalIso d A hA hW K).hom := by
  obtain ⟨a, ha⟩ := FrameCoherence.exists_map_to_chosen d A hA (A.obj ⦋0⦌) (𝟙 _)
  have ha' : a ≫ (augmentation d).app (A.obj ⦋0⦌) = FrameCoherence.augmentation A :=
    ha.trans ((congrArg (fun z => FrameCoherence.augmentation A ≫ z)
      ((CosimplicialObject.const C).map_id _)).trans (Category.comp_id _))
  refine ⟨a, ha', fun K => ?_⟩
  have ht := canonicalIso_represents_map d A hA hW (A.obj ⦋0⦌) (𝟙 _) a
    ha K
  have hi : ((tensorAction d).obj (pointedProjection.obj K)).map ((weakEquivalences C).Q.map (𝟙 (A.obj ⦋0⦌))) =
      𝟙 _ := (congrArg ((tensorAction d).obj (pointedProjection.obj K)).map ((weakEquivalences C).Q.map_id _)).trans
        (((tensorAction d).obj (pointedProjection.obj K)).map_id _)
  exact ht.trans ((congrArg (fun z => (canonicalIso d A hA hW K).hom ≫ z) hi).trans (Category.comp_id _))

end Tensor

end HomotopicalAlgebra.PointedFramingAction.FrameDerivedComparison

end PointedActionPromotionFrameNormalization


section PointedActionPromotionActionAssociator

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe uC_ActionAssociator vC_ActionAssociator
open CategoryTheory Limits MorphismProperty Simplicial MonoidalCategory
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.PointedFramingAction.ActionAssociator

/-- Use the original pointed simplicial smash monoidal structure. -/
local instance pointedScalarMonoidal13 : MonoidalCategory PointedSSet.{vC_ActionAssociator} :=
  ScalarStructure.smashMonoidal
/-- Use the canonical localized pointed simplicial smash structure. -/
local instance scalarHomotopyMonoidal14 : MonoidalCategory PointedSpaceHo.{vC_ActionAssociator} :=
  ScalarStructure.monoidalHo
/-- The original weak localization is strong monoidal for smash. -/
local instance pointedScalarProjectionMonoidal15 : pointedProjection.{vC_ActionAssociator}.Monoidal :=
  ScalarStructure.projectionMonoidal

variable {C : Type uC_ActionAssociator} [Category.{vC_ActionAssociator} C] [ModelCategory C] [HasZeroObject C]
  [HasColimitsOfSize.{0, vC_ActionAssociator} C] [HasLimitsOfSize.{0, vC_ActionAssociator} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

/-- Use the native coefficient endofunctor monoidal structure given by composition. -/
local instance coefficientEndofunctorsMonoidal16 : MonoidalCategory ((weakEquivalences C).Localization ⥤
    (weakEquivalences C).Localization) := endofunctorMonoidalCategory (weakEquivalences C).Localization

/-- The actual derived composite is the inverse zero-degree comparison, inverse HFC comparison, and genuine coend Fubini
map. -/
def compositeIso (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K L : PointedSSet.{vC_ActionAssociator}) :
    ((tensorAction d).obj (pointedProjection.obj L)).obj ((weakEquivalences C).Q.obj (pointedTensor A K)) ≅
      (weakEquivalences C).Q.obj (pointedTensor A (K ⊗ L)) :=
  ((tensorAction d).obj (pointedProjection.obj L)).mapIso
      ((weakEquivalences C).Q.mapIso (FrameTensorFubini.frameZeroIso A K)).symm ≪≫
    (FrameDerivedComparison.canonicalIso d (FrameTensorFubini.frame A K)
      (FrameTensorFubini.latching_cofibration A hA hW K)
      (FrameTensorFubini.frame_map_weak A hA hW K) L).symm ≪≫
    (weakEquivalences C).Q.mapIso (FrameTensorFubini.fubiniIso A K L)

/-- The entire forward associator word retains the same original zero, HFC and Fubini maps. -/
theorem compositeIso_hom (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K L : PointedSSet.{vC_ActionAssociator}) :
    (compositeIso d A hA hW K L).hom =
      ((tensorAction d).obj (pointedProjection.obj L)).map
        ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫
      (FrameDerivedComparison.canonicalIso d (FrameTensorFubini.frame A K)
        (FrameTensorFubini.latching_cofibration A hA hW K)
        (FrameTensorFubini.frame_map_weak A hA hW K) L).inv ≫
      (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).hom := rfl

omit [HasLimitsOfSize.{0, vC_ActionAssociator} C] in
/-- The same zero-degree isomorphism retains the inverse naturality square for all frame and weight arrows. -/
theorem frameZeroInv_naturality {A B : CosimplicialObject C} (a : A ⟶ B)
    {K K' : PointedSSet.{vC_ActionAssociator}} (k : K ⟶ K') :
    pointedTensorMap a k ≫ (FrameTensorFubini.frameZeroIso B K').inv =
      (FrameTensorFubini.frameZeroIso A K).inv ≫ (FrameTensorFubini.frameMap a k).app ⦋0⦌ := by
  apply (cancel_mono (FrameTensorFubini.frameZeroIso B K').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [FrameTensorFubini.frameZeroIso_naturality, Iso.inv_hom_id_assoc]

/-- The canonical HFC comparison retains its entire inverse frame naturality square. -/
theorem canonicalInverse_source {A B : CosimplicialObject C}
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hWA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hB : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy B n))
    (hWB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (a : A ⟶ B) (L : PointedSSet.{vC_ActionAssociator}) :
    ((tensorAction d).obj (pointedProjection.obj L)).map ((weakEquivalences C).Q.map (a.app ⦋0⦌)) ≫
        (FrameDerivedComparison.canonicalIso d B hB hWB L).inv =
      (FrameDerivedComparison.canonicalIso d A hA hWA L).inv ≫
        (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app L) := by
  apply (cancel_epi (FrameDerivedComparison.canonicalIso d A hA hWA L).hom).mp
  rw [← Category.assoc, ← FrameDerivedComparison.canonicalIso_source d hA hWA hB hWB a L,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

omit [HasLimitsOfSize.{0, vC_ActionAssociator} C] in
/-- The full original frame bifunctor retains its same original scalar tensor map. -/
theorem tensorFrameMap_eq {A B : CosimplicialObject C} (a : A ⟶ B) (L : PointedSSet.{vC_ActionAssociator}) :
    (pointedTensorBifunctor.map a).app L = pointedTensorMap a (𝟙 L) := rfl

omit [HasLimitsOfSize.{0, vC_ActionAssociator} C] in
theorem tensorWeightMap_eq (A : CosimplicialObject C) {K L : PointedSSet.{vC_ActionAssociator}} (k : K ⟶ L) :
    (pointedTensorBifunctor.obj A).map k = pointedTensorMap (𝟙 A) k := rfl

/-- The inverse canonical comparison retains every original scalar arrow. -/
theorem canonicalInverse_weight (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    {L L' : PointedSSet.{vC_ActionAssociator}} (l : L ⟶ L') :
    ((tensorAction d).map (pointedProjection.map l)).app ((weakEquivalences C).Q.obj (A.obj ⦋0⦌)) ≫
        (FrameDerivedComparison.canonicalIso d A hA hW L').inv =
      (FrameDerivedComparison.canonicalIso d A hA hW L).inv ≫
        (weakEquivalences C).Q.map (pointedTensorMap (𝟙 A) l) := by
  have h := FrameDerivedComparison.canonicalIso_weight d A hA hW l
  rw [← tensorWeightMap_eq A l]
  apply (cancel_epi (FrameDerivedComparison.canonicalIso d A hA hW L).hom).mp
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (Iso.hom_inv_id_assoc (FrameDerivedComparison.canonicalIso d A hA hW L)
    ((weakEquivalences C).Q.map ((pointedTensorBifunctor.obj A).map l))).symm

/-- The genuine associator is natural in the whole original frame and the first weight. -/
theorem compositeIso_source {A B : CosimplicialObject C}
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hWA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hB : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy B n))
    (hWB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (a : A ⟶ B) {K K' : PointedSSet.{vC_ActionAssociator}} (k : K ⟶ K') (L : PointedSSet.{vC_ActionAssociator}) :
    ((tensorAction d).obj (pointedProjection.obj L)).map
        ((weakEquivalences C).Q.map (pointedTensorMap a k)) ≫ (compositeIso d B hB hWB K' L).hom =
      (compositeIso d A hA hWA K L).hom ≫
        (weakEquivalences C).Q.map (pointedTensorMap a (k ⊗ₘ 𝟙 L)) := by
  let eA := FrameDerivedComparison.canonicalIso d (FrameTensorFubini.frame A K)
    (FrameTensorFubini.latching_cofibration A hA hWA K)
    (FrameTensorFubini.frame_map_weak A hA hWA K) L
  let eB := FrameDerivedComparison.canonicalIso d (FrameTensorFubini.frame B K')
    (FrameTensorFubini.latching_cofibration B hB hWB K')
    (FrameTensorFubini.frame_map_weak B hB hWB K') L
  have hz := congrArg
    (fun z : pointedTensor A K ⟶ (FrameTensorFubini.frame B K').obj ⦋0⦌ =>
      ((tensorAction d).obj (pointedProjection.obj L)).map ((weakEquivalences C).Q.map z))
    (frameZeroInv_naturality a k)
  simp only [Functor.map_comp] at hz
  have he := canonicalInverse_source d
    (FrameTensorFubini.latching_cofibration A hA hWA K)
    (FrameTensorFubini.frame_map_weak A hA hWA K)
    (FrameTensorFubini.latching_cofibration B hB hWB K')
    (FrameTensorFubini.frame_map_weak B hB hWB K') (FrameTensorFubini.frameMap a k) L
  rw [tensorFrameMap_eq] at he
  have hf := congrArg (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso_naturality a k (𝟙 L))
  simp only [Functor.map_comp] at hf
  rw [compositeIso_hom, compositeIso_hom]
  change ((tensorAction d).obj (pointedProjection.obj L)).map
      ((weakEquivalences C).Q.map (pointedTensorMap a k)) ≫
    (((tensorAction d).obj (pointedProjection.obj L)).map
      ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso B K').inv) ≫
        eB.inv ≫ (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso B K' L).hom) =
    (((tensorAction d).obj (pointedProjection.obj L)).map
      ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫
        eA.inv ≫ (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).hom) ≫
      (weakEquivalences C).Q.map (pointedTensorMap a (k ⊗ₘ 𝟙 L))
  calc
    _ = ((tensorAction d).obj (pointedProjection.obj L)).map
        ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫
      ((tensorAction d).obj (pointedProjection.obj L)).map
        ((weakEquivalences C).Q.map ((FrameTensorFubini.frameMap a k).app ⦋0⦌)) ≫
      eB.inv ≫ (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso B K' L).hom := by
        simpa only [eA, eB, Category.assoc] using congrArg
          (fun z => z ≫ eB.inv ≫ (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso B K' L).hom) hz
    _ = ((tensorAction d).obj (pointedProjection.obj L)).map
        ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫
      eA.inv ≫ (weakEquivalences C).Q.map (pointedTensorMap (FrameTensorFubini.frameMap a k) (𝟙 L)) ≫
      (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso B K' L).hom := by
        have h := congrArg
          (fun z => ((tensorAction d).obj (pointedProjection.obj L)).map
            ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫ z ≫
              (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso B K' L).hom) he
        change ((tensorAction d).obj (pointedProjection.obj L)).map
            ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫
          (((tensorAction d).obj (pointedProjection.obj L)).map
            ((weakEquivalences C).Q.map ((FrameTensorFubini.frameMap a k).app ⦋0⦌)) ≫ eB.inv) ≫
          (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso B K' L).hom =
          ((tensorAction d).obj (pointedProjection.obj L)).map
            ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫
          (eA.inv ≫ (weakEquivalences C).Q.map (pointedTensorMap (FrameTensorFubini.frameMap a k) (𝟙 L))) ≫
          (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso B K' L).hom at h
        simpa only [Category.assoc] using h
    _ = _ := by
      have h := congrArg
        (fun z => ((tensorAction d).obj (pointedProjection.obj L)).map
          ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫ eA.inv ≫ z) hf
      change ((tensorAction d).obj (pointedProjection.obj L)).map
          ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫ eA.inv ≫
        ((weakEquivalences C).Q.map (pointedTensorMap (FrameTensorFubini.frameMap a k) (𝟙 L)) ≫
          (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso B K' L).hom) =
        ((tensorAction d).obj (pointedProjection.obj L)).map
          ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫ eA.inv ≫
        ((weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).hom ≫
          (weakEquivalences C).Q.map (pointedTensorMap a (k ⊗ₘ 𝟙 L))) at h
      exact h.trans
        ((congrArg
          (fun z => ((tensorAction d).obj (pointedProjection.obj L)).map
            ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫ z)
          (Category.assoc eA.inv ((weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).hom)
            ((weakEquivalences C).Q.map (pointedTensorMap a (k ⊗ₘ 𝟙 L)))).symm).trans
          (Category.assoc
            (((tensorAction d).obj (pointedProjection.obj L)).map
              ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv))
            (eA.inv ≫ (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).hom)
            ((weakEquivalences C).Q.map (pointedTensorMap a (k ⊗ₘ 𝟙 L)))).symm)

/-- The original frame naturality square remains exact after inverting the derived associator. -/
theorem compositeIso_frame_inverse {A B : CosimplicialObject C}
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hWA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hB : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy B n))
    (hWB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (a : A ⟶ B) (K L : PointedSSet.{vC_ActionAssociator}) :
    (weakEquivalences C).Q.map (pointedTensorMap a (𝟙 (K ⊗ L))) ≫ (compositeIso d B hB hWB K L).inv =
      (compositeIso d A hA hWA K L).inv ≫
        ((tensorAction d).obj (pointedProjection.obj L)).map ((weakEquivalences C).Q.map (pointedTensorMap a (𝟙
          K))) := by
  have h := compositeIso_source d hA hWA hB hWB a (𝟙 K) L
  simp only [MonoidalCategory.id_tensorHom_id] at h
  apply (cancel_epi (compositeIso d A hA hWA K L).hom).mp
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- The genuine derived associator retains every original second-weight arrow. -/
theorem compositeIso_weight (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_ActionAssociator}) {L L' : PointedSSet.{vC_ActionAssociator}} (l : L ⟶ L') :
    ((tensorAction d).map (pointedProjection.map l)).app ((weakEquivalences C).Q.obj (pointedTensor A K)) ≫
        (compositeIso d A hA hW K L').hom =
      (compositeIso d A hA hW K L).hom ≫
        (weakEquivalences C).Q.map (pointedTensorMap (𝟙 A) (K ◁ l)) := by
  let eL := FrameDerivedComparison.canonicalIso d (FrameTensorFubini.frame A K)
    (FrameTensorFubini.latching_cofibration A hA hW K)
    (FrameTensorFubini.frame_map_weak A hA hW K) L
  let eL' := FrameDerivedComparison.canonicalIso d (FrameTensorFubini.frame A K)
    (FrameTensorFubini.latching_cofibration A hA hW K)
    (FrameTensorFubini.frame_map_weak A hA hW K) L'
  have hz := ((tensorAction d).map (pointedProjection.map l)).naturality
    ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv)
  have he := canonicalInverse_weight d (FrameTensorFubini.frame A K)
    (FrameTensorFubini.latching_cofibration A hA hW K)
    (FrameTensorFubini.frame_map_weak A hA hW K) l
  have hf := congrArg (weakEquivalences C).Q.map
    (FrameTensorFubini.fubiniIso_naturality (𝟙 A) (𝟙 K) l)
  rw [FrameTensorFubini.frameMap_id, MonoidalCategory.id_tensorHom] at hf
  simp only [Functor.map_comp] at hf
  rw [compositeIso_hom, compositeIso_hom]
  change ((tensorAction d).map (pointedProjection.map l)).app ((weakEquivalences C).Q.obj (pointedTensor A K)) ≫
      (((tensorAction d).obj (pointedProjection.obj L')).map
        ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫ eL'.inv ≫
          (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L').hom) =
    (((tensorAction d).obj (pointedProjection.obj L)).map
      ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫ eL.inv ≫
        (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).hom) ≫
      (weakEquivalences C).Q.map (pointedTensorMap (𝟙 A) (K ◁ l))
  calc
    _ = ((tensorAction d).obj (pointedProjection.obj L)).map
        ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫
      ((tensorAction d).map (pointedProjection.map l)).app
        ((weakEquivalences C).Q.obj ((FrameTensorFubini.frame A K).obj ⦋0⦌)) ≫
      eL'.inv ≫ (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L').hom := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ eL'.inv ≫ (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L').hom) hz.symm
    _ = ((tensorAction d).obj (pointedProjection.obj L)).map
        ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫
      eL.inv ≫ (weakEquivalences C).Q.map (pointedTensorMap (𝟙 (FrameTensorFubini.frame A K)) l) ≫
      (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L').hom := by
      have h := congrArg (fun z => ((tensorAction d).obj (pointedProjection.obj L)).map
        ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫ z ≫
          (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L').hom) he
      change ((tensorAction d).obj (pointedProjection.obj L)).map
          ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫
        (((tensorAction d).map (pointedProjection.map l)).app
          ((weakEquivalences C).Q.obj ((FrameTensorFubini.frame A K).obj ⦋0⦌)) ≫ eL'.inv) ≫
        (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L').hom =
        ((tensorAction d).obj (pointedProjection.obj L)).map
          ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫
        (eL.inv ≫ (weakEquivalences C).Q.map (pointedTensorMap (𝟙 (FrameTensorFubini.frame A K)) l)) ≫
        (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L').hom at h
      simpa only [Category.assoc] using h
    _ = _ := by
      have h := congrArg (fun z => ((tensorAction d).obj (pointedProjection.obj L)).map
        ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫ eL.inv ≫ z) hf
      change ((tensorAction d).obj (pointedProjection.obj L)).map
          ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫ eL.inv ≫
        ((weakEquivalences C).Q.map (pointedTensorMap (𝟙 (FrameTensorFubini.frame A K)) l) ≫
          (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L').hom) =
        ((tensorAction d).obj (pointedProjection.obj L)).map
          ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫ eL.inv ≫
        ((weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).hom ≫
          (weakEquivalences C).Q.map (pointedTensorMap (𝟙 A) (K ◁ l))) at h
      exact h.trans
        ((congrArg (fun z => ((tensorAction d).obj (pointedProjection.obj L)).map
          ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv) ≫ z)
          (Category.assoc eL.inv ((weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).hom)
            ((weakEquivalences C).Q.map (pointedTensorMap (𝟙 A) (K ◁ l)))).symm).trans
          (Category.assoc
            (((tensorAction d).obj (pointedProjection.obj L)).map
              ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).inv))
            (eL.inv ≫ (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).hom)
            ((weakEquivalences C).Q.map (pointedTensorMap (𝟙 A) (K ◁ l)))).symm)

/-- On each original coefficient, the associator compares exactly the original two tensor functors. -/
def originalComponent (X : C) (K L : PointedSSet.{vC_ActionAssociator}) :
    (((tensorAction d).obj (pointedProjection.obj K) ⊗ (tensorAction d).obj (pointedProjection.obj L)).obj
      ((weakEquivalences C).Q.obj X)) ≅
    ((tensorAction d).obj (pointedProjection.obj (K ⊗ L))).obj ((weakEquivalences C).Q.obj X) :=
  compositeIso d ((leftFrame d).obj X) (leftFrame_latching_cofibration d X) (leftFrame_map_weak d X) K L

/-- Every original coefficient arrow preserves the actual associator word. -/
theorem originalComponent_naturality {X Y : C} (f : X ⟶ Y) (K L : PointedSSet.{vC_ActionAssociator}) :
    ((tensorAction d).obj (pointedProjection.obj K) ⊗ (tensorAction d).obj (pointedProjection.obj L)).map
        ((weakEquivalences C).Q.map f) ≫ (originalComponent d Y K L).hom =
      (originalComponent d X K L).hom ≫
        ((tensorAction d).obj (pointedProjection.obj (K ⊗ L))).map ((weakEquivalences C).Q.map f) := by
  have h := compositeIso_source d (leftFrame_latching_cofibration d X) (leftFrame_map_weak d X)
    (leftFrame_latching_cofibration d Y) (leftFrame_map_weak d Y) ((leftFrame d).map f) (𝟙 K) L
  simp only [MonoidalCategory.id_tensorHom_id] at h
  change ((tensorHo d L).map ((tensorHo d K).map ((weakEquivalences C).Q.map f))) ≫
      (originalComponent d Y K L).hom =
    (originalComponent d X K L).hom ≫ (tensorHo d (K ⊗ L)).map ((weakEquivalences C).Q.map f)
  rw [tensorHo_map, tensorHo_map]
  exact h

/-- The original associator is a natural isomorphism on every coefficient Ho arrow. -/
def originalIso (K L : PointedSSet.{vC_ActionAssociator}) :
    (tensorAction d).obj (pointedProjection.obj K) ⊗ (tensorAction d).obj (pointedProjection.obj L) ≅
      (tensorAction d).obj (pointedProjection.obj (K ⊗ L)) := by
  let _ : Localization.Lifting (weakEquivalences C).Q (weakEquivalences C)
      ((weakEquivalences C).Q ⋙ ((tensorAction d).obj (pointedProjection.obj K) ⊗ (tensorAction d).obj
        (pointedProjection.obj L)))
      ((tensorAction d).obj (pointedProjection.obj K) ⊗ (tensorAction d).obj (pointedProjection.obj L)) := ⟨Iso.refl _⟩
  let _ : Localization.Lifting (weakEquivalences C).Q (weakEquivalences C)
      ((weakEquivalences C).Q ⋙ (tensorAction d).obj (pointedProjection.obj (K ⊗ L)))
      ((tensorAction d).obj (pointedProjection.obj (K ⊗ L))) := ⟨Iso.refl _⟩
  exact Localization.liftNatIso (weakEquivalences C).Q (weakEquivalences C)
    ((weakEquivalences C).Q ⋙ ((tensorAction d).obj (pointedProjection.obj K) ⊗ (tensorAction d).obj
      (pointedProjection.obj L)))
    ((weakEquivalences C).Q ⋙ (tensorAction d).obj (pointedProjection.obj (K ⊗ L)))
    ((tensorAction d).obj (pointedProjection.obj K) ⊗ (tensorAction d).obj (pointedProjection.obj L))
    ((tensorAction d).obj (pointedProjection.obj (K ⊗ L)))
    (NatIso.ofComponents (fun X => originalComponent d X K L)
      (fun {_ _} f => originalComponent_naturality d f K L))

theorem originalIso_hom_original (X : C) (K L : PointedSSet.{vC_ActionAssociator}) :
    (originalIso d K L).hom.app ((weakEquivalences C).Q.obj X) = (originalComponent d X K L).hom := by
  let _ : Localization.Lifting (weakEquivalences C).Q (weakEquivalences C)
      ((weakEquivalences C).Q ⋙ ((tensorAction d).obj (pointedProjection.obj K) ⊗ (tensorAction d).obj
        (pointedProjection.obj L)))
      ((tensorAction d).obj (pointedProjection.obj K) ⊗ (tensorAction d).obj (pointedProjection.obj L)) := ⟨Iso.refl _⟩
  let _ : Localization.Lifting (weakEquivalences C).Q (weakEquivalences C)
      ((weakEquivalences C).Q ⋙ (tensorAction d).obj (pointedProjection.obj (K ⊗ L)))
      ((tensorAction d).obj (pointedProjection.obj (K ⊗ L))) := ⟨Iso.refl _⟩
  unfold originalIso
  rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change 𝟙 _ ≫ (originalComponent d X K L).hom ≫ 𝟙 _ = (originalComponent d X K L).hom
  exact (Category.id_comp ((originalComponent d X K L).hom ≫ 𝟙 _)).trans
    (Category.comp_id (originalComponent d X K L).hom)

/-- The original pointed scalar action, before its already constructed scalar localization. -/
abbrev pointedAction : PointedSSet.{vC_ActionAssociator} ⥤
    ((weakEquivalences C).Localization ⥤ (weakEquivalences C).Localization) :=
  pointedProjection ⋙ tensorAction d

/-- The original associator is natural in every original first scalar arrow, on all coefficient Ho arrows. -/
theorem originalIso_natural_left {K K' : PointedSSet.{vC_ActionAssociator}} (k : K ⟶ K') (L :
  PointedSSet.{vC_ActionAssociator}) :
    (pointedAction d).map k ▷ (pointedAction d).obj L ≫ (originalIso d K' L).hom =
      (originalIso d K L).hom ≫ (pointedAction d).map (k ▷ L) := by
  apply Localization.natTrans_ext (weakEquivalences C).Q (weakEquivalences C)
  intro X
  change ((tensorAction d).obj (pointedProjection.obj L)).map
      (((tensorAction d).map (pointedProjection.map k)).app ((weakEquivalences C).Q.obj X)) ≫
      (originalIso d K' L).hom.app ((weakEquivalences C).Q.obj X) =
    (originalIso d K L).hom.app ((weakEquivalences C).Q.obj X) ≫
      ((tensorAction d).map (pointedProjection.map (k ▷ L))).app ((weakEquivalences C).Q.obj X)
  rw [originalIso_hom_original, originalIso_hom_original]
  have hk := congrArg (fun τ => τ.app ((weakEquivalences C).Q.obj X)) (tensorAction_map_original d k)
  have hkl := congrArg (fun τ => τ.app ((weakEquivalences C).Q.obj X)) (tensorAction_map_original d (k ▷ L))
  rw [tensorWeightMap_app] at hk hkl
  rw [hk, hkl]
  have h := compositeIso_source d (leftFrame_latching_cofibration d X) (leftFrame_map_weak d X)
    (leftFrame_latching_cofibration d X) (leftFrame_map_weak d X) (𝟙 ((leftFrame d).obj X)) k L
  rw [MonoidalCategory.tensorHom_id] at h
  exact h

/-- The original associator is natural in every original second scalar arrow, on all coefficient Ho arrows. -/
theorem originalIso_natural_right (K : PointedSSet.{vC_ActionAssociator}) {L L' :
  PointedSSet.{vC_ActionAssociator}} (l : L ⟶ L') :
    (pointedAction d).obj K ◁ (pointedAction d).map l ≫ (originalIso d K L').hom =
      (originalIso d K L).hom ≫ (pointedAction d).map (K ◁ l) := by
  apply Localization.natTrans_ext (weakEquivalences C).Q (weakEquivalences C)
  intro X
  change ((tensorAction d).map (pointedProjection.map l)).app
      (((tensorAction d).obj (pointedProjection.obj K)).obj ((weakEquivalences C).Q.obj X)) ≫
      (originalIso d K L').hom.app ((weakEquivalences C).Q.obj X) =
    (originalIso d K L).hom.app ((weakEquivalences C).Q.obj X) ≫
      ((tensorAction d).map (pointedProjection.map (K ◁ l))).app ((weakEquivalences C).Q.obj X)
  rw [originalIso_hom_original, originalIso_hom_original]
  have hkl := congrArg (fun τ => τ.app ((weakEquivalences C).Q.obj X)) (tensorAction_map_original d (K ◁ l))
  rw [tensorWeightMap_app] at hkl
  rw [hkl]
  exact compositeIso_weight d ((leftFrame d).obj X) (leftFrame_latching_cofibration d X)
    (leftFrame_map_weak d X) K l

end HomotopicalAlgebra.PointedFramingAction.ActionAssociator

end PointedActionPromotionActionAssociator


section PointedActionPromotionActionCoherenceProofs

set_option autoImplicit false

universe uC_ActionCoherenceProofs vC_ActionCoherenceProofs
open CategoryTheory Limits MorphismProperty Simplicial MonoidalCategory
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.PointedFramingAction.ActionAssociator

/-- Use the original pointed simplicial smash monoidal structure. -/
local instance pointedScalarMonoidal17 : MonoidalCategory PointedSSet.{vC_ActionCoherenceProofs} :=
  ScalarStructure.smashMonoidal
/-- Use the canonical localized pointed simplicial smash structure. -/
local instance scalarHomotopyMonoidal18 : MonoidalCategory PointedSpaceHo.{vC_ActionCoherenceProofs} :=
  ScalarStructure.monoidalHo

variable {C : Type uC_ActionCoherenceProofs} [Category.{vC_ActionCoherenceProofs} C] [ModelCategory C] [HasZeroObject C]
  [HasColimitsOfSize.{0, vC_ActionCoherenceProofs} C] [HasLimitsOfSize.{0, vC_ActionCoherenceProofs} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

/-- Every actual weighted-frame map covering the original zero comparison induces
the canonical associator simultaneously at every last weight. -/
theorem compositeIso_inv_represents (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_ActionCoherenceProofs}) (a : FrameTensorFubini.frame A K ⟶ (leftFrame d).obj
      (pointedTensor A K))
    (ha : a ≫ (augmentation d).app (pointedTensor A K) =
      FrameCoherence.augmentation (FrameTensorFubini.frame A K) ≫
        (CosimplicialObject.const C).map (FrameTensorFubini.frameZeroIso A K).hom)
    (L : PointedSSet.{vC_ActionCoherenceProofs}) :
    (compositeIso d A hA hW K L).inv =
      (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).inv ≫
        (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app L) := by
  have h := FrameDerivedComparison.canonicalIso_represents_map d (FrameTensorFubini.frame A K)
    (FrameTensorFubini.latching_cofibration A hA hW K) (FrameTensorFubini.frame_map_weak A hA hW K)
    (pointedTensor A K) (FrameTensorFubini.frameZeroIso A K).hom a ha L
  calc
    _ = (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).inv ≫
        (FrameDerivedComparison.canonicalIso d (FrameTensorFubini.frame A K)
          (FrameTensorFubini.latching_cofibration A hA hW K)
          (FrameTensorFubini.frame_map_weak A hA hW K) L).hom ≫
          ((tensorAction d).obj (pointedProjection.obj L)).map
            ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).hom) := by
      simp only [compositeIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
        Functor.mapIso_hom, Category.assoc]
      rfl
    _ = _ := congrArg
      (fun z => (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).inv ≫ z) h.symm

/-- One genuine weighted-frame comparison map supplies the inverse associator
at every original last weight, with its same original augmentation equation. -/
theorem exists_composite_frame_map (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_ActionCoherenceProofs}) :
    ∃ a : FrameTensorFubini.frame A K ⟶ (leftFrame d).obj (pointedTensor A K),
      a ≫ (augmentation d).app (pointedTensor A K) =
        FrameCoherence.augmentation (FrameTensorFubini.frame A K) ≫
          (CosimplicialObject.const C).map (FrameTensorFubini.frameZeroIso A K).hom ∧
      ∀ L : PointedSSet.{vC_ActionCoherenceProofs},
        (compositeIso d A hA hW K L).inv =
          (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).inv ≫
            (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app L) := by
  obtain ⟨a, ha⟩ := FrameCoherence.exists_map_to_chosen d (FrameTensorFubini.frame A K)
    (FrameTensorFubini.latching_cofibration A hA hW K) (pointedTensor A K)
    (FrameTensorFubini.frameZeroIso A K).hom
  exact ⟨a, ha, fun L => compositeIso_inv_represents d A hA hW K a ha L⟩

/-- Every original frame map covering a coefficient arrow preserves the complete
ordinary tensor-unit word, including the same original Q augmentation. -/
theorem tensorUnitHo_frameMap (A : CosimplicialObject C) (X : C)
    (f : A.obj ⦋0⦌ ⟶ X) (a : A ⟶ (leftFrame d).obj X)
    (ha : a ≫ (augmentation d).app X = FrameCoherence.augmentation A ≫ (CosimplicialObject.const C).map f) :
    (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app pointedUnit) ≫
        (tensorUnitHo d).hom.app ((weakEquivalences C).Q.obj X) =
      (weakEquivalences C).Q.map (tensorUnitIso A).hom ≫ (weakEquivalences C).Q.map f := by
  let B := (leftFrame d).obj X
  let φ : B.obj ⦋0⦌ ⟶ X := ((augmentation d).app X).app ⦋0⦌
  have hz := congrArg (fun τ => τ.app ⦋0⦌) ha
  have hAug : (FrameCoherence.augmentation A).app ⦋0⦌ = 𝟙 (A.obj ⦋0⦌) :=
    (congrArg A.map (SimplexCategory.hom_zero_zero (SimplexCategory.isTerminalZero.from ⦋0⦌))).trans
      (A.map_id _)
  have hzero : a.app ⦋0⦌ ≫ φ = f :=
    hz.trans ((congrArg (fun z => z ≫ f) hAug).trans (Category.id_comp f))
  have hunit := (tensorUnitHo_hom_original d X).trans (tensorUnitHoComponent_hom d X)
  have hφ : (weakEquivalences C).Q.map ((leftZeroIso d).hom.app X) ≫
      (weakEquivalences C).Q.map (d.q.app X) = (weakEquivalences C).Q.map φ :=
    ((weakEquivalences C).Q.map_comp _ _).symm.trans
      (congrArg (weakEquivalences C).Q.map (augmentation_zero d X).symm)
  have hu : (tensorUnitHo d).hom.app ((weakEquivalences C).Q.obj X) =
      (weakEquivalences C).Q.map (tensorUnitIso B).hom ≫ (weakEquivalences C).Q.map φ :=
    hunit.trans (congrArg (fun z => (weakEquivalences C).Q.map (tensorUnitIso B).hom ≫ z) hφ)
  have ht : (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app pointedUnit) ≫
      (weakEquivalences C).Q.map (tensorUnitIso B).hom =
    (weakEquivalences C).Q.map (tensorUnitIso A).hom ≫ (weakEquivalences C).Q.map (a.app ⦋0⦌) := by
    exact ((weakEquivalences C).Q.map_comp _ _).symm.trans
      ((congrArg (weakEquivalences C).Q.map (tensorUnitIso_naturality a)).trans
        ((weakEquivalences C).Q.map_comp _ _))
  let t := (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app pointedUnit)
  let v := (weakEquivalences C).Q.map (tensorUnitIso B).hom
  let p := (weakEquivalences C).Q.map φ
  exact (congrArg (fun z => t ≫ z) hu).trans
    ((Category.assoc t v p).symm.trans
      ((congrArg (fun z => z ≫ p) ht).trans
        ((Category.assoc _ _ p).trans
          ((congrArg (fun z => (weakEquivalences C).Q.map (tensorUnitIso A).hom ≫ z)
            ((weakEquivalences C).Q.map_comp _ _).symm).trans
              (congrArg (fun z => (weakEquivalences C).Q.map (tensorUnitIso A).hom ≫
                (weakEquivalences C).Q.map z) hzero)))))

/-- The actual associator at the final scalar unit agrees with the complete original
ordinary tensor-unit comparison before any scalar localization descent. -/
theorem compositeIso_right_unit (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_ActionCoherenceProofs}) :
    (compositeIso d A hA hW K pointedUnit).hom ≫
        (weakEquivalences C).Q.map (pointedTensorMap (𝟙 A) (ρ_ K).hom) =
      (tensorUnitHo d).hom.app ((weakEquivalences C).Q.obj (pointedTensor A K)) := by
  obtain ⟨a, ha, hr⟩ := exists_composite_frame_map d A hA hW K
  let F := (weakEquivalences C).Q.mapIso (FrameTensorFubini.fubiniIso A K pointedUnit)
  let u := (tensorUnitHo d).hom.app ((weakEquivalences C).Q.obj (pointedTensor A K))
  let t := (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app pointedUnit)
  let p := (weakEquivalences C).Q.map (pointedTensorMap (𝟙 A) (ρ_ K).hom)
  have hu := tensorUnitHo_frameMap d (FrameTensorFubini.frame A K) (pointedTensor A K)
    (FrameTensorFubini.frameZeroIso A K).hom a ha
  have hf := congrArg (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso_right_unit A K)
  have hfu : t ≫ u = F.hom ≫ p :=
    hu.trans (((weakEquivalences C).Q.map_comp _ _).symm.trans
      (hf.trans ((weakEquivalences C).Q.map_comp _ _)))
  have hi : (compositeIso d A hA hW K pointedUnit).inv ≫ u = p :=
    (congrArg (fun z => z ≫ u) (hr pointedUnit)).trans
      ((Category.assoc F.inv t u).trans
        ((congrArg (fun z => F.inv ≫ z) hfu).trans (F.inv_hom_id_assoc p)))
  exact (congrArg (fun z => (compositeIso d A hA hW K pointedUnit).hom ≫ z) hi.symm).trans
    ((compositeIso d A hA hW K pointedUnit).hom_inv_id_assoc u)

/-- The canonical comparison of the iterated weighted frame retains its complete
point-set frame associator and original degree-zero Fubini equation. -/
theorem iteratedFrame_comparison (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K L M : PointedSSet.{vC_ActionCoherenceProofs}) :
    (weakEquivalences C).Q.map
        (pointedTensorMap (FrameTensorFubini.frameAssociatorIso A K L).hom (𝟙 M)) ≫
      (FrameDerivedComparison.canonicalIso d (FrameTensorFubini.frame A (K ⊗ L))
        (FrameTensorFubini.latching_cofibration A hA hW (K ⊗ L))
        (FrameTensorFubini.frame_map_weak A hA hW (K ⊗ L)) M).hom ≫
      ((tensorAction d).obj (pointedProjection.obj M)).map
        ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A (K ⊗ L)).hom) =
    (FrameDerivedComparison.canonicalIso d (FrameTensorFubini.frame (FrameTensorFubini.frame A K) L)
      (FrameTensorFubini.latching_cofibration (FrameTensorFubini.frame A K)
        (FrameTensorFubini.latching_cofibration A hA hW K) (FrameTensorFubini.frame_map_weak A hA hW K) L)
      (FrameTensorFubini.frame_map_weak (FrameTensorFubini.frame A K)
        (FrameTensorFubini.latching_cofibration A hA hW K) (FrameTensorFubini.frame_map_weak A hA hW K) L) M).hom ≫
      ((tensorAction d).obj (pointedProjection.obj M)).map
        ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso (FrameTensorFubini.frame A K) L).hom) ≫
      ((tensorAction d).obj (pointedProjection.obj M)).map
        ((weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).hom) := by
  let T := (tensorAction d).obj (pointedProjection.obj M)
  let c := (FrameTensorFubini.frameAssociatorIso A K L).hom
  have hn := FrameDerivedComparison.canonicalIso_source d
    (FrameTensorFubini.latching_cofibration (FrameTensorFubini.frame A K)
      (FrameTensorFubini.latching_cofibration A hA hW K) (FrameTensorFubini.frame_map_weak A hA hW K) L)
    (FrameTensorFubini.frame_map_weak (FrameTensorFubini.frame A K)
      (FrameTensorFubini.latching_cofibration A hA hW K) (FrameTensorFubini.frame_map_weak A hA hW K) L)
    (FrameTensorFubini.latching_cofibration A hA hW (K ⊗ L))
    (FrameTensorFubini.frame_map_weak A hA hW (K ⊗ L)) c M
  have hz := FrameTensorFubini.frameAssociatorIso_zero A K L
  have hm : T.map ((weakEquivalences C).Q.map (c.app ⦋0⦌)) ≫
      T.map ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A (K ⊗ L)).hom) =
    T.map ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso (FrameTensorFubini.frame A K) L).hom) ≫
      T.map ((weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).hom) := by
    calc
      _ = T.map ((weakEquivalences C).Q.map
          (c.app ⦋0⦌ ≫ (FrameTensorFubini.frameZeroIso A (K ⊗ L)).hom)) :=
        (T.map_comp _ _).symm.trans (congrArg T.map ((weakEquivalences C).Q.map_comp _ _).symm)
      _ = T.map ((weakEquivalences C).Q.map
          ((FrameTensorFubini.frameZeroIso (FrameTensorFubini.frame A K) L).hom ≫
            (FrameTensorFubini.fubiniIso A K L).hom)) :=
        congrArg (fun z => T.map ((weakEquivalences C).Q.map z)) hz
      _ = _ := (congrArg T.map ((weakEquivalences C).Q.map_comp _ _)).trans (T.map_comp _ _)
  have he := congrArg (fun z => z ≫ T.map
    ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A (K ⊗ L)).hom)) hn
  exact (Category.assoc _ _ _).symm.trans
    (he.trans ((Category.assoc _ _ _).trans (congrArg (fun z => _ ≫ z) hm)))

omit [HasLimitsOfSize.{0, vC_ActionCoherenceProofs} C] in
/-- The inverse point-set Fubini associativity word retains the original entire
iterated-frame associator. -/
theorem fubiniIso_inverse_associativity (A : CosimplicialObject C) (K L M : PointedSSet.{vC_ActionCoherenceProofs}) :
    pointedTensorMap (𝟙 A) (α_ K L M).inv ≫ (FrameTensorFubini.fubiniIso A (K ⊗ L) M).inv =
      (FrameTensorFubini.fubiniIso A K (L ⊗ M)).inv ≫
        (FrameTensorFubini.fubiniIso (FrameTensorFubini.frame A K) L M).inv ≫
          pointedTensorMap (FrameTensorFubini.frameAssociatorIso A K L).hom (𝟙 M) := by
  let R := ((pointedTensorBifunctor).mapIso (FrameTensorFubini.frameAssociatorIso A K L)).app M
  let F := FrameTensorFubini.fubiniIso A (K ⊗ L) M
  let G := FrameTensorFubini.fubiniIso (FrameTensorFubini.frame A K) L M
  let H := FrameTensorFubini.fubiniIso A K (L ⊗ M)
  let U := (pointedTensorBifunctor.obj A).mapIso (α_ K L M)
  have hs : (R ≪≫ F ≪≫ U).hom = (G ≪≫ H).hom :=
    FrameTensorFubini.fubiniIso_associativity A K L M
  have he : R ≪≫ F ≪≫ U = G ≪≫ H := Iso.ext hs
  have hi := congrArg (fun i => i.inv) he
  have hc : U.inv ≫ F.inv = H.inv ≫ G.inv ≫ R.hom :=
    (Category.comp_id (U.inv ≫ F.inv)).symm.trans
      ((congrArg (fun z => (U.inv ≫ F.inv) ≫ z) R.inv_hom_id.symm).trans
        ((Category.assoc (U.inv ≫ F.inv) R.inv R.hom).symm.trans
          ((congrArg (fun z => z ≫ R.hom) hi).trans (Category.assoc H.inv G.inv R.hom))))
  exact hc

/-- The inverse derived associator retains its complete original Fubini,
canonical HFC, and weighted degree-zero word. -/
theorem compositeIso_inv_word (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K L : PointedSSet.{vC_ActionCoherenceProofs}) :
    (compositeIso d A hA hW K L).inv =
      (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).inv ≫
        (FrameDerivedComparison.canonicalIso d (FrameTensorFubini.frame A K)
          (FrameTensorFubini.latching_cofibration A hA hW K)
          (FrameTensorFubini.frame_map_weak A hA hW K) L).hom ≫
          ((tensorAction d).obj (pointedProjection.obj L)).map
            ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A K).hom) := by
  simp only [compositeIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    Functor.mapIso_hom, Category.assoc]
  rfl

/-- The derived composite on the iterated weighted frame agrees with the same
original scalar associator and Fubini maps. -/
theorem iteratedCompositeIso (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K L M : PointedSSet.{vC_ActionCoherenceProofs}) :
    (weakEquivalences C).Q.map (pointedTensorMap (𝟙 A) (α_ K L M).inv) ≫
        (compositeIso d A hA hW (K ⊗ L) M).inv =
      (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K (L ⊗ M)).inv ≫
        (compositeIso d (FrameTensorFubini.frame A K)
          (FrameTensorFubini.latching_cofibration A hA hW K)
          (FrameTensorFubini.frame_map_weak A hA hW K) L M).inv ≫
        ((tensorAction d).obj (pointedProjection.obj M)).map
          ((weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).hom) := by
  let Γ := FrameTensorFubini.frame A K
  let T := (tensorAction d).obj (pointedProjection.obj M)
  let F := (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A (K ⊗ L) M).inv
  let G := (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso Γ L M).inv
  let H := (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K (L ⊗ M)).inv
  let c := (weakEquivalences C).Q.map
    (pointedTensorMap (FrameTensorFubini.frameAssociatorIso A K L).hom (𝟙 M))
  let p := (weakEquivalences C).Q.map (pointedTensorMap (𝟙 A) (α_ K L M).inv)
  let e₁ := (FrameDerivedComparison.canonicalIso d (FrameTensorFubini.frame A (K ⊗ L))
    (FrameTensorFubini.latching_cofibration A hA hW (K ⊗ L))
    (FrameTensorFubini.frame_map_weak A hA hW (K ⊗ L)) M).hom
  let z₁ := T.map ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A (K ⊗ L)).hom)
  let e₂ := (FrameDerivedComparison.canonicalIso d (FrameTensorFubini.frame Γ L)
    (FrameTensorFubini.latching_cofibration Γ (FrameTensorFubini.latching_cofibration A hA hW K)
      (FrameTensorFubini.frame_map_weak A hA hW K) L)
    (FrameTensorFubini.frame_map_weak Γ (FrameTensorFubini.latching_cofibration A hA hW K)
      (FrameTensorFubini.frame_map_weak A hA hW K) L) M).hom
  let z₂ := T.map ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso Γ L).hom)
  let f := T.map ((weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso A K L).hom)
  have hp : p ≫ F = H ≫ G ≫ c :=
    ((weakEquivalences C).Q.map_comp _ _).symm.trans
      ((congrArg (weakEquivalences C).Q.map (fubiniIso_inverse_associativity A K L M)).trans
        (((weakEquivalences C).Q.map_comp _ _).trans
          (congrArg (fun z => H ≫ z) ((weakEquivalences C).Q.map_comp _ _))))
  have hc : c ≫ e₁ ≫ z₁ = e₂ ≫ z₂ ≫ f := iteratedFrame_comparison d A hA hW K L M
  have h₁ : (compositeIso d A hA hW (K ⊗ L) M).inv = F ≫ e₁ ≫ z₁ :=
    compositeIso_inv_word d A hA hW (K ⊗ L) M
  have h₂ : (compositeIso d Γ (FrameTensorFubini.latching_cofibration A hA hW K)
      (FrameTensorFubini.frame_map_weak A hA hW K) L M).inv = G ≫ e₂ ≫ z₂ :=
    compositeIso_inv_word d Γ (FrameTensorFubini.latching_cofibration A hA hW K)
      (FrameTensorFubini.frame_map_weak A hA hW K) L M
  calc
    _ = p ≫ F ≫ e₁ ≫ z₁ := congrArg (fun z => p ≫ z) h₁
    _ = (p ≫ F) ≫ e₁ ≫ z₁ := (Category.assoc p F (e₁ ≫ z₁)).symm
    _ = (H ≫ G ≫ c) ≫ e₁ ≫ z₁ := congrArg (fun z => z ≫ e₁ ≫ z₁) hp
    _ = H ≫ G ≫ (c ≫ e₁ ≫ z₁) := by simp only [Category.assoc]
    _ = H ≫ G ≫ (e₂ ≫ z₂ ≫ f) := congrArg (fun z => H ≫ G ≫ z) hc
    _ = H ≫ (G ≫ e₂ ≫ z₂) ≫ f :=
      (congrArg (fun z => H ≫ G ≫ z) (Category.assoc e₂ z₂ f).symm).trans
        (congrArg (fun z => H ≫ z) (Category.assoc G (e₂ ≫ z₂) f).symm)
    _ = _ := congrArg (fun z => H ≫ z ≫ f) h₂.symm

/-- The actual original scalar associator satisfies the full inverse pentagon for
the constructed derived framing composites. -/
theorem compositeIso_inverse_pentagon (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K L M : PointedSSet.{vC_ActionCoherenceProofs}) :
    (weakEquivalences C).Q.map (pointedTensorMap (𝟙 A) (α_ K L M).inv) ≫
        (compositeIso d A hA hW (K ⊗ L) M).inv ≫
        ((tensorAction d).obj (pointedProjection.obj M)).map (compositeIso d A hA hW K L).inv =
      (compositeIso d A hA hW K (L ⊗ M)).inv ≫
        (compositeIso d ((leftFrame d).obj (pointedTensor A K))
          (leftFrame_latching_cofibration d (pointedTensor A K))
          (leftFrame_map_weak d (pointedTensor A K)) L M).inv := by
  obtain ⟨a, ha, hr⟩ := exists_composite_frame_map d A hA hW K
  let Γ := FrameTensorFubini.frame A K
  let T := (tensorAction d).obj (pointedProjection.obj M)
  let F := (weakEquivalences C).Q.mapIso (FrameTensorFubini.fubiniIso A K L)
  let H := (weakEquivalences C).Q.mapIso (FrameTensorFubini.fubiniIso A K (L ⊗ M))
  let q := (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app L)
  let q' := (weakEquivalences C).Q.map ((pointedTensorBifunctor.map a).app (L ⊗ M))
  let i := (compositeIso d Γ (FrameTensorFubini.latching_cofibration A hA hW K)
    (FrameTensorFubini.frame_map_weak A hA hW K) L M).inv
  let j := (compositeIso d ((leftFrame d).obj (pointedTensor A K))
    (leftFrame_latching_cofibration d (pointedTensor A K))
    (leftFrame_map_weak d (pointedTensor A K)) L M).inv
  have hn : q' ≫ j = i ≫ T.map q :=
    compositeIso_frame_inverse d (FrameTensorFubini.latching_cofibration A hA hW K)
      (FrameTensorFubini.frame_map_weak A hA hW K)
      (leftFrame_latching_cofibration d (pointedTensor A K))
      (leftFrame_map_weak d (pointedTensor A K)) a L M
  have ht : T.map F.hom ≫ T.map (compositeIso d A hA hW K L).inv = T.map q :=
    (T.map_comp _ _).symm.trans
      ((congrArg (fun z => T.map (F.hom ≫ z)) (hr L)).trans
        (congrArg T.map (F.hom_inv_id_assoc q)))
  have hp := congrArg
    (fun z => z ≫ T.map (compositeIso d A hA hW K L).inv)
    (iteratedCompositeIso d A hA hW K L M)
  let m := T.map (compositeIso d A hA hW K L).inv
  have hb : (H.inv ≫ i ≫ T.map F.hom) ≫ m = H.inv ≫ i ≫ (T.map F.hom ≫ m) :=
    (Category.assoc H.inv (i ≫ T.map F.hom) m).trans
      (congrArg (fun z => H.inv ≫ z) (Category.assoc i (T.map F.hom) m))
  exact (Category.assoc _ _ m).symm.trans
    (hp.trans (hb.trans
      ((congrArg (fun z => H.inv ≫ i ≫ z) ht).trans
        ((congrArg (fun z => H.inv ≫ z) hn.symm).trans
          ((Category.assoc H.inv q' j).symm.trans
            (congrArg (fun z => z ≫ j) (hr (L ⊗ M)).symm))))))

end HomotopicalAlgebra.PointedFramingAction.ActionAssociator

end PointedActionPromotionActionCoherenceProofs


section PointedActionPromotionRawCoreMonoidal

set_option autoImplicit false

universe uC_RawCoreMonoidal vC_RawCoreMonoidal
open CategoryTheory Limits MorphismProperty Simplicial MonoidalCategory
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.PointedFramingAction.ActionAssociator

/-- Use the original pointed simplicial smash monoidal structure. -/
local instance pointedScalarMonoidal19 : MonoidalCategory PointedSSet.{vC_RawCoreMonoidal} :=
  ScalarStructure.smashMonoidal
/-- Use the canonical localized pointed simplicial smash structure. -/
local instance scalarHomotopyMonoidal20 : MonoidalCategory PointedSpaceHo.{vC_RawCoreMonoidal} :=
  ScalarStructure.monoidalHo

variable {C : Type uC_RawCoreMonoidal} [Category.{vC_RawCoreMonoidal} C] [ModelCategory C] [HasZeroObject C]
  [HasColimitsOfSize.{0, vC_RawCoreMonoidal} C] [HasLimitsOfSize.{0, vC_RawCoreMonoidal} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

/-- Use the native coefficient endofunctor monoidal structure given by composition. -/
local instance coefficientEndofunctorsMonoidal21 : MonoidalCategory ((weakEquivalences C).Localization ⥤
    (weakEquivalences C).Localization) := endofunctorMonoidalCategory (weakEquivalences C).Localization

/-- The first scalar unit coherence retains the entire original unit-frame,
Fubini, and canonical HFC comparison maps. -/
theorem compositeIso_left_unit_frame (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (K : PointedSSet.{vC_RawCoreMonoidal}) :
    (compositeIso d A hA hW pointedUnit K).hom ≫
        (weakEquivalences C).Q.map (pointedTensorMap (𝟙 A) (λ_ K).hom) ≫
        (FrameDerivedComparison.canonicalIso d A hA hW K).hom =
      ((tensorAction d).obj (pointedProjection.obj K)).map
        ((weakEquivalences C).Q.map (tensorUnitIso A).hom) := by
  let Γ := FrameTensorFubini.frame A pointedUnit
  let T := (tensorAction d).obj (pointedProjection.obj K)
  let e := (FrameDerivedComparison.canonicalIso d A hA hW K).hom
  let eΓ := (FrameDerivedComparison.canonicalIso d Γ
    (FrameTensorFubini.latching_cofibration A hA hW pointedUnit)
    (FrameTensorFubini.frame_map_weak A hA hW pointedUnit) K).hom
  let F := (weakEquivalences C).Q.mapIso (FrameTensorFubini.fubiniIso A pointedUnit K)
  let g := T.map ((weakEquivalences C).Q.map (FrameTensorFubini.frameZeroIso A pointedUnit).hom)
  let u := T.map ((weakEquivalences C).Q.map (tensorUnitIso A).hom)
  let c := (FrameTensorFubini.frameUnitIso A).hom
  let tc := (weakEquivalences C).Q.map (pointedTensorMap c (𝟙 K))
  let p := (weakEquivalences C).Q.map (pointedTensorMap (𝟙 A) (λ_ K).hom)
  have hm : T.map ((weakEquivalences C).Q.map (c.app ⦋0⦌)) = g ≫ u :=
    (congrArg (fun z => T.map ((weakEquivalences C).Q.map z)) (FrameTensorFubini.frameUnitIso_zero A)).trans
      ((congrArg T.map ((weakEquivalences C).Q.map_comp _ _)).trans (T.map_comp _ _))
  have hc : tc ≫ e = eΓ ≫ g ≫ u :=
    (FrameDerivedComparison.canonicalIso_source d
      (FrameTensorFubini.latching_cofibration A hA hW pointedUnit)
      (FrameTensorFubini.frame_map_weak A hA hW pointedUnit) hA hW c K).trans
        (congrArg (fun z => eΓ ≫ z) hm)
  have hf : tc = F.hom ≫ p :=
    (congrArg (weakEquivalences C).Q.map (FrameTensorFubini.fubiniIso_left_unit A K)).trans
      ((weakEquivalences C).Q.map_comp _ _)
  have hn : eΓ ≫ g ≫ u = F.hom ≫ p ≫ e :=
    hc.symm.trans ((congrArg (fun z => z ≫ e) hf).trans (Category.assoc F.hom p e))
  have hw : (compositeIso d A hA hW pointedUnit K).inv = F.inv ≫ eΓ ≫ g :=
    compositeIso_inv_word d A hA hW pointedUnit K
  have hi : (compositeIso d A hA hW pointedUnit K).inv ≫ u = p ≫ e :=
    (congrArg (fun z => z ≫ u) hw).trans
      ((Category.assoc F.inv (eΓ ≫ g) u).trans
        ((congrArg (fun z => F.inv ≫ z) (Category.assoc eΓ g u)).trans
          ((congrArg (fun z => F.inv ≫ z) hn).trans (F.inv_hom_id_assoc (p ≫ e)))))
  exact (congrArg (fun z => (compositeIso d A hA hW pointedUnit K).hom ≫ z) hi.symm).trans
    ((compositeIso d A hA hW pointedUnit K).hom_inv_id_assoc u)

omit [HasZeroObject C] [HasColimitsOfSize.{0, vC_RawCoreMonoidal} C] [HasLimitsOfSize.{0, vC_RawCoreMonoidal} C] in
/-- The actual chosen augmentation factors through its original zero-degree map. -/
theorem chosenAugmentation_factor (X : C) :
    (augmentation d).app X = FrameCoherence.augmentation ((leftFrame d).obj X) ≫
      (CosimplicialObject.const C).map (((augmentation d).app X).app ⦋0⦌) := by
  have h := FrameCoherence.augmentation_square ((augmentation d).app X)
  have hi : FrameCoherence.augmentation ((CosimplicialObject.const C).obj X) = 𝟙 _ := by
    ext n
    rfl
  exact (Category.comp_id ((augmentation d).app X)).symm.trans
    ((congrArg (fun z => (augmentation d).app X ≫ z) hi.symm).trans h)

/-- The ordinary unit component is the actual pointed tensor unit followed by
the same original zero-degree Q augmentation map. -/
theorem unitHo_original_word (X : C) :
    (tensorUnitHo d).hom.app ((weakEquivalences C).Q.obj X) =
      (weakEquivalences C).Q.map (tensorUnitIso ((leftFrame d).obj X)).hom ≫
        (weakEquivalences C).Q.map (((augmentation d).app X).app ⦋0⦌) := by
  let A := (leftFrame d).obj X
  let φ : A.obj ⦋0⦌ ⟶ X := ((augmentation d).app X).app ⦋0⦌
  have h := tensorUnitHo_frameMap d A X φ (𝟙 A)
    ((Category.id_comp ((augmentation d).app X)).trans (chosenAugmentation_factor d X))
  have hi : (weakEquivalences C).Q.map ((pointedTensorBifunctor.map (𝟙 A)).app pointedUnit) = 𝟙 _ :=
    (congrArg (fun τ => (weakEquivalences C).Q.map (τ.app pointedUnit)) (pointedTensorBifunctor.map_id A)).trans
      ((weakEquivalences C).Q.map_id _)
  exact (Category.id_comp ((tensorUnitHo d).hom.app ((weakEquivalences C).Q.obj X))).symm.trans
    ((congrArg (fun z => z ≫ (tensorUnitHo d).hom.app ((weakEquivalences C).Q.obj X)) hi.symm).trans h)

/-- The first scalar unit coherence for a chosen frame retains the complete
ordinary unit word on every original coefficient. -/
theorem compositeIso_left_unit (X : C) (K : PointedSSet.{vC_RawCoreMonoidal}) :
    (originalComponent d X pointedUnit K).hom ≫
        (weakEquivalences C).Q.map (pointedTensorMap (𝟙 ((leftFrame d).obj X)) (λ_ K).hom) =
      ((tensorAction d).obj (pointedProjection.obj K)).map
        ((tensorUnitHo d).hom.app ((weakEquivalences C).Q.obj X)) := by
  let A := (leftFrame d).obj X
  let T := (tensorAction d).obj (pointedProjection.obj K)
  let m := (originalComponent d X pointedUnit K).hom
  let p := (weakEquivalences C).Q.map (pointedTensorMap (𝟙 A) (λ_ K).hom)
  let e := (FrameDerivedComparison.canonicalIso d A (leftFrame_latching_cofibration d X)
    (leftFrame_map_weak d X) K).hom
  let φ : A.obj ⦋0⦌ ⟶ X := ((augmentation d).app X).app ⦋0⦌
  let q := T.map ((weakEquivalences C).Q.map φ)
  let u := (weakEquivalences C).Q.map (tensorUnitIso A).hom
  have hn : e ≫ q = 𝟙 _ := FrameDerivedComparison.canonicalIso_chosen d X K
  have hg : m ≫ p ≫ e = T.map u :=
    compositeIso_left_unit_frame d A (leftFrame_latching_cofibration d X) (leftFrame_map_weak d X) K
  have hu : u ≫ (weakEquivalences C).Q.map φ =
      (tensorUnitHo d).hom.app ((weakEquivalences C).Q.obj X) := (unitHo_original_word d X).symm
  have hv : T.map u ≫ q = T.map ((tensorUnitHo d).hom.app ((weakEquivalences C).Q.obj X)) :=
    (T.map_comp _ _).symm.trans (congrArg T.map hu)
  exact (Category.comp_id (m ≫ p)).symm.trans
    ((congrArg (fun z => (m ≫ p) ≫ z) hn.symm).trans
      ((Category.assoc (m ≫ p) e q).symm.trans
        ((congrArg (fun z => z ≫ q) ((Category.assoc m p e).trans hg)).trans hv)))

/-- The inverse of the full coefficient-Ho associator retains its same original component. -/
theorem originalIso_inv_original (X : C) (K L : PointedSSet.{vC_RawCoreMonoidal}) :
    (originalIso d K L).inv.app ((weakEquivalences C).Q.obj X) = (originalComponent d X K L).inv := by
  have h : (originalIso d K L).app ((weakEquivalences C).Q.obj X) = originalComponent d X K L :=
    Iso.ext (originalIso_hom_original d X K L)
  exact congrArg (fun i => i.inv) h

/-- Every original scalar arrow acts by the same actual chosen-frame tensor map. -/
theorem pointedAction_map_original {K L : PointedSSet.{vC_RawCoreMonoidal}} (k : K ⟶ L) (X : C) :
    ((pointedAction d).map k).app ((weakEquivalences C).Q.obj X) =
      (weakEquivalences C).Q.map (pointedTensorMap (𝟙 ((leftFrame d).obj X)) k) :=
  (congrArg (fun τ => τ.app ((weakEquivalences C).Q.obj X)) (tensorAction_map_original d k)).trans
    (tensorWeightMap_app d k X)

/-- The exact original associator inverses are natural in every first scalar arrow. -/
theorem originalIso_inv_natural_left {K K' : PointedSSet.{vC_RawCoreMonoidal}} (k : K ⟶ K') (L :
  PointedSSet.{vC_RawCoreMonoidal}) :
    (originalIso d K L).inv ≫ (pointedAction d).map k ▷ (pointedAction d).obj L =
      (pointedAction d).map (k ▷ L) ≫ (originalIso d K' L).inv := by
  apply (cancel_mono (originalIso d K' L).hom).mp
  rw [Category.assoc, originalIso_natural_left, Iso.inv_hom_id_assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The exact original associator inverses are natural in every second scalar arrow. -/
theorem originalIso_inv_natural_right (K : PointedSSet.{vC_RawCoreMonoidal}) {L L' :
  PointedSSet.{vC_RawCoreMonoidal}} (l : L ⟶ L') :
    (originalIso d K L).inv ≫ (pointedAction d).obj K ◁ (pointedAction d).map l =
      (pointedAction d).map (K ◁ l) ≫ (originalIso d K L').inv := by
  apply (cancel_mono (originalIso d K L').hom).mp
  rw [Category.assoc, originalIso_natural_right, Iso.inv_hom_id_assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The original scalar associator gives the complete native inverse-associativity
law of the constructed scalar functor into actual coefficient endofunctors. -/
theorem originalIso_oplax_associativity (K L M : PointedSSet.{vC_RawCoreMonoidal}) :
    (originalIso d (K ⊗ L) M).inv ≫ (originalIso d K L).inv ▷ (pointedAction d).obj M ≫
        (α_ ((pointedAction d).obj K) ((pointedAction d).obj L) ((pointedAction d).obj M)).hom =
      (pointedAction d).map (α_ K L M).hom ≫ (originalIso d K (L ⊗ M)).inv ≫
        (pointedAction d).obj K ◁ (originalIso d L M).inv := by
  apply Localization.natTrans_ext (weakEquivalences C).Q (weakEquivalences C)
  intro X
  let A := (leftFrame d).obj X
  let T := (pointedAction d).obj M
  let P := (weakEquivalences C).Q.mapIso ((pointedTensorBifunctor.obj A).mapIso (α_ K L M))
  let u := (compositeIso d A (leftFrame_latching_cofibration d X) (leftFrame_map_weak d X) (K ⊗ L) M).inv
  let v := (compositeIso d A (leftFrame_latching_cofibration d X) (leftFrame_map_weak d X) K L).inv
  let w := (compositeIso d A (leftFrame_latching_cofibration d X) (leftFrame_map_weak d X) K (L ⊗ M)).inv
  let z := (compositeIso d ((leftFrame d).obj (pointedTensor A K))
    (leftFrame_latching_cofibration d (pointedTensor A K))
    (leftFrame_map_weak d (pointedTensor A K)) L M).inv
  have hp := compositeIso_inverse_pentagon d A (leftFrame_latching_cofibration d X)
    (leftFrame_map_weak d X) K L M
  have h : u ≫ T.map v = P.hom ≫ w ≫ z :=
    (P.hom_inv_id_assoc (u ≫ T.map v)).symm.trans (congrArg (fun q => P.hom ≫ q) hp)
  have h₀ : (originalIso d (K ⊗ L) M).inv.app ((weakEquivalences C).Q.obj X) = u :=
    originalIso_inv_original d X (K ⊗ L) M
  have h₁ : (originalIso d K L).inv.app ((weakEquivalences C).Q.obj X) = v :=
    originalIso_inv_original d X K L
  have h₂ : (originalIso d K (L ⊗ M)).inv.app ((weakEquivalences C).Q.obj X) = w :=
    originalIso_inv_original d X K (L ⊗ M)
  have h₃ : (originalIso d L M).inv.app (((pointedAction d).obj K).obj ((weakEquivalences C).Q.obj X)) = z :=
    originalIso_inv_original d (pointedTensor A K) L M
  have hP : ((pointedAction d).map (α_ K L M).hom).app ((weakEquivalences C).Q.obj X) = P.hom :=
    pointedAction_map_original d (α_ K L M).hom X
  change (originalIso d (K ⊗ L) M).inv.app ((weakEquivalences C).Q.obj X) ≫
      T.map ((originalIso d K L).inv.app ((weakEquivalences C).Q.obj X)) ≫ 𝟙 _ =
    ((pointedAction d).map (α_ K L M).hom).app ((weakEquivalences C).Q.obj X) ≫
      (originalIso d K (L ⊗ M)).inv.app ((weakEquivalences C).Q.obj X) ≫
        (originalIso d L M).inv.app (((pointedAction d).obj K).obj ((weakEquivalences C).Q.obj X))
  have hl := (congrArg (fun q => (originalIso d (K ⊗ L) M).inv.app ((weakEquivalences C).Q.obj X) ≫ q)
    (Category.comp_id (T.map ((originalIso d K L).inv.app ((weakEquivalences C).Q.obj X))))).trans
      ((congrArg (fun q => q ≫ T.map ((originalIso d K L).inv.app ((weakEquivalences C).Q.obj X))) h₀).trans
        (congrArg (fun q => u ≫ T.map q) h₁))
  have hr := (congrArg (fun q => q ≫ (originalIso d K (L ⊗ M)).inv.app ((weakEquivalences C).Q.obj X) ≫
      (originalIso d L M).inv.app (((pointedAction d).obj K).obj ((weakEquivalences C).Q.obj X))) hP).trans
    ((congrArg (fun q => P.hom ≫ q ≫
      (originalIso d L M).inv.app (((pointedAction d).obj K).obj ((weakEquivalences C).Q.obj X))) h₂).trans
        (congrArg (fun q => P.hom ≫ w ≫ q) h₃))
  exact hl.trans (h.trans hr.symm)

/-- The inverse left unit law retains the exact same ordinary unit natural transformation. -/
theorem originalIso_oplax_left_unitality (K : PointedSSet.{vC_RawCoreMonoidal}) :
    (λ_ ((pointedAction d).obj K)).inv =
      (pointedAction d).map (λ_ K).inv ≫ (originalIso d pointedUnit K).inv ≫
        (tensorUnitHo d).hom ▷ (pointedAction d).obj K := by
  apply Localization.natTrans_ext (weakEquivalences C).Q (weakEquivalences C)
  intro X
  let A := (leftFrame d).obj X
  let T := (pointedAction d).obj K
  let P := (weakEquivalences C).Q.mapIso ((pointedTensorBifunctor.obj A).mapIso (λ_ K))
  let m := originalComponent d X pointedUnit K
  let u := T.map ((tensorUnitHo d).hom.app ((weakEquivalences C).Q.obj X))
  have hu : m.hom ≫ P.hom = u := compositeIso_left_unit d X K
  have hc : P.inv ≫ m.inv ≫ u = 𝟙 _ :=
    (congrArg (fun q => P.inv ≫ m.inv ≫ q) hu.symm).trans
      ((congrArg (fun q => P.inv ≫ q) (m.inv_hom_id_assoc P.hom)).trans P.inv_hom_id)
  have hP : ((pointedAction d).map (λ_ K).inv).app ((weakEquivalences C).Q.obj X) = P.inv :=
    pointedAction_map_original d (λ_ K).inv X
  have hm : (originalIso d pointedUnit K).inv.app ((weakEquivalences C).Q.obj X) = m.inv :=
    originalIso_inv_original d X pointedUnit K
  change 𝟙 _ = ((pointedAction d).map (λ_ K).inv).app ((weakEquivalences C).Q.obj X) ≫
    (originalIso d pointedUnit K).inv.app ((weakEquivalences C).Q.obj X) ≫ u
  exact hc.symm.trans
    ((congrArg (fun q => q ≫ m.inv ≫ u) hP.symm).trans
      (congrArg (fun q => ((pointedAction d).map (λ_ K).inv).app ((weakEquivalences C).Q.obj X) ≫ q ≫ u) hm.symm))

/-- The inverse right unit law retains the exact same ordinary unit natural transformation. -/
theorem originalIso_oplax_right_unitality (K : PointedSSet.{vC_RawCoreMonoidal}) :
    (ρ_ ((pointedAction d).obj K)).inv =
      (pointedAction d).map (ρ_ K).inv ≫ (originalIso d K pointedUnit).inv ≫
        (pointedAction d).obj K ◁ (tensorUnitHo d).hom := by
  apply Localization.natTrans_ext (weakEquivalences C).Q (weakEquivalences C)
  intro X
  let A := (leftFrame d).obj X
  let P := (weakEquivalences C).Q.mapIso ((pointedTensorBifunctor.obj A).mapIso (ρ_ K))
  let m := originalComponent d X K pointedUnit
  let u := (tensorUnitHo d).hom.app (((pointedAction d).obj K).obj ((weakEquivalences C).Q.obj X))
  have hu : m.hom ≫ P.hom = u :=
    compositeIso_right_unit d A (leftFrame_latching_cofibration d X) (leftFrame_map_weak d X) K
  have hc : P.inv ≫ m.inv ≫ u = 𝟙 _ :=
    (congrArg (fun q => P.inv ≫ m.inv ≫ q) hu.symm).trans
      ((congrArg (fun q => P.inv ≫ q) (m.inv_hom_id_assoc P.hom)).trans P.inv_hom_id)
  have hP : ((pointedAction d).map (ρ_ K).inv).app ((weakEquivalences C).Q.obj X) = P.inv :=
    pointedAction_map_original d (ρ_ K).inv X
  have hm : (originalIso d K pointedUnit).inv.app ((weakEquivalences C).Q.obj X) = m.inv :=
    originalIso_inv_original d X K pointedUnit
  change 𝟙 _ = ((pointedAction d).map (ρ_ K).inv).app ((weakEquivalences C).Q.obj X) ≫
    (originalIso d K pointedUnit).inv.app ((weakEquivalences C).Q.obj X) ≫ u
  exact hc.symm.trans
    ((congrArg (fun q => q ≫ m.inv ≫ u) hP.symm).trans
      (congrArg (fun q => ((pointedAction d).map (ρ_ K).inv).app ((weakEquivalences C).Q.obj X) ≫ q ≫ u) hm.symm))

end HomotopicalAlgebra.PointedFramingAction.ActionAssociator

namespace HomotopicalAlgebra.PointedFramingAction.ActionCoherence

open ActionAssociator
/-- Use the original pointed simplicial smash monoidal structure. -/
local instance pointedScalarMonoidal22 : MonoidalCategory PointedSSet.{vC_RawCoreMonoidal} :=
  ScalarStructure.smashMonoidal
/-- Use the canonical localized pointed simplicial smash structure. -/
local instance scalarHomotopyMonoidal23 : MonoidalCategory PointedSpaceHo.{vC_RawCoreMonoidal} :=
  ScalarStructure.monoidalHo

variable {C : Type uC_RawCoreMonoidal} [Category.{vC_RawCoreMonoidal} C] [ModelCategory C] [HasZeroObject C]
  [HasColimitsOfSize.{0, vC_RawCoreMonoidal} C] [HasLimitsOfSize.{0, vC_RawCoreMonoidal} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

/-- Use the native coefficient endofunctor monoidal structure given by composition. -/
local instance coefficientEndofunctorsMonoidal24 : MonoidalCategory ((weakEquivalences C).Localization ⥤
    (weakEquivalences C).Localization) := endofunctorMonoidalCategory (weakEquivalences C).Localization

/-- The original frames and their actual HFC/Fubini comparisons construct the complete
native strong monoidal scalar functor into the original coefficient endofunctors. -/
def pointedActionCoreMonoidal : (pointedAction d).CoreMonoidal :=
  Functor.CoreMonoidal.mk' (tensorUnitHo d).symm (originalIso d)
    (originalIso_inv_natural_left d) (fun {_ _} K l => originalIso_inv_natural_right d K l)
    (originalIso_oplax_associativity d) (originalIso_oplax_left_unitality d)
    (originalIso_oplax_right_unitality d)

/-- The actual raw pointed scalar action has the native strong monoidal structure. -/
@[instance_reducible]
def pointedActionMonoidal : (pointedAction d).Monoidal := (pointedActionCoreMonoidal d).toMonoidal

end HomotopicalAlgebra.PointedFramingAction.ActionCoherence

end PointedActionPromotionRawCoreMonoidal


section PointedActionPromotionClosedAction

set_option autoImplicit false

universe uC_ClosedAction vC_ClosedAction
open CategoryTheory Limits MorphismProperty Simplicial MonoidalCategory
open scoped MonoidalCategory MonoidalRightAction SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.PointedFramingAction

/-- Use the original pointed simplicial smash monoidal structure. -/
local instance pointedScalarMonoidal25 : MonoidalCategory PointedSSet.{vC_ClosedAction} := ScalarStructure.smashMonoidal
/-- Use the canonical localized pointed simplicial smash structure. -/
local instance scalarHomotopyMonoidal26 : MonoidalCategory PointedSpaceHo.{vC_ClosedAction} :=
  ScalarStructure.monoidalHo
/-- The original weak localization is strong monoidal for smash. -/
local instance pointedScalarProjectionMonoidal27 : pointedProjection.{vC_ClosedAction}.Monoidal :=
  ScalarStructure.projectionMonoidal

variable {C : Type uC_ClosedAction} [Category.{vC_ClosedAction} C] [ModelCategory C] [HasZeroObject C]
  [HasColimitsOfSize.{0, vC_ClosedAction} C] [HasLimitsOfSize.{0, vC_ClosedAction} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

/-- Use the native coefficient endofunctor monoidal structure given by composition. -/
local instance coefficientEndofunctorsMonoidal28 : MonoidalCategory ((weakEquivalences C).Localization ⥤
    (weakEquivalences C).Localization) := endofunctorMonoidalCategory (weakEquivalences C).Localization

/-- The actual framing action is strong monoidal on all scalar Ho objects and arrows.
The native localized monoidal universal property transports the proved original
frame Fubini, pentagon and unit comparisons through the genuine weak localization. -/
@[instance_reducible]
def tensorActionMonoidal : (tensorAction d).Monoidal := by
  letI : (ActionAssociator.pointedAction d).Monoidal := ActionCoherence.pointedActionMonoidal d
  letI : Localization.Lifting pointedProjection (weakEquivalences PointedSSet.{vC_ClosedAction})
      (ActionAssociator.pointedAction d) (tensorAction d) := ⟨Iso.refl _⟩
  exact Localization.Monoidal.functorMonoidalOfComp pointedProjection
    (weakEquivalences PointedSSet.{vC_ClosedAction}) (tensorAction d) (ActionAssociator.pointedAction d)

/-- The full localized tensorator retains the original frame Fubini comparison followed by the actual inverse scalar
comparison. -/
theorem tensorActionMonoidal_tensorator (K L : PointedSSet.{vC_ClosedAction}) :
    let _ := tensorActionMonoidal d
    Functor.LaxMonoidal.μ (tensorAction d) (pointedProjection.obj K) (pointedProjection.obj L) =
      (ActionAssociator.originalIso d K L).hom ≫
        (tensorAction d).map (Functor.OplaxMonoidal.δ pointedProjection K L) := by
  let _ : (ActionAssociator.pointedAction d).Monoidal := ActionCoherence.pointedActionMonoidal d
  let _ : (ActionAssociator.pointedAction d).LaxMonoidal :=
    (ActionCoherence.pointedActionMonoidal d).toLaxMonoidal
  let _ : Localization.Lifting pointedProjection (weakEquivalences PointedSSet.{vC_ClosedAction})
      (ActionAssociator.pointedAction d) (tensorAction d) := ⟨Iso.refl _⟩
  have h := Localization.Monoidal.functorMonoidalOfComp_μ pointedProjection
    (weakEquivalences PointedSSet.{vC_ClosedAction}) (tensorAction d) (ActionAssociator.pointedAction d) K L
  change let _ := tensorActionMonoidal d
    Functor.LaxMonoidal.μ (tensorAction d) (pointedProjection.obj K) (pointedProjection.obj L) =
      (𝟙 ((tensorAction d).obj (pointedProjection.obj K)) ⊗ₘ
        𝟙 ((tensorAction d).obj (pointedProjection.obj L))) ≫
      (ActionAssociator.originalIso d K L).hom ≫ 𝟙 _ ≫
        (tensorAction d).map (Functor.OplaxMonoidal.δ pointedProjection K L) at h
  dsimp only at h ⊢
  simpa only [MonoidalCategory.id_tensorHom_id, Category.id_comp, Category.comp_id] using h

/-- The localized monoidal unit retains the original inverse frame-zero and Q word
followed by the actual scalar localization unit comparison. -/
theorem tensorActionMonoidal_unit :
    let _ : (ActionAssociator.pointedAction d).Monoidal := ActionCoherence.pointedActionMonoidal d
  let _ : (ActionAssociator.pointedAction d).LaxMonoidal :=
    (ActionCoherence.pointedActionMonoidal d).toLaxMonoidal
    let _ : Localization.Lifting pointedProjection (weakEquivalences PointedSSet.{vC_ClosedAction})
      (ActionAssociator.pointedAction d) (tensorAction d) := ⟨Iso.refl _⟩
    let _ := tensorActionMonoidal d
    Functor.LaxMonoidal.ε (tensorAction d) =
      Functor.LaxMonoidal.ε (ActionAssociator.pointedAction d) ≫
        (Localization.Lifting.iso pointedProjection (weakEquivalences PointedSSet.{vC_ClosedAction})
          (ActionAssociator.pointedAction d) (tensorAction d)).inv.app (𝟙_ PointedSSet.{vC_ClosedAction}) ≫
        (tensorAction d).map (Functor.OplaxMonoidal.η pointedProjection) := by
  let _ : (ActionAssociator.pointedAction d).Monoidal := ActionCoherence.pointedActionMonoidal d
  let _ : (ActionAssociator.pointedAction d).LaxMonoidal :=
    (ActionCoherence.pointedActionMonoidal d).toLaxMonoidal
  let _ : Localization.Lifting pointedProjection (weakEquivalences PointedSSet.{vC_ClosedAction})
      (ActionAssociator.pointedAction d) (tensorAction d) := ⟨Iso.refl _⟩
  exact Localization.Monoidal.functorMonoidalOfComp_ε pointedProjection
    (weakEquivalences PointedSSet.{vC_ClosedAction}) (tensorAction d) (ActionAssociator.pointedAction d)

/-- The native right action retains the actual scalar framing functor and its complete coherence. -/
@[instance_reducible]
def rightAction : MonoidalRightAction PointedSpaceHo.{vC_ClosedAction} (weakEquivalences C).Localization := by
  let _ : (tensorAction d).Monoidal := tensorActionMonoidal d
  exact MonoidalRightAction.actionOfMonoidalFunctorToEndofunctor (tensorAction d)

/-- The actual native action keeps every coefficient and scalar object of the original tensor. -/
theorem rightAction_obj (X : (weakEquivalences C).Localization) (K : PointedSpaceHo.{vC_ClosedAction}) :
    let _ := rightAction d
    X ⊙ᵣ K = ((tensorAction d).obj K).obj X := rfl

/-- Every original coefficient Ho arrow remains the same full framing tensor arrow. -/
theorem rightAction_coefficient {X Y : (weakEquivalences C).Localization} (f : X ⟶ Y)
    (K : PointedSpaceHo.{vC_ClosedAction}) :
    let _ := rightAction d
    f ⊵ᵣ K = ((tensorAction d).obj K).map f := rfl

/-- Every scalar Ho arrow, including formal inverses, keeps its original full tensor transformation. -/
theorem rightAction_scalar (X : (weakEquivalences C).Localization)
    {K L : PointedSpaceHo.{vC_ClosedAction}} (k : K ⟶ L) :
    let _ := rightAction d
    X ⊴ᵣ k = ((tensorAction d).map k).app X := rfl

/-- The right cotensor associator is the mate of the full actual tensorator under the same original adjunctions. -/
def cotensorAssociator (K L : PointedSpaceHo.{vC_ClosedAction}) :
    cotensorActionObj d (K ⊗ L) ≅ cotensorActionObj d L ⋙ cotensorActionObj d K := by
  let _ : (tensorAction d).Monoidal := tensorActionMonoidal d
  exact conjugateIsoEquiv (tensorActionAdjunction d (K ⊗ L))
    ((tensorActionAdjunction d K).comp (tensorActionAdjunction d L))
    (Functor.Monoidal.μIso (tensorAction d) K L)

/-- Both closure adjunctions and the genuine mapping HFC accompany the constructed native action. -/
structure ClosedAction where
  /-- The proved native coherent action. -/
  action : MonoidalRightAction PointedSpaceHo.{vC_ClosedAction} (weakEquivalences C).Localization
  /-- Its entire scalar functor is the actual original framing tensor. -/
  actionIso : let _ := action
    MonoidalRightAction.curriedAction PointedSpaceHo.{vC_ClosedAction} (weakEquivalences C).Localization ≅
      tensorAction d
  /-- Fixing a scalar gives the original complete tensor--cotensor adjunction. -/
  cotensorAdjunction : ∀ K : PointedSpaceHo.{vC_ClosedAction}, (tensorAction d).obj K ⊣ cotensorActionObj d K
  /-- Fixing a coefficient gives the original complete tensor--mapping-HFC adjunction. -/
  mappingAdjunction : ∀ X : (weakEquivalences C).Localization,
    (tensorAction d).flip.obj X ⊣ (mappingHo d).obj (Opposite.op X)

/-- Every actual pointed model's original two factories construct the full closed Ho(SSet*) action. -/
def closedAction : ClosedAction d := by
  let _ : (tensorAction d).Monoidal := tensorActionMonoidal d
  exact
    { action := rightAction d
      actionIso := MonoidalRightAction.curriedActionActionOfMonoidalFunctorToEndofunctorIso (tensorAction d)
      cotensorAdjunction := tensorActionAdjunction d
      mappingAdjunction := closedAdjunction d }

/-- The full native closed action is constructed from any original pair of functorial factors,
without generation, enrichment or a monoidal structure on the coefficient model. -/
def closedActionOfFactors
    (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C)) :
    ClosedAction (GeneratedFunctorialReplacements.replacementsOfFactors Fc Ff) :=
  closedAction (GeneratedFunctorialReplacements.replacementsOfFactors Fc Ff)

end HomotopicalAlgebra.PointedFramingAction

end PointedActionPromotionClosedAction
