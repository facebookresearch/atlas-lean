/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.OriginalRankMonoidal
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.DerivedAmbientAction
import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorBraidingCoherence

/-!
# The actual closed symmetric derived balanced module tensor

The original fixed-rank free-module transfer earns its balanced monoidal
model and regular module unit. The exact original Q/R factory therefore
derives that same tensor and internal Hom on the original module localization.
The qualified full derived pentagon, units, two hexagons, symmetry and Hom
adjunction are instantiated on this actual module category.

The unit is the actual regular module. This construction does not require
cofibrancy of the diagonal regular bimodule over A tensor A-opposite.
-/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v wA

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty HomotopicalAlgebra Opposite
open scoped MonoidalCategory MonoidalClosed CategoryTheory.MonObj

namespace HomotopicalAlgebra.ModuleTransfer.DerivedCommutativeTensor

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C] [IsCofibrant (𝟙_ C)]
  (A : CommMon C) {I J : MorphismProperty C}
  {κA : Cardinal.{wA}} [Fact κA.IsRegular] [OrderBot κA.ord.ToType]
  (t : RightTransfer.OriginalRankModelTransfer (Mod.free A.X) (Mod.forget (D := C) A.X) I J κA)

/-- The balanced tensor monoidal structure on modules over the original commutative scalar. -/
local instance moduleMonoidal : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
/-- The symmetry of the same balanced tensor over the original commutative scalar. -/
local instance moduleSymmetric : SymmetricCategory (Mod C A.X) := Mod.instSymmetricCategory A
/-- The chosen internal Hom right adjoints for the original balanced module tensor. -/
local instance moduleClosed : MonoidalClosed (Mod C A.X) := Mod.instMonoidalClosed A

local notation "M" => Mod C A.X
local notation "qA" => t.replacements
local notation "HA" => MorphismProperty.Localization (DerivedAmbientAction.moduleWeak t)
local notation "πA" => MorphismProperty.Q (DerivedAmbientAction.moduleWeak t)
local notation "H" => DerivedTensorConstructions.MonoidalHo (qA)

/-- The earned original module monoidal model and the complete closed symmetric derived structure. -/
structure DerivedData where
  /-- The original source-rank module model is monoidal for the original balanced tensor. -/
  moduleModel : letI : ModelCategory M := t.model
    IsClosedSymmetricMonoidalModelCategory M
  /-- The original module localization has its complete actual derived internal Hom. -/
  closed : letI : ModelCategory M := t.model
    letI : IsClosedSymmetricMonoidalModelCategory M := moduleModel
    MonoidalClosed H
  /-- The original module localization has the full actual derived symmetric tensor structure. -/
  symmetric : letI : ModelCategory M := t.model
    letI : IsClosedSymmetricMonoidalModelCategory M := moduleModel
    SymmetricCategory H

variable (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)

/-- The actual original transfer constructs the full derived closed symmetric module category. -/
def construct : DerivedData A t := by
  let : ModelCategory M := t.model
  let h := OriginalRankMonoidal.monoidalModel A t hI hJ
  let : IsClosedSymmetricMonoidalModelCategory M := h
  exact
    { moduleModel := h
      closed := DerivedTensorConstructions.MonoidalHo.monoidalClosed (qA)
      symmetric := DerivedTensorConstructions.MonoidalHo.symmetricCategory (qA) }

/-- The constructed closed record is exactly the complete original Q/R derived closed record. -/
theorem construct_closed :
    letI : ModelCategory M := t.model
    letI : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
    (construct A t hI hJ).closed = DerivedTensorConstructions.MonoidalHo.monoidalClosed (qA) := rfl

/-- The constructed symmetric record is exactly the original derived braid with both full hexagons and involution. -/
theorem construct_symmetric :
    letI : ModelCategory M := t.model
    letI : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
    (construct A t hI hJ).symmetric = DerivedTensorConstructions.MonoidalHo.symmetricCategory (qA) := rfl

/-- The derived relative tensor is the exact chosen QQ functor of the original balanced module tensor. -/
def tensor : HA ⥤ HA ⥤ HA := by
  let : ModelCategory M := t.model
  let : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
  exact DerivedTensorConstructions.tensor (qA)

/-- The derived relative internal Hom is the exact chosen Hom(Q-,R-) of the original balanced closed module category. -/
def internalHom : HAᵒᵖ ⥤ HA ⥤ HA := by
  let : ModelCategory M := t.model
  let : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
  exact DerivedTensorConstructions.derivedInternalHom (qA)

/-- Every actual original source pair retains the balanced tensor of both original Q objects. -/
def originalTensorComparison (N N' : M) :
    letI : ModelCategory M := t.model
    ((tensor A t hI hJ).obj ((πA).obj N)).obj ((πA).obj N') ≅
      (πA).obj ((qA).Q.obj N ⊗ (qA).Q.obj N') := by
  let : ModelCategory M := t.model
  let : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
  exact DerivedTensorConstructions.comparison (qA) N N'

/-- The original ordinary balanced tensor computes the actual derived tensor at both original cofibrant endpoints. -/
def cofibrantTensorComparison (N N' : M) :
    letI : ModelCategory M := t.model
    ∀ [_hN : IsCofibrant N] [_hN' : IsCofibrant N'],
      ((tensor A t hI hJ).obj ((πA).obj N)).obj ((πA).obj N') ≅ (πA).obj (N ⊗ N') := by
  let : ModelCategory M := t.model
  let : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
  intro hN hN'
  exact DerivedTensorConstructions.cofibrantComparison (qA) N N'

/-- Every original source Hom calculation retains the actual module Q-source and R-target. -/
def originalHomComparison (N N' : M) :
    letI : ModelCategory M := t.model
    ((internalHom A t hI hJ).obj (op ((πA).obj N))).obj ((πA).obj N') ≅
      (πA).obj ((ihom ((qA).Q.obj N)).obj ((qA).R.obj N')) := by
  let : ModelCategory M := t.model
  let : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
  exact DerivedTensorConstructions.homComparison (qA) N N'

/-- The same original internal Hom computes the derived module Hom at cofibrant/fibrant endpoints. -/
def cofibrantFibrantHomComparison (N N' : M) :
    letI : ModelCategory M := t.model
    ∀ [_hN : IsCofibrant N] [_hN' : IsFibrant N'],
      ((internalHom A t hI hJ).obj (op ((πA).obj N))).obj ((πA).obj N') ≅
        (πA).obj ((ihom N).obj N') := by
  let : ModelCategory M := t.model
  let : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
  intro hN hN'
  exact DerivedTensorConstructions.cofibrantFibrantHomComparison (qA) N N'

/-- The complete actual two-variable balanced derived tensor-Hom adjunction retains all homotopy arrows. -/
def parametrizedAdjunction : tensor A t hI hJ ⊣₂ internalHom A t hI hJ := by
  let : ModelCategory M := t.model
  let : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
  exact DerivedTensorAdjunction.parametrizedAdjunction (qA)

/-- Every actual homotopy module has the original chosen full tensor-Hom adjunction. -/
def adjunction (N : HA) : (tensor A t hI hJ).obj N ⊣ (internalHom A t hI hJ).obj (op N) := by
  let : ModelCategory M := t.model
  let : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
  exact DerivedTensorAdjunction.adjunction (qA) N

/-- Every derived module Hom function is the same original full Q/R Hom function. -/
theorem adjunction_homEquiv (N P Z : HA) (f : ((tensor A t hI hJ).obj N).obj P ⟶ Z) :
    letI : ModelCategory M := t.model
    letI : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
    (adjunction A t hI hJ N).homEquiv P Z f = DerivedTensorAdjunction.homEquiv (qA) N P Z f := by
  let : ModelCategory M := t.model
  let : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
  exact DerivedTensorAdjunction.adjunction_homEquiv (qA) N P Z f

/-- The full actual balanced derived adjunction retains its complete left unit/counit triangle. -/
theorem left_triangle (N P : HA) :
    ((tensor A t hI hJ).obj N).map ((adjunction A t hI hJ N).unit.app P) ≫
      (adjunction A t hI hJ N).counit.app (((tensor A t hI hJ).obj N).obj P) = 𝟙 _ :=
  (adjunction A t hI hJ N).left_triangle_components P

/-- The same original balanced derived adjunction retains its complete right unit/counit triangle. -/
theorem right_triangle (N Z : HA) :
    (adjunction A t hI hJ N).unit.app (((internalHom A t hI hJ).obj (op N)).obj Z) ≫
      ((internalHom A t hI hJ).obj (op N)).map ((adjunction A t hI hJ N).counit.app Z) = 𝟙 _ :=
  (adjunction A t hI hJ N).right_triangle_components Z

/-- The complete derived unit is the projection of the actual original regular module. -/
theorem unit_object :
    letI : ModelCategory M := t.model
    letI : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
    𝟙_ H = (πA).obj (Mod.regular A.X) := rfl

/-- Every original cofibrant source morphism retains the complete balanced tensor computation. -/
@[reassoc]
theorem cofibrantTensorComparison_naturality_left {N N' : M} (f : N ⟶ N') (P : M) :
    letI : ModelCategory M := t.model
    ∀ [_hN : IsCofibrant N] [_hN' : IsCofibrant N'] [_hP : IsCofibrant P],
      ((tensor A t hI hJ).map ((πA).map f)).app ((πA).obj P) ≫
          (cofibrantTensorComparison A t hI hJ N' P).hom =
        (cofibrantTensorComparison A t hI hJ N P).hom ≫ (πA).map (f ▷ P) := by
  let : ModelCategory M := t.model
  let : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
  intro hN hN' hP
  exact DerivedTensorConstructions.cofibrantComparison_naturality_left (qA) f P

/-- Every original second-variable morphism retains the same actual balanced tensor computation. -/
@[reassoc]
theorem cofibrantTensorComparison_naturality_right (N : M) {P P' : M} (f : P ⟶ P') :
    letI : ModelCategory M := t.model
    ∀ [_hN : IsCofibrant N] [_hP : IsCofibrant P] [_hP' : IsCofibrant P'],
      ((tensor A t hI hJ).obj ((πA).obj N)).map ((πA).map f) ≫
          (cofibrantTensorComparison A t hI hJ N P').hom =
        (cofibrantTensorComparison A t hI hJ N P).hom ≫ (πA).map (N ◁ f) := by
  let : ModelCategory M := t.model
  let : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
  intro hN hP hP'
  exact DerivedTensorConstructions.cofibrantComparison_naturality_right (qA) N f

/-- The full source Hom comparison retains every original contravariant module map. -/
@[reassoc]
theorem originalHomComparison_naturality_source {N N' : M} (f : N ⟶ N') (P : M) :
    letI : ModelCategory M := t.model
    ((internalHom A t hI hJ).map ((πA).map f).op).app ((πA).obj P) ≫
        (originalHomComparison A t hI hJ N P).hom =
      (originalHomComparison A t hI hJ N' P).hom ≫
        (πA).map ((MonoidalClosed.pre ((qA).Q.map f)).app ((qA).R.obj P)) := by
  let : ModelCategory M := t.model
  let : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
  exact DerivedTensorConstructions.homComparison_naturality_source (qA) f P

/-- The full source Hom comparison retains every original covariant target module map. -/
@[reassoc]
theorem originalHomComparison_naturality_target (N : M) {P P' : M} (f : P ⟶ P') :
    letI : ModelCategory M := t.model
    ((internalHom A t hI hJ).obj (op ((πA).obj N))).map ((πA).map f) ≫
        (originalHomComparison A t hI hJ N P').hom =
      (originalHomComparison A t hI hJ N P).hom ≫
        (πA).map ((ihom ((qA).Q.obj N)).map ((qA).R.map f)) := by
  let : ModelCategory M := t.model
  let : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
  exact DerivedTensorConstructions.homComparison_naturality_target (qA) N f

/-- The actual derived symmetry is the original balanced symmetry between the complete source computations. -/
theorem braiding_cofibrant (N P : M) :
    letI : ModelCategory M := t.model
    letI : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
    ∀ [_hN : IsCofibrant N] [_hP : IsCofibrant P],
      ((DerivedTensorConstructions.derivedBraiding (qA)).hom.app ((πA).obj N)).app ((πA).obj P) =
        (cofibrantTensorComparison A t hI hJ N P).hom ≫ (πA).map (β_ N P).hom ≫
          (cofibrantTensorComparison A t hI hJ P N).inv := by
  let : ModelCategory M := t.model
  let : IsClosedSymmetricMonoidalModelCategory M := (construct A t hI hJ).moduleModel
  intro hN hP
  exact DerivedTensorConstructions.MonoidalHo.braidingNatIso_hom_app (qA) N P

end HomotopicalAlgebra.ModuleTransfer.DerivedCommutativeTensor
