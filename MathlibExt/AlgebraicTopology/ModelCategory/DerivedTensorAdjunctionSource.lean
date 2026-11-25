/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorHom
public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedFunctorCoherence
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoHom

/-!
# The full original Hom functions for the chosen derived tensor adjunction

These bijections use the actual Q tensor source, R target, ordinary Quillen
Hom functions and both original projection comparisons. All three original
variables are retained. Parameter naturality of the ordinary Hom function
is proved from actual cofibrant/fibrant representatives and original currying.

Source: Hovey, *Model Categories*, Proposition 4.3.1.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory MorphismProperty Functor Opposite
open scoped MonoidalCategory MonoidalClosed

namespace HomotopicalAlgebra.DerivedTensorAdjunctionSource

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]

local notation "Ho" => MorphismProperty.Localization (weakEquivalences C)
local notation "π" => MorphismProperty.Q (weakEquivalences C)

open DerivedTensorConstructions

/-- The complete original Q counit becomes a natural projection isomorphism. -/
def qProjectionIso (d : GeneratedFunctorialReplacements.Data (C := C)) : d.Q ⋙ π ≅ π := by
  let _ : IsIso (whiskerRight d.q π) := DerivedFunctorCoherence.qLocalized_isIso d
  exact asIso (whiskerRight d.q π) ≪≫ (π).leftUnitor

/-- The complete original R unit becomes the same actual natural projection isomorphism. -/
def rProjectionIso (d : GeneratedFunctorialReplacements.Data (C := C)) : π ≅ d.R ⋙ π := by
  let _ : IsIso (whiskerRight d.r π) := DerivedFunctorCoherence.rLocalized_isIso d
  exact (π).leftUnitor.symm ≪≫ asIso (whiskerRight d.r π)

/-- The full original ordinary-Ho tensor-Hom function is natural in the original cofibrant tensor
parameter. -/
theorem ordinaryHom_parameter {A A' : C} (f : A ⟶ A') [IsCofibrant A] [IsCofibrant A']
    (B : C) [IsCofibrant B] (Z : C) [IsFibrant Z]
    (g : (π).obj (A' ⊗ B) ⟶ (π).obj Z) :
    letI : (ihom.adjunction A).IsQuillenAdjunction :=
      (IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom
          (C := C)).ihomAdjunction_isQuillenAdjunction A
    letI : (ihom.adjunction A').IsQuillenAdjunction :=
      (IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom
          (C := C)).ihomAdjunction_isQuillenAdjunction A'
    QuillenOrdinaryHoHom.homEquiv (ihom.adjunction A) B Z ((π).map (f ▷ B) ≫ g) =
      QuillenOrdinaryHoHom.homEquiv (ihom.adjunction A') B Z g ≫
        (π).map ((MonoidalClosed.pre f).app Z) := by
  let pp := IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom (C := C)
  let _ : (ihom.adjunction A).IsQuillenAdjunction := pp.ihomAdjunction_isQuillenAdjunction A
  let _ : (ihom.adjunction A').IsQuillenAdjunction := pp.ihomAdjunction_isQuillenAdjunction A'
  let _ : IsCofibrant (A' ⊗ B) := pp.isCofibrant_tensorObj A' B
  obtain ⟨h, hh⟩ := map_surjective_of_isLocalization π (A' ⊗ B) Z g
  rw [← hh, ← (π).map_comp, QuillenOrdinaryHoHom.homEquiv_map, QuillenOrdinaryHoHom.homEquiv_map]
  change (π).map (MonoidalClosed.curry ((f ▷ B) ≫ h)) =
    (π).map (MonoidalClosed.curry h) ≫ (π).map ((MonoidalClosed.pre f).app Z)
  rw [← (π).map_comp, MonoidalClosed.curry_pre_app]

/-- The original tensor-Hom bijection is evaluated on the exact same chosen Q sources and R target.
-/
def originalHomEquiv (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y Z : C) :
    ((π).obj (d.Q.obj X ⊗ d.Q.obj Y) ⟶ (π).obj (d.R.obj Z)) ≃
      ((π).obj (d.Q.obj Y) ⟶ (π).obj ((ihom (d.Q.obj X)).obj (d.R.obj Z))) := by
  let _ : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let _ : IsCofibrant (d.Q.obj Y) := d.q_cofibrant Y
  let _ : IsFibrant (d.R.obj Z) := d.r_fibrant Z
  let _ : (ihom.adjunction (d.Q.obj X)).IsQuillenAdjunction :=
    (IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom
        (C := C)).ihomAdjunction_isQuillenAdjunction _
  exact QuillenOrdinaryHoHom.homEquiv (ihom.adjunction (d.Q.obj X)) (d.Q.obj Y) (d.R.obj Z)

/-- The full represented derived Hom equivalence is constructed from both
original replacements and original Hom functions. -/
def representedHomEquiv (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y Z : C) :
    (((tensor d).obj ((π).obj X)).obj ((π).obj Y) ⟶ (π).obj Z) ≃
      ((π).obj Y ⟶ ((derivedInternalHom d).obj (op ((π).obj X))).obj ((π).obj Z)) :=
  ((Iso.homCongr (comparison d X Y) ((rProjectionIso d).app Z)).trans
    (originalHomEquiv d X Y Z)).trans
      (Iso.homCongr ((qProjectionIso d).app Y) (homComparison d X Z).symm)

/-- The actual forward function retains both Q/R projection maps and the complete original ordinary
adjunct. -/
theorem representedHomEquiv_apply (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y Z : C)
    (f : ((tensor d).obj ((π).obj X)).obj ((π).obj Y) ⟶ (π).obj Z) :
    representedHomEquiv d X Y Z f =
      (qProjectionIso d).inv.app Y ≫
        originalHomEquiv d X Y Z ((comparison d X Y).inv ≫ f ≫ (rProjectionIso d).hom.app Z) ≫
        (homComparison d X Z).inv := rfl

/-- The original Q/R ordinary adjunct retains every original second-variable map. -/
theorem originalHomEquiv_source (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C)
    {Y Y' : C} (f : Y ⟶ Y') (Z : C)
    (g : (π).obj (d.Q.obj X ⊗ d.Q.obj Y') ⟶ (π).obj (d.R.obj Z)) :
    originalHomEquiv d X Y Z ((π).map (d.Q.obj X ◁ d.Q.map f) ≫ g) =
      (π).map (d.Q.map f) ≫ originalHomEquiv d X Y' Z g := by
  let _ : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let _ : IsCofibrant (d.Q.obj Y) := d.q_cofibrant Y
  let _ : IsCofibrant (d.Q.obj Y') := d.q_cofibrant Y'
  let _ : IsFibrant (d.R.obj Z) := d.r_fibrant Z
  let _ : (ihom.adjunction (d.Q.obj X)).IsQuillenAdjunction :=
    (IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom
        (C := C)).ihomAdjunction_isQuillenAdjunction _
  exact QuillenOrdinaryHoHom.homEquiv_naturality_left (ihom.adjunction (d.Q.obj X)) (d.R.obj Z)
      (d.Q.map f) g

/-- The original ordinary adjunct retains every original fibrant target map. -/
theorem originalHomEquiv_target (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y : C)
    {Z Z' : C} (f : Z ⟶ Z') (g : (π).obj (d.Q.obj X ⊗ d.Q.obj Y) ⟶ (π).obj (d.R.obj Z)) :
    originalHomEquiv d X Y Z' (g ≫ (π).map (d.R.map f)) =
      originalHomEquiv d X Y Z g ≫ (π).map ((ihom (d.Q.obj X)).map (d.R.map f)) := by
  let _ : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let _ : IsCofibrant (d.Q.obj Y) := d.q_cofibrant Y
  let _ : IsFibrant (d.R.obj Z) := d.r_fibrant Z
  let _ : IsFibrant (d.R.obj Z') := d.r_fibrant Z'
  let _ : (ihom.adjunction (d.Q.obj X)).IsQuillenAdjunction :=
    (IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom
        (C := C)).ihomAdjunction_isQuillenAdjunction _
  exact QuillenOrdinaryHoHom.homEquiv_naturality_right (ihom.adjunction (d.Q.obj X)) (d.Q.obj Y) g
      (d.R.map f)

/-- The exact original ordinary parameter naturality holds for every original Q-source map. -/
theorem originalHomEquiv_parameter (d : GeneratedFunctorialReplacements.Data (C := C))
    {X X' : C} (f : X ⟶ X') (Y Z : C)
    (g : (π).obj (d.Q.obj X' ⊗ d.Q.obj Y) ⟶ (π).obj (d.R.obj Z)) :
    originalHomEquiv d X Y Z ((π).map (d.Q.map f ▷ d.Q.obj Y) ≫ g) =
      originalHomEquiv d X' Y Z g ≫ (π).map ((MonoidalClosed.pre (d.Q.map f)).app (d.R.obj Z)) := by
  let _ : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let _ : IsCofibrant (d.Q.obj X') := d.q_cofibrant X'
  let _ : IsCofibrant (d.Q.obj Y) := d.q_cofibrant Y
  let _ : IsFibrant (d.R.obj Z) := d.r_fibrant Z
  exact ordinaryHom_parameter (d.Q.map f) (d.Q.obj Y) (d.R.obj Z) g

/-- The complete represented derived Hom function is natural in every original second-variable
arrow. -/
theorem representedHomEquiv_source (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C)
    {Y Y' : C} (f : Y ⟶ Y') (Z : C)
    (g : ((tensor d).obj ((π).obj X)).obj ((π).obj Y') ⟶ (π).obj Z) :
    representedHomEquiv d X Y Z (((tensor d).obj ((π).obj X)).map ((π).map f) ≫ g) =
      (π).map f ≫ representedHomEquiv d X Y' Z g := by
  have hArg : (comparison d X Y).inv ≫
      (((tensor d).obj ((π).obj X)).map ((π).map f) ≫ g) ≫ (rProjectionIso d).hom.app Z =
      (π).map (d.Q.obj X ◁ d.Q.map f) ≫
        ((comparison d X Y').inv ≫ g ≫ (rProjectionIso d).hom.app Z) := by
    simp only [Category.assoc]
    rw [reassoc_of% (comparison_inv_naturality_right d X f).symm]
  have hQ : (qProjectionIso d).inv.app Y ≫ (π).map (d.Q.map f) =
      (π).map f ≫ (qProjectionIso d).inv.app Y' :=
    ((qProjectionIso d).inv.naturality f).symm
  rw [representedHomEquiv_apply, representedHomEquiv_apply, hArg, originalHomEquiv_source]
  simp only [Category.assoc]
  rw [reassoc_of% hQ]

/-- The complete represented derived Hom function is natural in every original target arrow. -/
theorem representedHomEquiv_target (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y : C)
    {Z Z' : C} (f : Z ⟶ Z') (g : ((tensor d).obj ((π).obj X)).obj ((π).obj Y) ⟶ (π).obj Z) :
    representedHomEquiv d X Y Z' (g ≫ (π).map f) =
      representedHomEquiv d X Y Z g ≫ ((derivedInternalHom d).obj (op ((π).obj X))).map ((π).map f)
          := by
  have hR : (π).map f ≫ (rProjectionIso d).hom.app Z' =
      (rProjectionIso d).hom.app Z ≫ (π).map (d.R.map f) :=
    (rProjectionIso d).hom.naturality f
  have hArg : (comparison d X Y).inv ≫ (g ≫ (π).map f) ≫ (rProjectionIso d).hom.app Z' =
      ((comparison d X Y).inv ≫ g ≫ (rProjectionIso d).hom.app Z) ≫ (π).map (d.R.map f) := by
    simp only [Category.assoc]
    rw [hR]
  have hHom : (π).map ((ihom (d.Q.obj X)).map (d.R.map f)) ≫ (homComparison d X Z').inv =
      (homComparison d X Z).inv ≫ ((derivedInternalHom d).obj (op ((π).obj X))).map ((π).map f) :=
    ((homProjectionIso d).inv.app (op X)).naturality f
  rw [representedHomEquiv_apply, representedHomEquiv_apply, hArg, originalHomEquiv_target]
  simp only [Category.assoc]
  rw [hHom]

/-- The full represented derived Hom function is natural in every original tensor-parameter arrow.
-/
theorem representedHomEquiv_parameter (d : GeneratedFunctorialReplacements.Data (C := C))
    {X X' : C} (f : X ⟶ X') (Y Z : C)
    (g : ((tensor d).obj ((π).obj X')).obj ((π).obj Y) ⟶ (π).obj Z) :
    representedHomEquiv d X Y Z (((tensor d).map ((π).map f)).app ((π).obj Y) ≫ g) =
      representedHomEquiv d X' Y Z g ≫ ((derivedInternalHom d).map ((π).map f).op).app ((π).obj Z)
          := by
  have hArg : (comparison d X Y).inv ≫
      (((tensor d).map ((π).map f)).app ((π).obj Y) ≫ g) ≫ (rProjectionIso d).hom.app Z =
      (π).map (d.Q.map f ▷ d.Q.obj Y) ≫
        ((comparison d X' Y).inv ≫ g ≫ (rProjectionIso d).hom.app Z) := by
    simp only [Category.assoc]
    rw [reassoc_of% (comparison_inv_naturality_left d f Y).symm]
  have hHom : (π).map ((MonoidalClosed.pre (d.Q.map f)).app (d.R.obj Z)) ≫
      (homComparison d X Z).inv =
      (homComparison d X' Z).inv ≫ ((derivedInternalHom d).map ((π).map f).op).app ((π).obj Z) :=
    congrArg (fun t => t.app Z) ((homProjectionIso d).inv.naturality f.op)
  rw [representedHomEquiv_apply, representedHomEquiv_apply, hArg, originalHomEquiv_parameter]
  simp only [Category.assoc]
  rw [hHom]

end HomotopicalAlgebra.DerivedTensorAdjunctionSource
