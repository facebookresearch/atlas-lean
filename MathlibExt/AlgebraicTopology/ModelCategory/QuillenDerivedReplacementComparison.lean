/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedEquivalence

/-!
# Canonical derived comparisons at genuine cofibrant and fibrant objects

The actual derivability structures and Quillen Brown lemmas prove
invertibility of the two canonical comparisons on their native domains.
The original derived unit and counit equations extend to every actual
replacement arrow, retaining its complete adjoint transpose.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u₁ u₂ v₁ v₂
open CategoryTheory MorphismProperty

namespace HomotopicalAlgebra
variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [adj.IsQuillenAdjunction]

local notation "WC" => weakEquivalences C
local notation "WD" => weakEquivalences D
local notation "data" => quillenDerivedAdjunctionData adj

/-- Actual cofibrant derivability makes the SAME canonical left comparison invertible at a cofibrant
object. -/
theorem quillenDerived_leftComparison_isIso_of_isCofibrant (X : C) [IsCofibrant X] :
    IsIso ((data).leftComparison.app X) := by
  let Φ := CofibrantObject.localizerMorphism C
  have h : Φ.Derives (L ⋙ (WD).Q) := by
    intro A B f hf
    let _ : WeakEquivalence f.hom := by
      rw [← weakEquivalence_iff_of_objectProperty, weakEquivalence_iff]
      exact hf
    let _ : WeakEquivalence (L.map f.hom) :=
      Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := adj) f.hom
    apply Localization.inverts (WD).Q WD
    change weakEquivalences D (L.map f.hom)
    exact mem_weakEquivalences _
  let _ : (data).leftDerived.IsLeftDerivedFunctor (data).leftComparison WC := (data).leftIsDerived
  exact h.isIso' (data).leftComparison (CofibrantObject.mk X)

/-- Actual fibrant derivability makes the SAME canonical right comparison invertible at a fibrant
object. -/
theorem quillenDerived_rightComparison_isIso_of_isFibrant (Y : D) [IsFibrant Y] :
    IsIso ((data).rightComparison.app Y) := by
  let Φ := FibrantObject.localizerMorphism D
  have h : Φ.Derives (R ⋙ (WC).Q) := by
    intro A B f hf
    let _ : WeakEquivalence f.hom := by
      rw [← weakEquivalence_iff_of_objectProperty, weakEquivalence_iff]
      exact hf
    let _ : WeakEquivalence (R.map f.hom) :=
      Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) f.hom
    apply Localization.inverts (WC).Q WC
    change weakEquivalences C (R.map f.hom)
    exact mem_weakEquivalences _
  let _ : (data).rightDerived.IsRightDerivedFunctor (data).rightComparison WD :=
    (data).rightIsDerived
  exact h.isIso_of_isRightDerivedFunctor (data).rightComparison (FibrantObject.mk Y)

/-- The actual canonical derived unit retains every replacement arrow and its SAME original
transpose. -/
theorem quillenDerived_unit_replacement_fac (X : C) {Y : D} (f : L.obj X ⟶ Y) :
    (data).adjunction.unit.app ((WC).Q.obj X) ≫
      (data).rightDerived.map ((data).leftComparison.app X ≫ (WD).Q.map f) =
    (WC).Q.map (adj.homEquiv X Y f) ≫ (data).rightComparison.app Y := by
  have hn : (WC).Q.map (R.map f) ≫ (data).rightComparison.app Y =
      (data).rightComparison.app (L.obj X) ≫ (data).rightDerived.map ((WD).Q.map f) :=
    (data).rightComparison.naturality f
  rw [Functor.map_comp, ← Category.assoc, quillenDerived_unit_fac, Category.assoc, ← hn,
    ← Category.assoc, ← Functor.map_comp]
  rfl

/-- The SAME canonical derived counit retains every actual source arrow and its full original
adjoint mate. -/
theorem quillenDerived_counit_replacement_fac {X : C} (Y : D) (g : X ⟶ R.obj Y) :
    (data).leftDerived.map ((WC).Q.map g ≫ (data).rightComparison.app Y) ≫
      (data).adjunction.counit.app ((WD).Q.obj Y) =
    (data).leftComparison.app X ≫ (WD).Q.map ((adj.homEquiv X Y).symm g) := by
  have hn : (data).leftDerived.map ((WC).Q.map g) ≫ (data).leftComparison.app (R.obj Y) =
      (data).leftComparison.app X ≫ (WD).Q.map (L.map g) :=
    (data).leftComparison.naturality g
  rw [Functor.map_comp, Category.assoc, quillenDerived_counit_fac, ← Category.assoc, hn,
    Category.assoc, ← Functor.map_comp]
  rfl

end HomotopicalAlgebra
