/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeRestrictionCohomologyMaps

/-!
# Normalized native scalar composition and degree-zero identifications

These are intermediate native functor identifications, fixed on EVERY
original module, section and adjunction unit. They provide no higher
comparison, bundle, filtration or connection.

Source: native Mathlib adjunction, scalar restriction and cochain single
functors, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeScalarCompositionSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open RingedDerivedCoefficientOperations NativeFilteredDeRhamOutputs

attribute [local instance] HasDerivedCategory.standard

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [UnivLE.{max u v, 1}] [HasSheafify J AddCommGrpCat.{1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{1}]
  (R₀ R₁ R₂ : Sheaf J CommRingCat.{1}) (a : R₀ ⟶ R₁) (b : R₁ ⟶ R₂)
  [(pushforward (𝟭 C) R₀ R₁ a).IsRightAdjoint]
  [(pushforward (𝟭 C) R₁ R₂ b).IsRightAdjoint]
  [(pushforward (𝟭 C) R₀ R₂ (a ≫ b)).IsRightAdjoint]

/-- Direct and two-step native scalar extension, on all original adjunction units. -/
structure CompositionSource where
  iso : pullback (𝟭 C) R₀ R₂ (a ≫ b) ≅
    pullback (𝟭 C) R₀ R₁ a ⋙ pullback (𝟭 C) R₁ R₂ b
  units : ∀ (M : Modules R₀) (U : Cᵒᵖ) (m : M.val.obj U),
    ((iso.hom.app M).val.app U).hom
      ((((adjunction (𝟭 C) R₀ R₂ (a ≫ b)).unit.app M).val.app U).hom m) =
    (((adjunction (𝟭 C) R₁ R₂ b).unit.app ((pullback (𝟭 C) R₀ R₁ a).obj M)).val.app U).hom
      ((((adjunction (𝟭 C) R₀ R₁ a).unit.app M).val.app U).hom m)

variable (R O : Sheaf J CommRingCat.{1}) (eta : R ⟶ O)

/-- Identity scalar restriction, retaining the literal original section. -/
structure IdentityRestrictionSource where
  iso : 𝟭 (Modules O) ≅ restrict O O (𝟙 O)
  sections : ∀ (M : Modules O) (U : Cᵒᵖ) (m : M.val.obj U),
    ((iso.hom.app M).val.app U).hom m = m

def single (M : Modules O) : CochainComplex.Plus (Modules O) :=
  ⟨(CochainComplex.singleFunctor (Modules O) 0).obj M, ⟨0, by infer_instance⟩⟩

/-- The actual native bounded-below lift of the original full-derived single/cochain factor. -/
def singleDerivedIso (M : Modules O) :
    DerivedCategory.Plus.Q.obj (single O M) ≅ (DerivedCategory.Plus.singleFunctor (Modules O) 0).obj M :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((DerivedCategory.Plus.QCompιIso (Modules O)).app (single O M) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (Modules O) 0).app M).symm ≪≫
      ((DerivedCategory.Plus.singleFunctorιIso (Modules O) 0).app M).symm)

local instance restrictionAdditive : (restrict R O eta).Additive := by
  unfold restrict
  infer_instance

/-- Native scalar restriction commutes with the actual degree-zero cochain; its map is fixed
on every original degree-zero section, with all other terms native zero objects. -/
structure SingleRestrictionSource where
  iso : ∀ M : Modules O,
    (restrict R O eta).mapCochainComplexPlus.obj (single O M) ≅
      single R ((restrict R O eta).obj M)
  zero_source : ∀ (M : Modules O) (U : Cᵒᵖ) (m : M.val.obj U),
    (((iso M).hom.hom.f 0).val.app U).hom
      (show ((((restrict R O eta).mapCochainComplexPlus.obj (single O M)).obj.X 0).val.obj U) from m) =
    (show (((single R ((restrict R O eta).obj M)).obj.X 0).val.obj U) from m)

end MathlibExt.CategoryTheory.NativeScalarCompositionSources
