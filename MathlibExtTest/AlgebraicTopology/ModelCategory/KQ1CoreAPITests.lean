/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence
public import MathlibExt.AlgebraicTopology.ModelCategory.Replacement
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject

@[expose] public section

/-!
# KQ1 core API consumer tests

Compact compile-time consumer checks for the KQ1 categorical and small-object
layer: identity Quillen adjunctions and equivalences with right-adjoint and
(co)fibrant-object preservation, functorial (co)fibrant replacement with its
natural maps and factorization identities, and boundary and horn small-object
factorizations with composition and factor properties.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Adjunction HomotopicalAlgebra MorphismProperty
  Limits

open scoped SSet.modelCategoryQuillen

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.KQ1CoreAPITests

universe v₁ v₂ v₃ u₁ u₂ u₃

section QuillenIdentity

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
variable {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
variable {L : C ⥤ D} {R : D ⥤ C} {adj : L ⊣ R}
variable {E : Type u₃} [Category.{v₃} E] [ModelCategory E]
variable {L' : D ⥤ E} {R' : E ⥤ D} {adj' : L' ⊣ R'}

example : IsQuillenAdjunction (Adjunction.id (C := C)) :=
  inferInstance

example : IsQuillenEquivalence (Adjunction.id (C := C)) :=
  inferInstance

example [IsQuillenAdjunction adj] :
    PreservesFibrations (C := D) (D := C) R :=
  IsQuillenAdjunction.preservesFibrations (adj := adj)

example [IsQuillenAdjunction adj] :
    PreservesTrivialFibrations (C := D) (D := C) R :=
  IsQuillenAdjunction.preservesTrivialFibrations (adj := adj)

example [IsQuillenAdjunction adj] :
    PreservesCofibrantObjects (C := C) (D := D) L :=
  IsQuillenAdjunction.preservesCofibrantObjects (adj := adj)

example [IsQuillenAdjunction adj] :
    PreservesFibrantObjects (C := D) (D := C) R :=
  IsQuillenAdjunction.preservesFibrantObjects (adj := adj)

example :
    IsQuillenAdjunction adj ↔
      PreservesFibrations (C := D) (D := C) R ∧
        PreservesTrivialFibrations (C := D) (D := C) R :=
  IsQuillenAdjunction.isQuillenAdjunction_iff (adj := adj)

example [h : IsQuillenAdjunction adj] :
    PreservesCofibrations (C := C) (D := D) L :=
  h.preservesCofibrations

example [h : IsQuillenAdjunction adj] :
    PreservesTrivialCofibrations (C := C) (D := D) L :=
  h.preservesTrivialCofibrations

example [IsQuillenAdjunction adj] [IsQuillenAdjunction adj'] :
    IsQuillenAdjunction (adj.comp adj') :=
  inferInstance

example [IsQuillenEquivalence adj] [IsQuillenEquivalence adj'] :
    IsQuillenEquivalence (adj.comp adj') :=
  inferInstance

example [IsQuillenEquivalence adj] {X : C} [IsCofibrant X] {Y : D}
    [IsFibrant Y] (f : L.obj X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence (adj.homEquiv X Y f) :=
  IsQuillenEquivalence.weakEquivalence_homEquiv_iff (adj := adj) f

example [IsQuillenEquivalence adj] (X : C) [IsCofibrant X]
    [IsFibrant (L.obj X)] : WeakEquivalence (adj.unit.app X) :=
  IsQuillenEquivalence.weakEquivalence_unit (adj := adj) X

example [IsQuillenEquivalence adj] (Y : D) [IsCofibrant (R.obj Y)]
    [IsFibrant Y] : WeakEquivalence (adj.counit.app Y) :=
  IsQuillenEquivalence.weakEquivalence_counit (adj := adj) Y

end QuillenIdentity

section CofibrantReplacementClient

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]

example (X : C) : IsCofibrant ((cofibrantReplacement (C := C)).obj X) :=
  inferInstance

example (X : C) : Cofibration (initialToCofibrantReplacement (C := C) X) :=
  inferInstance

example (X : C) : Fibration ((cofibrantReplacementCounit (C := C)).app X) :=
  inferInstance

example (X : C) :
    WeakEquivalence ((cofibrantReplacementCounit (C := C)).app X) :=
  inferInstance

theorem cofibrantReplacement_fac_client (X : C) :
    initialToCofibrantReplacement (C := C) X ≫
      (cofibrantReplacementCounit (C := C)).app X = initial.to X :=
  cofibrantReplacement_fac X

theorem cofibrantReplacementCounit_naturality_client {X Y : C} (f : X ⟶ Y) :
    (cofibrantReplacement (C := C)).map f ≫
        (cofibrantReplacementCounit (C := C)).app Y =
      (cofibrantReplacementCounit (C := C)).app X ≫ (𝟭 C).map f :=
  (cofibrantReplacementCounit (C := C)).naturality f

end CofibrantReplacementClient

section FibrantReplacementClient

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
variable [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

example (X : C) : IsFibrant ((fibrantReplacement (C := C)).obj X) :=
  inferInstance

example (X : C) : Cofibration ((fibrantReplacementUnit (C := C)).app X) :=
  inferInstance

example (X : C) :
    WeakEquivalence ((fibrantReplacementUnit (C := C)).app X) :=
  inferInstance

example (X : C) : Fibration (fibrantReplacementToTerminal (C := C) X) :=
  inferInstance

theorem fibrantReplacement_fac_client (X : C) :
    (fibrantReplacementUnit (C := C)).app X ≫
      fibrantReplacementToTerminal (C := C) X = terminal.from X :=
  fibrantReplacement_fac X

theorem fibrantReplacementUnit_naturality_client {X Y : C} (f : X ⟶ Y) :
    (𝟭 C).map f ≫ (fibrantReplacementUnit (C := C)).app Y =
      (fibrantReplacementUnit (C := C)).app X ≫
        (fibrantReplacement (C := C)).map f :=
  (fibrantReplacementUnit (C := C)).naturality f

end FibrantReplacementClient

section BoundaryFactorizationClient

example :
    HasFunctorialFactorization (MorphismProperty.monomorphisms SSet.{u₁})
      (MorphismProperty.monomorphisms SSet.{u₁}).rlp :=
  inferInstance

theorem mono_factorization_composition {X Y : SSet.{u₁}} (f : X ⟶ Y) :
    (SSet.modelCategoryQuillen.monoFactorizationData f).i ≫
      (SSet.modelCategoryQuillen.monoFactorizationData f).p = f :=
  (SSet.modelCategoryQuillen.monoFactorizationData f).fac

example {X Y : SSet.{u₁}} (f : X ⟶ Y) :
    Mono (SSet.modelCategoryQuillen.monoFactorizationData f).i :=
  inferInstance

theorem mono_factorization_right {X Y : SSet.{u₁}} (f : X ⟶ Y) :
    (MorphismProperty.monomorphisms SSet.{u₁}).rlp
      (SSet.modelCategoryQuillen.monoFactorizationData f).p :=
  (SSet.modelCategoryQuillen.monoFactorizationData f).hp

theorem mono_mapZ_comp {X Y X' Y' X'' Y'' : SSet.{u₁}} {f : X ⟶ Y}
    {g : X' ⟶ Y'} {h : X'' ⟶ Y''} (φ : Arrow.mk f ⟶ Arrow.mk g)
    (ψ : Arrow.mk g ⟶ Arrow.mk h) :
    SSet.modelCategoryQuillen.monoFunctorialFactorizationData.mapZ (φ ≫ ψ) =
      SSet.modelCategoryQuillen.monoFunctorialFactorizationData.mapZ φ ≫
        SSet.modelCategoryQuillen.monoFunctorialFactorizationData.mapZ ψ :=
  SSet.modelCategoryQuillen.monoFunctorialFactorizationData.mapZ_comp φ ψ

end BoundaryFactorizationClient

section HornFactorizationClient

example :
    HasFunctorialFactorization SSet.anodyneExtensions
      (HomotopicalAlgebra.fibrations SSet.{u₁}) :=
  inferInstance

theorem anodyne_factorization_composition {X Y : SSet.{u₁}} (f : X ⟶ Y) :
    (SSet.modelCategoryQuillen.anodyneFactorizationData f).i ≫
      (SSet.modelCategoryQuillen.anodyneFactorizationData f).p = f :=
  (SSet.modelCategoryQuillen.anodyneFactorizationData f).fac

theorem anodyne_factorization_left {X Y : SSet.{u₁}} (f : X ⟶ Y) :
    SSet.anodyneExtensions
      (SSet.modelCategoryQuillen.anodyneFactorizationData f).i :=
  SSet.modelCategoryQuillen.anodyneFactorizationData_mem_anodyne f

example {X Y : SSet.{u₁}} (f : X ⟶ Y) :
    Fibration (SSet.modelCategoryQuillen.anodyneFactorizationData f).p :=
  inferInstance

theorem anodyne_factorization_right {X Y : SSet.{u₁}} (f : X ⟶ Y) :
    HomotopicalAlgebra.fibrations SSet.{u₁}
      (SSet.modelCategoryQuillen.anodyneFactorizationData f).p :=
  (SSet.modelCategoryQuillen.anodyneFactorizationData f).hp

theorem anodyne_mapZ_comp {X Y X' Y' X'' Y'' : SSet.{u₁}} {f : X ⟶ Y}
    {g : X' ⟶ Y'} {h : X'' ⟶ Y''} (φ : Arrow.mk f ⟶ Arrow.mk g)
    (ψ : Arrow.mk g ⟶ Arrow.mk h) :
    SSet.modelCategoryQuillen.anodyneFunctorialFactorizationData.mapZ (φ ≫ ψ) =
      SSet.modelCategoryQuillen.anodyneFunctorialFactorizationData.mapZ φ ≫
        SSet.modelCategoryQuillen.anodyneFunctorialFactorizationData.mapZ ψ :=
  SSet.modelCategoryQuillen.anodyneFunctorialFactorizationData.mapZ_comp φ ψ

end HornFactorizationClient

end MathlibExtTest.AlgebraicTopology.ModelCategory.KQ1CoreAPITests
