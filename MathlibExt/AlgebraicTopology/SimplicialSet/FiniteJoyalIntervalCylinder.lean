/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalSimplices
public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorialCylinder
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The exact product cylinder of the finite Joyal interval

The accepted finite interval gives a native precylinder of the identity
endofunctor, with object `J ⊗ X`. Its boundary is monic, it preserves
monomorphisms and value-universe small colimits, and every endpoint
naturality square is a pullback. The pullback statement holds for all maps.

This is Cisinski's Example 2.4.10 applied to the two endpoints of the
finite interval. Exactness is independent of any model structure.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory HomotopicalAlgebra
open scoped Simplicial

universe u

namespace SSet.joyalInterval

/-- The accepted endpoint, with the native tensor unit as its domain. -/
noncomputable def unitPoint (ε : Fin 2) : (𝟙_ SSet.{u}) ⟶ joyalInterval :=
  (isTerminalTensorUnit.uniqueUpToIso stdSimplex.isTerminalObj₀.{u}).hom ≫ endpoint ε

/-- The endpoint transformation for the product with the finite interval. -/
noncomputable def productEndpoint (ε : Fin 2) :
    𝟭 SSet.{u} ⟶ tensorLeft joyalInterval where
  app X := lift (toUnit X ≫ unitPoint ε) (𝟙 X)
  naturality {X Y} f := by
    change f ≫ lift (toUnit Y ≫ unitPoint ε) (𝟙 Y) =
      lift (toUnit X ≫ unitPoint ε) (𝟙 X) ≫ joyalInterval ◁ f
    apply CartesianMonoidalCategory.hom_ext <;> simp

/-- The second projection of the product cylinder. -/
noncomputable def productProjection : tensorLeft joyalInterval.{u} ⟶ 𝟭 SSet where
  app X := snd joyalInterval X
  naturality {X Y} f := by
    change joyalInterval ◁ f ≫ snd joyalInterval Y = snd joyalInterval X ≫ f
    exact whiskerLeft_snd _ _

/-- The native precylinder with underlying endofunctor `J ⊗ -`. -/
noncomputable def productPrecylinder : Precylinder (𝟭 SSet.{u}) where
  I := tensorLeft joyalInterval
  i₀ := productEndpoint 0
  i₁ := productEndpoint 1
  π := productProjection
  i₀_π := by ext X; simp [productEndpoint, productProjection]
  i₁_π := by ext X; simp [productEndpoint, productProjection]

@[simp]
lemma productPrecylinder_I : productPrecylinder.{u}.I = tensorLeft joyalInterval := rfl

@[simp]
lemma productPrecylinder_projection (X : SSet.{u}) :
    (productPrecylinder.app X).π = snd joyalInterval X := rfl

@[simp]
lemma productPrecylinder_endpoint (X : SSet.{u}) (ε : Fin 2) :
    (productPrecylinder.app X).endpoint ε = lift (toUnit X ≫ unitPoint ε) (𝟙 X) := by
  fin_cases ε <;> rfl

/-- The product endpoint is the unit endpoint tensored with the identity. -/
lemma productPrecylinder_endpoint_unitor (X : SSet.{u}) (ε : Fin 2) :
    (productPrecylinder.app X).endpoint ε = (λ_ X).inv ≫ unitPoint ε ▷ X := by
  rw [productPrecylinder_endpoint]
  apply CartesianMonoidalCategory.hom_ext <;> simp

private lemma mono_unitPointCoprod :
    Mono (coprod.desc (unitPoint.{u} 0) (unitPoint 1)) := by
  have h : coprod.desc (unitPoint.{u} 0) (unitPoint 1) =
      coprod.map (isTerminalTensorUnit.uniqueUpToIso stdSimplex.isTerminalObj₀.{u}).hom
        (isTerminalTensorUnit.uniqueUpToIso stdSimplex.isTerminalObj₀.{u}).hom ≫
          endpointCoprod.{u} := by
    apply coprod.hom_ext <;> simp [unitPoint]
  rw [h]
  infer_instance

/-- The full pointwise boundary of the product precylinder is monic. -/
instance mono_productPrecylinder_boundary (X : SSet.{u}) :
    Mono (productPrecylinder.app X).i := by
  have hJ : Mono (coprod.desc (unitPoint.{u} 0) (unitPoint 1)) := mono_unitPointCoprod
  have h : (productPrecylinder.app X).i =
      coprod.map (λ_ X).inv (λ_ X).inv ≫
        coprodComparison (tensorRight X) (𝟙_ SSet.{u}) (𝟙_ SSet.{u}) ≫
          coprod.desc (unitPoint.{u} 0) (unitPoint 1) ▷ X := by
    apply coprod.hom_ext
    · simpa [coprodComparison, ← MonoidalCategory.comp_whiskerRight] using
        productPrecylinder_endpoint_unitor X 0
    · simpa [coprodComparison, ← MonoidalCategory.comp_whiskerRight] using
        productPrecylinder_endpoint_unitor X 1
  rw [h]
  have h₁ : IsIso (coprod.map (λ_ X).inv (λ_ X).inv) := inferInstance
  have h₂ : IsIso (coprodComparison (tensorRight X) (𝟙_ SSet.{u}) (𝟙_ SSet.{u})) :=
    inferInstance
  have h₃ : Mono (coprod.desc (unitPoint.{u} 0) (unitPoint 1) ▷ X) := by
    change Mono ((tensorRight X).map (coprod.desc (unitPoint.{u} 0) (unitPoint 1)))
    infer_instance
  infer_instance

/-- Every endpoint naturality square of the product cylinder is a pullback. -/
theorem productPrecylinder_endpoint_isPullback {X Y : SSet.{u}} (i : X ⟶ Y)
    (ε : Fin 2) :
    IsPullback i ((productPrecylinder.app X).endpoint ε)
      ((productPrecylinder.app Y).endpoint ε) (joyalInterval ◁ i) := by
  have w : i ≫ (productPrecylinder.app Y).endpoint ε =
      (productPrecylinder.app X).endpoint ε ≫ joyalInterval ◁ i :=
    productPrecylinder.endpoint_naturality i ε
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk w
    (fun s ↦ s.snd ≫ snd joyalInterval X) ?_ ?_ ?_)
  · intro s
    have h := congrArg (fun k ↦ k ≫ snd joyalInterval Y) s.condition
    simpa only [Category.assoc, productPrecylinder_endpoint, comp_lift, lift_snd,
      Category.comp_id, whiskerLeft_snd] using h.symm
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · have h := congrArg (fun k ↦ k ≫ fst joyalInterval Y) s.condition
      simpa only [Category.assoc, productPrecylinder_endpoint, comp_lift, lift_fst,
        whiskerLeft_fst, comp_toUnit_assoc] using h
    · simp only [Category.assoc, productPrecylinder_endpoint, comp_lift, lift_snd,
        Category.comp_id]
  · intro s m _ hm
    have h := congrArg (fun k ↦ k ≫ snd joyalInterval X) hm
    simpa only [Category.assoc, productPrecylinder_endpoint, comp_lift, lift_snd,
      Category.comp_id] using h

/-- Product with the finite interval is exact at the value universe. -/
instance isExact_productPrecylinder : productPrecylinder.{u}.IsExact.{u} where
  toPreservesMonomorphisms := by
    change Functor.PreservesMonomorphisms (tensorLeft joyalInterval)
    infer_instance
  toPreservesColimitsOfSize := by
    change PreservesColimitsOfSize.{u, u} (tensorLeft joyalInterval)
    infer_instance
  mono_boundary X := mono_productPrecylinder_boundary X
  endpoint_isPullback i _ ε := productPrecylinder_endpoint_isPullback i ε

end SSet.joyalInterval
