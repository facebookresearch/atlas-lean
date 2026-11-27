/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable

import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Small-object factorizations of simplicial maps

The boundary inclusions `I` admit the small-object argument at `aleph0`,
and `I.rlp.llp` is the class of simplicial monomorphisms. This gives a
functorial factorization into a monomorphism followed by an `I.rlp` map.
The anodyne-extension small-object argument gives a second functorial
factorization into an anodyne extension followed by a fibration, with
explicit factorization data for each simplicial map.
-/

@[expose] public section

universe u

open CategoryTheory HomotopicalAlgebra Simplicial MorphismProperty

namespace SSet

namespace modelCategoryQuillen

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

instance : MorphismProperty.IsSmall.{u} I.{u} :=
  isSmall_ofHoms _

instance instIsCardinalForSmallObjectArgumentIAleph0_mathlibExt :
    IsCardinalForSmallObjectArgument I.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      obtain ⟨n⟩ := hi
      infer_instance
    infer_instance

instance : HasSmallObjectArgument.{u} I.{u} :=
  ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

lemma llp_rlp_I : I.rlp.llp = monomorphisms SSet.{u} := by
  apply le_antisymm
  · rw [llp_rlp_of_hasSmallObjectArgument, retracts_le_iff,
      transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
    exact I_le_monomorphisms
  · rw [← SSet.rlp_monomorphisms]
    exact le_llp_rlp _

/-- Boundary small-object factorization: monomorphisms vs maps in `(monomorphisms SSet).rlp`. -/
scoped instance monoFunctorialFactorization :
    HasFunctorialFactorization (monomorphisms SSet.{u})
      (monomorphisms SSet.{u}).rlp := by
  rw [SSet.rlp_monomorphisms, ← llp_rlp_I]
  infer_instance

/-- Functorial factorization via boundary inclusions: every map factors functorially as a
monomorphism followed by a map with the right lifting property against monomorphisms. -/
noncomputable def monoFunctorialFactorizationData :
    FunctorialFactorizationData (monomorphisms SSet.{u}) (monomorphisms SSet.{u}).rlp :=
  functorialFactorizationData (monomorphisms SSet.{u}) (monomorphisms SSet.{u}).rlp

/-- Per-map factorization derived from `monoFunctorialFactorizationData`. -/
noncomputable def monoFactorizationData {X Y : SSet.{u}} (f : X ⟶ Y) :
    MapFactorizationData (monomorphisms SSet.{u}) (monomorphisms SSet.{u}).rlp f :=
  monoFunctorialFactorizationData.factorizationData f

instance {X Y : SSet.{u}} (f : X ⟶ Y) : Mono (monoFactorizationData (X := X) (Y := Y) f).i :=
  (monoFactorizationData f).hi

/-- Horn small-object factorization: anodyne extensions vs fibrations. -/
instance : HasFunctorialFactorization anodyneExtensions.{u} (fibrations SSet.{u}) := by
  rw [anodyneExtensions_eq_llp_rlp, fibrations_eq]
  infer_instance

/-- Functorial factorization via horn inclusions: every map factors functorially as an
anodyne extension followed by a fibration. -/
noncomputable def anodyneFunctorialFactorizationData :
    FunctorialFactorizationData anodyneExtensions.{u} (fibrations SSet.{u}) :=
  functorialFactorizationData anodyneExtensions.{u} (fibrations SSet.{u})

/-- Per-map factorization derived from `anodyneFunctorialFactorizationData`. -/
noncomputable def anodyneFactorizationData {X Y : SSet.{u}} (f : X ⟶ Y) :
    MapFactorizationData anodyneExtensions.{u} (fibrations SSet.{u}) f :=
  anodyneFunctorialFactorizationData.factorizationData f

/-- The left factor of the anodyne factorization is an anodyne extension. -/
theorem anodyneFactorizationData_mem_anodyne {X Y : SSet.{u}} (f : X ⟶ Y) :
    anodyneExtensions (anodyneFactorizationData f).i :=
  (anodyneFactorizationData f).hi

instance {X Y : SSet.{u}} (f : X ⟶ Y) : Fibration (anodyneFactorizationData f).p :=
  ⟨(anodyneFactorizationData f).hp⟩

end modelCategoryQuillen

end SSet
