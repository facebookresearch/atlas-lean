/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Preadditive.EilenbergMoore
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-!
# Abelian coalgebras for an additive left exact comonad

Coalgebra morphisms form the additive subgroup of maps commuting with the
coactions. The forgetful functor creates the required limits and colimits.
Its preservation of the coimage-image comparison and reflection of
isomorphisms give an abelian category of coalgebras.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v w

namespace CategoryTheory.Comonad
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (G : Comonad C) [G.toFunctor.Additive]

/-- The additive subgroup of underlying maps compatible with the coactions. -/
def compatibleHomSubgroup (X Y : G.Coalgebra) : AddSubgroup (X.A ⟶ Y.A) where
  carrier := { f | X.a ≫ G.map f = f ≫ Y.a }
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change X.a ≫ G.map (f + g) = (f + g) ≫ Y.a
    rw [G.toFunctor.map_add, Preadditive.comp_add, Preadditive.add_comp, hf, hg]
  neg_mem' := by
    intro f hf
    change X.a ≫ G.map (-f) = (-f) ≫ Y.a
    rw [G.toFunctor.map_neg, Preadditive.comp_neg, Preadditive.neg_comp, hf]

/-- Coalgebra maps are exactly the compatible subgroup, with identical underlying maps. -/
def compatibleHomEquiv (X Y : G.Coalgebra) : (X ⟶ Y) ≃ compatibleHomSubgroup G X Y where
  toFun f := ⟨f.f, f.h⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end CategoryTheory.Comonad

namespace CategoryTheory.Comonad
variable {C : Type u} [Category.{v} C]
variable (G : Comonad C)

/-- Finite limits of a limit-preserving comonad's coalgebras are created underneath. -/
instance coalgebraHasFiniteLimits [HasFiniteLimits C] [PreservesFiniteLimits G.toFunctor] :
    HasFiniteLimits G.Coalgebra where
  out _ _ _ :=
    { has_limit D := Comonad.forget_creates_limits_of_comonad_preserves D }

/-- Coalgebra colimits are created in the underlying category. -/
instance coalgebraHasFiniteColimits [HasFiniteColimits C] : HasFiniteColimits G.Coalgebra where
  out _ _ _ :=
    { has_colimit D := hasColimit_of_created D G.forget }

/-- The forgetful functor preserves finite limits for a limit-preserving comonad. -/
instance forgetPreservesFiniteLimits [HasFiniteLimits C] [PreservesFiniteLimits G.toFunctor] :
    PreservesFiniteLimits G.forget where
  preservesFiniteLimits J _ _ := by infer_instance

/-- The forgetful functor preserves every finite coalgebra colimit. -/
instance forgetPreservesFiniteColimits :
    PreservesFiniteColimits G.forget where
  preservesFiniteColimits J _ _ := by infer_instance

end CategoryTheory.Comonad

namespace CategoryTheory.Comonad
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (G : Comonad C) [G.toFunctor.Additive] [PreservesFiniteLimits G.toFunctor]

/-- An additive left exact comonad on an abelian category has an abelian coalgebra category. -/
@[instance_reducible]
def coalgebraAbelian : Abelian G.Coalgebra := by
  have : ∀ {X Y : G.Coalgebra} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    have : IsIso (G.forget.map (Abelian.coimageImageComparison f)) := by
      let e := Abelian.PreservesCoimageImageComparison.iso G.forget f
      exact (Arrow.isIso_iff_isIso_of_isIso e.hom).mpr inferInstance
    exact isIso_of_reflects_iso _ G.forget
  exact Abelian.ofCoimageImageComparisonIsIso

end CategoryTheory.Comonad
