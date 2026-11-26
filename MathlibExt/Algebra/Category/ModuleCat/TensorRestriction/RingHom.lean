/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.TensorRestriction

/-!
# The restricted-coefficient tensor bifunctor for a specified ring map

For a homomorphism f : R → S of commutative rings, use f to restrict the action on an S-module
M. The bifunctor sends (M,L) to M ⊗_R L as an S-module, with f determining the balancing
action.

Input maps act on the second factor and coefficient maps on the first. At f = algebraMap R S,
this is the tensor bifunctor for the given algebra structure, with all ring and carrier
universe levels as stated.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u w t v

namespace ModuleCat.TensorRestriction

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)

/-- The tensor bifunctor determined by a ring homomorphism.

For f : R → S, use its algebra structure to send an S-module M to the R-input tensor functor M
⊗_R −. -/
abbrev factoryForMap :
    ModuleCat.{t} S ⥤ (ModuleCat.{v} R ⥤ ModuleCat.{max t v} S) := by
  letI : Algebra R S := f.toAlgebra
  exact factory.{u, w, t, v} R S

/-- The tensor functor for a specified scalar map and coefficient.

For f : R → S and M an S-module, this functor sends L to M ⊗_R L, with M restricted along f. -/
abbrev functorForMap (M : ModuleCat.{t} S) :
    ModuleCat.{v} R ⥤ ModuleCat.{max t v} S :=
  (factoryForMap.{u, w, t, v} f).obj M

/-- Additivity of tensoring through a specified ring map.

The functor L ↦ M ⊗_R L defined using f preserves sums of input morphisms. -/
instance functorForMap_additive (M : ModuleCat.{t} S) :
    (functorForMap.{u, w, t, v} f M).Additive := by
  letI : Algebra R S := f.toAlgebra
  change (functorAt R S M : ModuleCat.{v} R ⥤ ModuleCat.{max t v} S).Additive
  infer_instance

/-- Agreement with tensoring through the algebra map.

For an existing algebra structure R → S, factoryForMap at algebraMap R S equals the
coefficient tensor bifunctor of that structure. -/
theorem factoryForMap_algebraMap [Algebra R S] :
    factoryForMap.{u, w, t, v} (algebraMap R S) = factory.{u, w, t, v} R S := by
  unfold factoryForMap
  rw [toAlgebra_algebraMap]

/-- Input-map coordinates for the specified scalar tensor functor.

The map of g : L → L′ sends m ⊗ l to m ⊗ g(l), with the R-action on M restricted through f. -/
theorem functorForMap_map_tmul (M : ModuleCat.{t} S)
    {L L' : ModuleCat.{v} R} (g : L ⟶ L') (m : M) (l : L) :
    letI : Module R M := Module.compHom M f
    ((functorForMap.{u, w, t, v} f M).map g).hom (m ⊗ₜ[R] l) =
      m ⊗ₜ[R] g.hom l := by
  letI : Algebra R S := f.toAlgebra
  exact functorAt_map_tmul R S M g m l

/-- Coefficient-map coordinates for the specified scalar tensor bifunctor.

For an S-linear map g : M → N, the component at L sends m ⊗ l to g(m) ⊗ l. -/
theorem factoryForMap_map_tmul {M N : ModuleCat.{t} S} (g : M ⟶ N)
    (L : ModuleCat.{v} R) (m : M) (l : L) :
    letI : Module R M := Module.compHom M f
    letI : Module R N := Module.compHom N f
    (((factoryForMap.{u, w, t, v} f).map g).app L).hom (m ⊗ₜ[R] l) =
      g.hom m ⊗ₜ[R] l := by
  letI : Algebra R S := f.toAlgebra
  exact coefficientMapAt_tmul R S g L m l

end ModuleCat.TensorRestriction

end
