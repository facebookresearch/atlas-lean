/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.TensorRestriction

/-!
# Original coefficient tensor along a ring homomorphism

This is the ring-map adapter to the existing native tensor factory. The
original coefficient keeps its carrier and S-action; its R-action is the
actual map f. Both ring worlds and both module worlds are independent.

The existing factory owns all tensor objects, maps and coefficient
naturality. This file introduces no tensor quotient, scalar-extension
engine, flatness assumption or comparison certificate.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u w t v

namespace ModuleCat.TensorRestriction

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)

/-- The original ring map supplies the sole native coefficient tensor factory. -/
abbrev factoryForMap :
    ModuleCat.{t} S ⥤ (ModuleCat.{v} R ⥤ ModuleCat.{max t v} S) := by
  letI : Algebra R S := f.toAlgebra
  exact factory.{u, w, t, v} R S

/-- Fix the original coefficient in the actual ring-map tensor family. -/
abbrev functorForMap (M : ModuleCat.{t} S) :
    ModuleCat.{v} R ⥤ ModuleCat.{max t v} S :=
  (factoryForMap.{u, w, t, v} f).obj M

/-- The original tensor functor is additive for arbitrary original coefficients. -/
instance functorForMap_additive (M : ModuleCat.{t} S) :
    (functorForMap.{u, w, t, v} f M).Additive := by
  letI : Algebra R S := f.toAlgebra
  change (functorAt R S M : ModuleCat.{v} R ⥤ ModuleCat.{max t v} S).Additive
  infer_instance

/-- An actual structural algebra and its structural map give the same tensor family. -/
theorem factoryForMap_algebraMap [Algebra R S] :
    factoryForMap.{u, w, t, v} (algebraMap R S) = factory.{u, w, t, v} R S := by
  unfold factoryForMap
  rw [toAlgebra_algebraMap]

/-- The actual input map acts on the second tensor factor. -/
theorem functorForMap_map_tmul (M : ModuleCat.{t} S)
    {L L' : ModuleCat.{v} R} (g : L ⟶ L') (m : M) (l : L) :
    letI : Module R M := Module.compHom M f
    ((functorForMap.{u, w, t, v} f M).map g).hom (m ⊗ₜ[R] l) =
      m ⊗ₜ[R] g.hom l := by
  letI : Algebra R S := f.toAlgebra
  exact functorAt_map_tmul R S M g m l

/-- The actual coefficient map acts on the first tensor factor. -/
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
