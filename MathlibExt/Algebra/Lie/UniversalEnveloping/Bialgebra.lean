/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.Augmentation
public import Mathlib.RingTheory.Bialgebra.Primitive
public import Mathlib.RingTheory.Bialgebra.Hom
public meta import Mathlib.Tactic.Abel

/-!
# The bialgebra structure of a universal enveloping algebra

For a Lie algebra L over a commutative ring R, the enveloping coproduct sends ιx to 1⊗ιx +
ιx⊗1, and the counit is the scalar augmentation. Thus every Lie generator is primitive.

Lie morphisms induce bialgebra morphisms through the canonical enveloping algebra maps. The
coefficient ring and all Lie carrier universes remain independent.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v v' v''

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type u) [CommRing R]

section Construction

variable (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

private def comultiplicationLinear : L →ₗ[R] U ⊗[R] U :=
  (TensorProduct.mk R U U 1).comp (ι R).toLinearMap +
    ((TensorProduct.mk R U U).flip 1).comp (ι R).toLinearMap

private theorem comultiplicationLinear_apply (x : L) :
    comultiplicationLinear R L x = 1 ⊗ₜ[R] ι R x + ι R x ⊗ₜ[R] 1 :=
  rfl

private theorem comultiplicationLinear_map_lie (x y : L) :
    comultiplicationLinear R L ⁅x, y⁆ =
      ⁅comultiplicationLinear R L x, comultiplicationLinear R L y⁆ := by
  simp only [comultiplicationLinear_apply, LieHom.map_lie,
    LieRing.of_associative_ring_bracket, TensorProduct.tmul_sub, TensorProduct.sub_tmul,
    add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  abel

private def comultiplicationLieHom : L →ₗ⁅R⁆ U ⊗[R] U where
  __ := comultiplicationLinear R L
  map_lie' := by
    intro x y
    exact comultiplicationLinear_map_lie R L x y

private def comultiplication : U →ₐ[R] U ⊗[R] U :=
  lift R (comultiplicationLieHom R L)

private theorem comultiplication_ι (x : L) :
    comultiplication R L (ι R x) = 1 ⊗ₜ[R] ι R x + ι R x ⊗ₜ[R] 1 := by
  rw [comultiplication, lift_ι_apply]
  exact comultiplicationLinear_apply R L x

private theorem comultiplication_coassoc :
    (Algebra.TensorProduct.assoc R R R U U U).toAlgHom.comp
        ((Algebra.TensorProduct.map (comultiplication R L) (AlgHom.id R U)).comp
          (comultiplication R L)) =
      (Algebra.TensorProduct.map (AlgHom.id R U) (comultiplication R L)).comp
        (comultiplication R L) := by
  apply hom_ext
  apply LieHom.ext
  intro x
  change Algebra.TensorProduct.assoc R R R U U U
      (Algebra.TensorProduct.map (comultiplication R L) (AlgHom.id R U)
        (comultiplication R L (ι R x))) =
    Algebra.TensorProduct.map (AlgHom.id R U) (comultiplication R L)
      (comultiplication R L (ι R x))
  simp only [comultiplication_ι, map_add, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, map_one, Algebra.TensorProduct.one_def,
    TensorProduct.add_tmul, TensorProduct.tmul_add, Algebra.TensorProduct.assoc_tmul,
    add_assoc]

private theorem comultiplication_counit_left :
    (Algebra.TensorProduct.map (augmentation R L) (AlgHom.id R U)).comp
        (comultiplication R L) = (Algebra.TensorProduct.lid R U).symm := by
  apply hom_ext
  apply LieHom.ext
  intro x
  change Algebra.TensorProduct.map (augmentation R L) (AlgHom.id R U)
      (comultiplication R L (ι R x)) = (Algebra.TensorProduct.lid R U).symm (ι R x)
  simp only [comultiplication_ι, map_add, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, map_one, augmentation_ι, TensorProduct.zero_tmul,
    add_zero, Algebra.TensorProduct.lid_symm_apply]

private theorem comultiplication_counit_right :
    (Algebra.TensorProduct.map (AlgHom.id R U) (augmentation R L)).comp
        (comultiplication R L) = (Algebra.TensorProduct.rid R R U).symm := by
  apply hom_ext
  apply LieHom.ext
  intro x
  change Algebra.TensorProduct.map (AlgHom.id R U) (augmentation R L)
      (comultiplication R L (ι R x)) = (Algebra.TensorProduct.rid R R U).symm (ι R x)
  simp only [comultiplication_ι, map_add, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, map_one, augmentation_ι, TensorProduct.tmul_zero,
    zero_add, Algebra.TensorProduct.rid_symm_apply]

/-- The enveloping bialgebra with primitive Lie generators.

Use the coproduct ιx ↦ 1⊗ιx + ιx⊗1 and the scalar augmentation as counit. -/
instance instBialgebra : Bialgebra R U :=
  Bialgebra.ofAlgHom
    (lift R
      { __ := (TensorProduct.mk R U U 1).comp (ι R).toLinearMap +
          ((TensorProduct.mk R U U).flip 1).comp (ι R).toLinearMap
        map_lie' := by
          intro x y
          exact comultiplicationLinear_map_lie R L x y })
    (augmentation R L)
    (by exact comultiplication_coassoc R L)
    (by exact comultiplication_counit_left R L)
    (by exact comultiplication_counit_right R L)

/-- The enveloping bialgebra counit is the augmentation.

The counit algebra homomorphism equals augmentation R L. -/
@[simp]
theorem counitAlgHom_eq_augmentation :
    Bialgebra.counitAlgHom R U = augmentation R L := by
  apply AlgHom.ext
  intro a
  rfl

/-- The coproduct of a Lie generator.

The coproduct of ιx is 1⊗ιx + ιx⊗1 in that tensor order. -/
@[simp]
theorem comul_ι (x : L) :
    Coalgebra.comul (R := R) (ι R x) = 1 ⊗ₜ[R] ι R x + ι R x ⊗ₜ[R] 1 := by
  change comultiplication R L (ι R x) = 1 ⊗ₜ[R] ι R x + ι R x ⊗ₜ[R] 1
  exact comultiplication_ι R L x

/-- The counit of a Lie generator.

The counit sends ιx to zero. -/
@[simp]
theorem counit_ι (x : L) : Coalgebra.counit (R := R) (ι R x) = 0 :=
  augmentation_ι R x

/-- Lie generators are primitive in the enveloping bialgebra.

Each ιx has zero counit and coproduct 1⊗ιx + ιx⊗1. -/
theorem isPrimitiveElem_ι (x : L) : Bialgebra.IsPrimitiveElem R (ι R x) :=
  ⟨counit_ι R L x, comul_ι R L x⟩

end Construction

section Maps

variable {L : Type v} [LieRing L] [LieAlgebra R L]
  {L' : Type v'} [LieRing L'] [LieAlgebra R L']
  {L'' : Type v''} [LieRing L''] [LieAlgebra R L'']

/-- Enveloping maps preserve the bialgebra counit.

The target counit after the map of a Lie morphism equals the source counit. -/
theorem map_counitAlgHom (f : L →ₗ⁅R⁆ L') :
    (Bialgebra.counitAlgHom R (UniversalEnvelopingAlgebra R L')).comp (map R f) =
      Bialgebra.counitAlgHom R (UniversalEnvelopingAlgebra R L) := by
  simpa only [counitAlgHom_eq_augmentation] using augmentation_naturality R f

/-- Enveloping maps preserve the bialgebra coproduct.

The tensor square of the enveloping map commutes with the coproduct algebra maps. -/
theorem map_comulAlgHom (f : L →ₗ⁅R⁆ L') :
    (Algebra.TensorProduct.map (map R f) (map R f)).comp
        (Bialgebra.comulAlgHom R (UniversalEnvelopingAlgebra R L)) =
      (Bialgebra.comulAlgHom R (UniversalEnvelopingAlgebra R L')).comp (map R f) := by
  apply hom_ext
  apply LieHom.ext
  intro x
  change Algebra.TensorProduct.map (map R f) (map R f)
      (Coalgebra.comul (R := R) (ι R x)) =
    Coalgebra.comul (R := R) (map R f (ι R x))
  simp only [comul_ι, map_ι, map_add, Algebra.TensorProduct.map_tmul, map_one]

/-- The bialgebra morphism induced by a Lie morphism.

Bundle the canonical enveloping algebra map with its coproduct and counit compatibilities. -/
def mapBialgHom (f : L →ₗ⁅R⁆ L') :
    UniversalEnvelopingAlgebra R L →ₐc[R] UniversalEnvelopingAlgebra R L' :=
  BialgHom.ofAlgHom (map R f) (map_counitAlgHom R f) (map_comulAlgHom R f)

/-- Values of the induced enveloping bialgebra morphism.

The underlying function is map R f. -/
@[simp]
theorem mapBialgHom_apply (f : L →ₗ⁅R⁆ L') (a : UniversalEnvelopingAlgebra R L) :
    mapBialgHom R f a = map R f a :=
  rfl

/-- The algebra map of the induced bialgebra morphism.

Its underlying algebra homomorphism is the canonical enveloping map. -/
@[simp]
theorem mapBialgHom_toAlgHom (f : L →ₗ⁅R⁆ L') :
    (mapBialgHom R f).toAlgHom = map R f := by
  apply AlgHom.ext
  intro a
  rfl

/-- The enveloping bialgebra map of the identity Lie morphism.

It is the identity bialgebra homomorphism. -/
@[simp]
theorem mapBialgHom_id :
    mapBialgHom R (LieHom.id : L →ₗ⁅R⁆ L) =
      BialgHom.id R (UniversalEnvelopingAlgebra R L) := by
  apply BialgHom.ext
  intro a
  change map R (LieHom.id : L →ₗ⁅R⁆ L) a = a
  rw [map_id]
  rfl

/-- Composition of enveloping bialgebra morphisms.

The bialgebra map of a composite Lie morphism is the composite of the induced maps. -/
theorem mapBialgHom_comp (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'') :
    mapBialgHom R (g.comp f) = (mapBialgHom R g).comp (mapBialgHom R f) := by
  apply BialgHom.ext
  intro a
  change map R (g.comp f) a = map R g (map R f a)
  rw [map_comp]
  rfl

end Maps

end UniversalEnvelopingAlgebra
