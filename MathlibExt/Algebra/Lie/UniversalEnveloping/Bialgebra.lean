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
# The bialgebra of a universal enveloping algebra

The coproduct sends each Lie generator to `1 ⊗ ι x + ι x ⊗ 1`.
Together with the scalar augmentation, it makes the universal enveloping
algebra a bialgebra over any commutative ring. Lie morphisms induce
bialgebra morphisms whose underlying algebra maps are the canonical
enveloping maps.
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

/-- The universal enveloping algebra has the bialgebra structure with primitive Lie generators. -/
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

/-- The native bialgebra counit is the canonical scalar augmentation. -/
@[simp]
theorem counitAlgHom_eq_augmentation :
    Bialgebra.counitAlgHom R U = augmentation R L := by
  apply AlgHom.ext
  intro a
  rfl

/-- Every Lie generator has coproduct `1 ⊗ ι x + ι x ⊗ 1`. -/
@[simp]
theorem comul_ι (x : L) :
    Coalgebra.comul (R := R) (ι R x) = 1 ⊗ₜ[R] ι R x + ι R x ⊗ₜ[R] 1 := by
  change comultiplication R L (ι R x) = 1 ⊗ₜ[R] ι R x + ι R x ⊗ₜ[R] 1
  exact comultiplication_ι R L x

/-- The counit annihilates every Lie generator. -/
@[simp]
theorem counit_ι (x : L) : Coalgebra.counit (R := R) (ι R x) = 0 :=
  augmentation_ι R x

/-- The canonical Lie generators are native primitive elements of the enveloping bialgebra. -/
theorem isPrimitiveElem_ι (x : L) : Bialgebra.IsPrimitiveElem R (ι R x) :=
  ⟨counit_ι R L x, comul_ι R L x⟩

end Construction

section Maps

variable {L : Type v} [LieRing L] [LieAlgebra R L]
  {L' : Type v'} [LieRing L'] [LieAlgebra R L']
  {L'' : Type v''} [LieRing L''] [LieAlgebra R L'']

/-- Canonical enveloping maps preserve the native bialgebra counits. -/
theorem map_counitAlgHom (f : L →ₗ⁅R⁆ L') :
    (Bialgebra.counitAlgHom R (UniversalEnvelopingAlgebra R L')).comp (map R f) =
      Bialgebra.counitAlgHom R (UniversalEnvelopingAlgebra R L) := by
  simpa only [counitAlgHom_eq_augmentation] using augmentation_naturality R f

/-- Canonical enveloping maps preserve the native bialgebra coproducts. -/
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

/-- A Lie morphism induces a bialgebra morphism through the canonical enveloping algebra map. -/
def mapBialgHom (f : L →ₗ⁅R⁆ L') :
    UniversalEnvelopingAlgebra R L →ₐc[R] UniversalEnvelopingAlgebra R L' :=
  BialgHom.ofAlgHom (map R f) (map_counitAlgHom R f) (map_comulAlgHom R f)

/-- The induced bialgebra map has the canonical enveloping algebra map as its underlying map. -/
@[simp]
theorem mapBialgHom_apply (f : L →ₗ⁅R⁆ L') (a : UniversalEnvelopingAlgebra R L) :
    mapBialgHom R f a = map R f a :=
  rfl

/-- Forgetting the bialgebra structure recovers the canonical enveloping algebra map. -/
@[simp]
theorem mapBialgHom_toAlgHom (f : L →ₗ⁅R⁆ L') :
    (mapBialgHom R f).toAlgHom = map R f := by
  apply AlgHom.ext
  intro a
  rfl

/-- Identity Lie morphisms induce identity bialgebra morphisms. -/
@[simp]
theorem mapBialgHom_id :
    mapBialgHom R (LieHom.id : L →ₗ⁅R⁆ L) =
      BialgHom.id R (UniversalEnvelopingAlgebra R L) := by
  apply BialgHom.ext
  intro a
  change map R (LieHom.id : L →ₗ⁅R⁆ L) a = a
  rw [map_id]
  rfl

/-- Composition of Lie morphisms induces composition of bialgebra morphisms. -/
theorem mapBialgHom_comp (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'') :
    mapBialgHom R (g.comp f) = (mapBialgHom R g).comp (mapBialgHom R f) := by
  apply BialgHom.ext
  intro a
  change map R (g.comp f) a = map R g (map R f a)
  rw [map_comp]
  rfl

end Maps

end UniversalEnvelopingAlgebra
