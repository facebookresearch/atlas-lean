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

public import Mathlib.RingTheory.Bialgebra.Primitive
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import MathlibExt.Algebra.Lie.UniversalEnveloping.Augmentation

/-!
# Primitive Lie algebras of bialgebras

The primitive elements of a bialgebra over a commutative ring form a Lie
subalgebra under the ring commutator. Bialgebra morphisms induce Lie
morphisms on primitives. These maps preserve identities and composition,
and their enveloping maps commute with the primitive inclusions.
-/

@[expose] public section

universe u v w z

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Bialgebra

variable (R : Type u) [CommRing R] (H : Type v) [Ring H] [Bialgebra R H]

/-- The primitive elements, with the Lie bracket inherited from the ring commutator. -/
def primitiveLieSubalgebra : LieSubalgebra R H where
  __ := Coalgebra.skewPrimitive R (1 : H) 1
  lie_mem' := by
    intro x y hx hy
    exact IsPrimitiveElem.commutator hx hy

/-- The underlying submodule is the native submodule of `(1, 1)`-skew-primitives. -/
@[simp]
theorem primitiveLieSubalgebra_toSubmodule :
    (primitiveLieSubalgebra R H).toSubmodule = Coalgebra.skewPrimitive R (1 : H) 1 :=
  rfl

/-- Membership in the primitive Lie subalgebra is native bialgebra primitivity. -/
@[simp]
theorem mem_primitiveLieSubalgebra {x : H} :
    x ∈ primitiveLieSubalgebra R H ↔ IsPrimitiveElem R x :=
  Iff.rfl

end Bialgebra

namespace BialgHom

variable {R : Type u} [CommRing R]
  {H : Type v} [Ring H] [Bialgebra R H]
  {K : Type w} [Ring K] [Bialgebra R K]
  {L : Type z} [Ring L] [Bialgebra R L]

/-- A bialgebra morphism restricts to a Lie morphism of primitive elements. -/
def primitiveLieMap (f : H →ₐc[R] K) :
    Bialgebra.primitiveLieSubalgebra R H →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R K where
  __ := (f.toLinearMap.comp
    (Bialgebra.primitiveLieSubalgebra R H).toSubmodule.subtype).codRestrict
      (Bialgebra.primitiveLieSubalgebra R K).toSubmodule
      (fun x => by
        change Coalgebra.IsSkewPrimitiveElem R (1 : K) (1 : K) (f (x : H))
        simpa only [map_one] using x.property.map f)
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact f.toAlgHom.toLieHom.map_lie (x : H) (y : H)

/-- The induced primitive morphism has the original bialgebra morphism as its underlying map. -/
@[simp]
theorem primitiveLieMap_apply (f : H →ₐc[R] K)
    (x : Bialgebra.primitiveLieSubalgebra R H) :
    (f.primitiveLieMap x : K) = f (x : H) :=
  rfl

/-- Primitive inclusions commute with the induced Lie morphism. -/
theorem primitiveLieMap_incl (f : H →ₐc[R] K) :
    (Bialgebra.primitiveLieSubalgebra R K).incl.comp f.primitiveLieMap =
      f.toAlgHom.toLieHom.comp (Bialgebra.primitiveLieSubalgebra R H).incl := by
  apply LieHom.ext
  intro x
  rfl

/-- The identity bialgebra morphism induces the identity on primitives. -/
@[simp]
theorem primitiveLieMap_id :
    (BialgHom.id R H).primitiveLieMap =
      (LieHom.id : Bialgebra.primitiveLieSubalgebra R H →ₗ⁅R⁆
        Bialgebra.primitiveLieSubalgebra R H) := by
  apply LieHom.ext
  intro x
  apply Subtype.ext
  rfl

/-- Composition of bialgebra morphisms induces composition of primitive Lie morphisms. -/
@[simp]
theorem primitiveLieMap_comp (f : H →ₐc[R] K) (g : K →ₐc[R] L) :
    (g.comp f).primitiveLieMap = g.primitiveLieMap.comp f.primitiveLieMap := by
  apply LieHom.ext
  intro x
  apply Subtype.ext
  rfl

/-- The canonical enveloping maps of primitive Lie algebras commute with bialgebra morphisms. -/
theorem primitive_enveloping_naturality (f : H →ₐc[R] K) :
    f.toAlgHom.comp
        (UniversalEnvelopingAlgebra.lift R (Bialgebra.primitiveLieSubalgebra R H).incl) =
      (UniversalEnvelopingAlgebra.lift R (Bialgebra.primitiveLieSubalgebra R K).incl).comp
        (UniversalEnvelopingAlgebra.map R f.primitiveLieMap) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  change f (UniversalEnvelopingAlgebra.lift R
      (Bialgebra.primitiveLieSubalgebra R H).incl (UniversalEnvelopingAlgebra.ι R x)) =
    UniversalEnvelopingAlgebra.lift R (Bialgebra.primitiveLieSubalgebra R K).incl
      (UniversalEnvelopingAlgebra.map R f.primitiveLieMap (UniversalEnvelopingAlgebra.ι R x))
  simp only [UniversalEnvelopingAlgebra.map_ι, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

end BialgHom
