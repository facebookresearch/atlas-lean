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
# Lie algebras of primitive elements

Let H be a bialgebra over a commutative ring R, with H an associative ring. Its primitive
elements satisfy Δ(x) = 1 ⊗ x + x ⊗ 1. They form an R-Lie subalgebra of H under the commutator
[x,y] = xy−yx, using the submodule of (1,1)-skew-primitive elements.

A bialgebra homomorphism f : H → K restricts to a Lie homomorphism on primitives. These maps
respect identities and composition, commute with the inclusions into H and K, and induce the
naturality square for the universal enveloping algebra maps to the original bialgebras. The
scalar and bialgebra universes are independent.
-/

@[expose] public section

universe u v w z

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Bialgebra

variable (R : Type u) [CommRing R] (H : Type v) [Ring H] [Bialgebra R H]

/-- Primitive elements as a Lie subalgebra.

For an R-bialgebra H with R commutative and H a ring, the elements with Δ(x) = 1 ⊗ x + x ⊗ 1
form a Lie subalgebra under [x,y] = xy−yx. Its underlying submodule is the
(1,1)-skew-primitive submodule. -/
def primitiveLieSubalgebra : LieSubalgebra R H where
  __ := Coalgebra.skewPrimitive R (1 : H) 1
  lie_mem' := by
    intro x y hx hy
    exact IsPrimitiveElem.commutator hx hy

/-- Underlying submodule of the primitive Lie algebra.

For a bialgebra H over a commutative ring R, the submodule underlying primitiveLieSubalgebra R
H is Coalgebra.skewPrimitive R 1 1, the submodule of primitive elements. -/
@[simp]
theorem primitiveLieSubalgebra_toSubmodule :
    (primitiveLieSubalgebra R H).toSubmodule = Coalgebra.skewPrimitive R (1 : H) 1 :=
  rfl

/-- Membership criterion for the primitive Lie subalgebra.

For x in a bialgebra H over a commutative ring R, x belongs to primitiveLieSubalgebra R H
exactly when IsPrimitiveElem R x holds. -/
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

/-- Lie map on primitives induced by a bialgebra homomorphism.

For f : H →ₐc[R] K between bialgebras over a commutative ring, restrict f to the primitive Lie
subalgebras. Preservation of comultiplication and unit sends primitives to primitives, while
the algebra-map commutator law gives preservation of the Lie bracket. -/
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

/-- Underlying value of a map on primitive Lie algebras.

For a primitive x in H and bialgebra homomorphism f : H → K, the image f.primitiveLieMap(x),
viewed in K, is f(x). -/
@[simp]
theorem primitiveLieMap_apply (f : H →ₐc[R] K)
    (x : Bialgebra.primitiveLieSubalgebra R H) :
    (f.primitiveLieMap x : K) = f (x : H) :=
  rfl

/-- Inclusion square for primitive Lie maps.

For f : H →ₐc[R] K, inclusion of the primitive Lie subalgebra into K after f.primitiveLieMap
equals f viewed as a Lie map after inclusion of the primitives into H. -/
theorem primitiveLieMap_incl (f : H →ₐc[R] K) :
    (Bialgebra.primitiveLieSubalgebra R K).incl.comp f.primitiveLieMap =
      f.toAlgHom.toLieHom.comp (Bialgebra.primitiveLieSubalgebra R H).incl := by
  apply LieHom.ext
  intro x
  rfl

/-- Identity law for induced primitive Lie maps.

The identity bialgebra homomorphism of H induces the identity Lie homomorphism of
primitiveLieSubalgebra R H. -/
@[simp]
theorem primitiveLieMap_id :
    (BialgHom.id R H).primitiveLieMap =
      (LieHom.id : Bialgebra.primitiveLieSubalgebra R H →ₗ⁅R⁆
        Bialgebra.primitiveLieSubalgebra R H) := by
  apply LieHom.ext
  intro x
  apply Subtype.ext
  rfl

/-- Composition law for induced primitive Lie maps.

For bialgebra maps f : H → K and g : K → L over R, (g ∘ f).primitiveLieMap = g.primitiveLieMap
∘ f.primitiveLieMap. -/
@[simp]
theorem primitiveLieMap_comp (f : H →ₐc[R] K) (g : K →ₐc[R] L) :
    (g.comp f).primitiveLieMap = g.primitiveLieMap.comp f.primitiveLieMap := by
  apply LieHom.ext
  intro x
  apply Subtype.ext
  rfl

/-- Naturality of enveloping maps from primitive Lie algebras.

For a bialgebra homomorphism f : H → K, let ev_H : U(P(H)) → H and ev_K : U(P(K)) → K be the
algebra maps extending the primitive inclusions. Then f ∘ ev_H = ev_K ∘ U(f.primitiveLieMap),
as R-algebra maps. -/
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
