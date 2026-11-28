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

public import MathlibExt.Algebra.Lie.UniversalEnveloping.Bialgebra
public import MathlibExt.RingTheory.Bialgebra.PrimitiveLie
public import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# Cocommutativity and primitive Lie generator naturality

The universal enveloping coproduct is cocommutative. Its primitive Lie subalgebra receives the
generator morphism L → Prim(U_R(L)), whose inclusion recovers ι.

This morphism is natural in Lie algebra maps. Lie algebra equivalences induce bialgebra
equivalences, with forward and inverse algebra maps given by the canonical enveloping maps.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type u) [CommRing R]

section Generators

variable (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "P" => Bialgebra.primitiveLieSubalgebra R U

/-- The enveloping coproduct is invariant under tensor exchange.

Composing the coproduct algebra map with the tensor commutation equivalence leaves it
unchanged. -/
theorem comulAlgHom_comm :
    (Algebra.TensorProduct.comm R U U).toAlgHom.comp (Bialgebra.comulAlgHom R U) =
      Bialgebra.comulAlgHom R U := by
  apply hom_ext
  apply LieHom.ext
  intro x
  change Algebra.TensorProduct.comm R U U (Coalgebra.comul (R := R) (ι R x)) =
    Coalgebra.comul (R := R) (ι R x)
  simp only [comul_ι, map_add, Algebra.TensorProduct.comm_tmul]
  exact add_comm _ _

/-- Cocommutativity of the enveloping coalgebra.

The coproduct satisfies the tensor exchange equation. -/
instance instIsCocomm : Coalgebra.IsCocomm R U where
  comm_comp_comul :=
    congrArg (fun f : U →ₐ[R] U ⊗[R] U => f.toLinearMap) (comulAlgHom_comm R L)

/-- The Lie generator map into primitive elements.

Send x to the primitive element ιx in the enveloping bialgebra's primitive Lie subalgebra. -/
def ιPrimitive : L →ₗ⁅R⁆ P where
  __ := (ι R).toLinearMap.codRestrict (Bialgebra.primitiveLieSubalgebra R U).toSubmodule
    (fun x => (Bialgebra.mem_primitiveLieSubalgebra R U).mpr (isPrimitiveElem_ι R L x))
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact (ι R).map_lie x y

/-- The underlying element of the primitive generator map.

The included primitive image of x is ιx. -/
@[simp]
theorem coe_ιPrimitive (x : L) : (ιPrimitive R L x : U) = ι R x :=
  rfl

/-- Primitive inclusion recovers the enveloping Lie map.

The primitive generator map followed by inclusion equals ι. -/
theorem ιPrimitive_incl :
    (Bialgebra.primitiveLieSubalgebra R U).incl.comp (ιPrimitive R L) = ι R := by
  apply LieHom.ext
  intro x
  rfl

end Generators

section Naturality

variable {L : Type v} [LieRing L] [LieAlgebra R L]
  {L' : Type w} [LieRing L'] [LieAlgebra R L']

/-- Naturality of the primitive generator Lie map.

The primitive Lie map induced by an enveloping bialgebra map commutes with the Lie generator
maps. -/
theorem ιPrimitive_naturality (f : L →ₗ⁅R⁆ L') :
    (mapBialgHom R f).primitiveLieMap.comp (ιPrimitive R L) =
      (ιPrimitive R L').comp f := by
  apply LieHom.ext
  intro x
  apply Subtype.ext
  simp only [LieHom.coe_comp, Function.comp_apply, BialgHom.primitiveLieMap_apply,
    coe_ιPrimitive, mapBialgHom_apply, map_ι]

/-- The bialgebra equivalence induced by a Lie equivalence.

Use the enveloping maps of the Lie equivalence and its inverse. -/
def mapBialgEquiv (e : L ≃ₗ⁅R⁆ L') :
    UniversalEnvelopingAlgebra R L ≃ₐc[R] UniversalEnvelopingAlgebra R L' :=
  BialgEquiv.ofBialgHom (mapBialgHom R e.toLieHom) (mapBialgHom R e.symm.toLieHom)
    (by
      rw [← mapBialgHom_comp]
      have h : e.toLieHom.comp e.symm.toLieHom = (LieHom.id : L' →ₗ⁅R⁆ L') := by
        apply LieHom.ext
        intro x
        exact e.right_inv x
      rw [h, mapBialgHom_id])
    (by
      rw [← mapBialgHom_comp]
      have h : e.symm.toLieHom.comp e.toLieHom = (LieHom.id : L →ₗ⁅R⁆ L) := by
        apply LieHom.ext
        intro x
        exact e.left_inv x
      rw [h, mapBialgHom_id])

/-- The forward enveloping bialgebra equivalence map.

Its value is map R applied to the forward Lie morphism. -/
@[simp]
theorem mapBialgEquiv_apply (e : L ≃ₗ⁅R⁆ L') (a : UniversalEnvelopingAlgebra R L) :
    mapBialgEquiv R e a = map R e.toLieHom a :=
  rfl

/-- The inverse enveloping bialgebra equivalence map.

Its value is map R applied to the inverse Lie morphism. -/
@[simp]
theorem mapBialgEquiv_symm_apply (e : L ≃ₗ⁅R⁆ L') (a : UniversalEnvelopingAlgebra R L') :
    (mapBialgEquiv R e).symm a = map R e.symm.toLieHom a :=
  rfl

end Naturality

end UniversalEnvelopingAlgebra
