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
# Cocommutativity and primitive generators of enveloping bialgebras

The enveloping coproduct is cocommutative. The Lie generators define a
natural Lie morphism into the primitive Lie algebra, whose inclusion is
the original generator morphism. Lie algebra equivalences induce
bialgebra equivalences through the canonical enveloping maps.
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

/-- Swapping the two tensor factors fixes the enveloping coproduct algebra map. -/
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

/-- The universal enveloping bialgebra is cocommutative. -/
instance instIsCocomm : Coalgebra.IsCocomm R U where
  comm_comp_comul :=
    congrArg (fun f : U →ₐ[R] U ⊗[R] U => f.toLinearMap) (comulAlgHom_comm R L)

/-- The Lie generators as a Lie morphism into the primitive Lie algebra. -/
def ιPrimitive : L →ₗ⁅R⁆ P where
  __ := (ι R).toLinearMap.codRestrict P.toSubmodule
    (fun x => (Bialgebra.mem_primitiveLieSubalgebra R U).mpr (isPrimitiveElem_ι R L x))
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact (ι R).map_lie x y

/-- The primitive-valued generator morphism has the original generators as its underlying map. -/
@[simp]
theorem coe_ιPrimitive (x : L) : (ιPrimitive R L x : U) = ι R x :=
  rfl

/-- Including the primitive-valued generators recovers the original generator Lie morphism. -/
theorem ιPrimitive_incl : P.incl.comp (ιPrimitive R L) = ι R := by
  apply LieHom.ext
  intro x
  rfl

end Generators

section Naturality

variable {L : Type v} [LieRing L] [LieAlgebra R L]
  {L' : Type w} [LieRing L'] [LieAlgebra R L']

/-- Primitive-valued generators are natural in Lie morphisms through the canonical bialgebra map. -/
theorem ιPrimitive_naturality (f : L →ₗ⁅R⁆ L') :
    (mapBialgHom R f).primitiveLieMap.comp (ιPrimitive R L) =
      (ιPrimitive R L').comp f := by
  apply LieHom.ext
  intro x
  apply Subtype.ext
  simp only [LieHom.coe_comp, Function.comp_apply, BialgHom.primitiveLieMap_apply,
    coe_ιPrimitive, mapBialgHom_apply, map_ι]

/-- A Lie equivalence induces a bialgebra equivalence by the canonical enveloping maps. -/
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

/-- The induced bialgebra equivalence applies the canonical enveloping algebra map. -/
@[simp]
theorem mapBialgEquiv_apply (e : L ≃ₗ⁅R⁆ L') (a : UniversalEnvelopingAlgebra R L) :
    mapBialgEquiv R e a = map R e.toLieHom a :=
  rfl

/-- The inverse bialgebra equivalence applies the enveloping map of the inverse Lie equivalence. -/
@[simp]
theorem mapBialgEquiv_symm_apply (e : L ≃ₗ⁅R⁆ L') (a : UniversalEnvelopingAlgebra R L') :
    (mapBialgEquiv R e).symm a = map R e.symm.toLieHom a :=
  rfl

end Naturality

end UniversalEnvelopingAlgebra
