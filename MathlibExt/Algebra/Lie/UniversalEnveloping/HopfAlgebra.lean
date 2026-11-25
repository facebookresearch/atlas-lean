/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/

module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.Bialgebra
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Primitive

/-!
# The Hopf algebra of a universal enveloping algebra

The map sending a Lie generator `ι x` to `-op (ι x)` extends to an algebra
map into the opposite enveloping algebra. Its underlying linear map is
the antipode for the coproduct with primitive Lie generators.

The generators span the enveloping algebra as an algebra. The native
generating-set Hopf factory extends the two antipode identities from these
generators to all elements. The antipode reverses products, is involutive,
and commutes with the enveloping maps induced by Lie morphisms.

The coefficient ring and Lie carrier universes are independent. The
construction requires only a commutative ring and a Lie algebra over it.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped TensorProduct

universe u v v'

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type u) [CommRing R]

section Construction

variable (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- The Lie generators generate their universal enveloping algebra as an algebra. -/
theorem adjoin_range_ι : Algebra.adjoin R (Set.range (ι R : L → U)) = ⊤ := by
  have hsurj : Function.Surjective (mkAlgHom R L) := fun a => Quotient.exists_rep a
  calc
    Algebra.adjoin R (Set.range (ι R : L → U)) = (mkAlgHom R L).range := by
      symm
      rw [← Algebra.map_top, ← TensorAlgebra.adjoin_range_ι R (M := L),
        AlgHom.map_adjoin, Set.image_range]
      rfl
    _ = ⊤ := AlgHom.range_eq_top.mpr hsurj

/-- The signed Lie generators extend to an algebra map into the opposite algebra. -/
def antipodeToOpposite : U →ₐ[R] Uᵐᵒᵖ :=
  lift R
    { __ := -((MulOpposite.opLinearEquiv R (M := U)).toLinearMap.comp (ι R).toLinearMap)
      map_lie' := by
        intro x y
        change -MulOpposite.op (ι R ⁅x, y⁆) =
          ⁅-MulOpposite.op (ι R x), -MulOpposite.op (ι R y)⁆
        apply MulOpposite.unop_injective
        change -ι R ⁅x, y⁆ = (-ι R y) * (-ι R x) - (-ι R x) * (-ι R y)
        rw [LieHom.map_lie]
        change -(ι R x * ι R y - ι R y * ι R x) =
          (-ι R y) * (-ι R x) - (-ι R x) * (-ι R y)
        simp only [neg_mul_neg, neg_sub] }

/-- The opposite-algebra map sends each Lie generator to its negative. -/
@[simp]
theorem antipodeToOpposite_ι (x : L) :
    antipodeToOpposite R L (ι R x) = -MulOpposite.op (ι R x) := by
  rw [antipodeToOpposite, lift_ι_apply]
  rfl

/-- The primitive coproduct and signed opposite-algebra map give the native Hopf structure. -/
instance instHopfAlgebra : HopfAlgebra R U :=
  HopfAlgebra.ofAntipodeOfAdjoin (antipodeToOpposite R L)
    (X := Set.range (ι R : L → U)) (adjoin_range_ι R L)
    (by
      rintro _ ⟨x, rfl⟩
      rw [comul_ι, counit_ι]
      simp only [map_add, LinearMap.rTensor_tmul, LinearMap.mul'_apply]
      change MulOpposite.unop (antipodeToOpposite R L 1) * ι R x +
          MulOpposite.unop (antipodeToOpposite R L (ι R x)) * 1 = algebraMap R U 0
      rw [map_one, antipodeToOpposite_ι]
      simp)
    (by
      rintro _ ⟨x, rfl⟩
      rw [comul_ι, counit_ι]
      simp only [map_add, LinearMap.lTensor_tmul, LinearMap.mul'_apply]
      change 1 * MulOpposite.unop (antipodeToOpposite R L (ι R x)) +
          ι R x * MulOpposite.unop (antipodeToOpposite R L 1) = algebraMap R U 0
      rw [map_one, antipodeToOpposite_ι]
      simp)

/-- The native antipode negates each Lie generator. -/
@[simp]
theorem antipode_ι (x : L) : HopfAlgebra.antipode R (ι R x) = -ι R x := by
  change MulOpposite.unop (antipodeToOpposite R L (ι R x)) = -ι R x
  rw [antipodeToOpposite_ι]
  rfl

/-- The native antipode as an opposite-algebra map is the signed universal lift. -/
theorem antipodeAlgHomOp_eq :
    HopfAlgebra.antipodeAlgHomOp R U = antipodeToOpposite R L := by
  apply AlgHom.ext
  intro a
  change MulOpposite.op (MulOpposite.unop (antipodeToOpposite R L a)) =
    antipodeToOpposite R L a
  rfl

/-- The antipode of a universal enveloping algebra is involutive. -/
theorem antipode_involutive : Function.Involutive (HopfAlgebra.antipode R (A := U)) := by
  intro a
  have ha : a ∈ Algebra.adjoin R (Set.range (ι R : L → U)) := by
    rw [adjoin_range_ι]
    exact Subalgebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
      obtain ⟨x, rfl⟩ := ha
      exact (isPrimitiveElem_ι R L x).antipode_antipode
  | algebraMap r =>
      simp only [Algebra.algebraMap_eq_smul_one, map_smul, HopfAlgebra.antipode_one]
  | add a b _ _ ha hb =>
      simp only [map_add, ha, hb]
  | mul a b _ _ ha hb =>
      rw [HopfAlgebra.antipode_mul_antidistrib, HopfAlgebra.antipode_mul_antidistrib, ha, hb]

/-- Applying the native antipode twice recovers every enveloping-algebra element. -/
@[simp]
theorem antipode_antipode (a : U) :
    HopfAlgebra.antipode R (HopfAlgebra.antipode R a) = a :=
  antipode_involutive R L a

end Construction

section Maps

variable {L : Type v} [LieRing L] [LieAlgebra R L]
  {L' : Type v'} [LieRing L'] [LieAlgebra R L']

/-- The signed universal lifts are natural for Lie morphisms, with independent Lie worlds. -/
theorem map_antipodeToOpposite (f : L →ₗ⁅R⁆ L') :
    (map R f).op.comp (antipodeToOpposite R L) =
      (antipodeToOpposite R L').comp (map R f) := by
  apply hom_ext
  apply LieHom.ext
  intro x
  change (map R f).op (antipodeToOpposite R L (ι R x)) =
    antipodeToOpposite R L' (map R f (ι R x))
  rw [antipodeToOpposite_ι, map_ι, antipodeToOpposite_ι, map_neg]
  change -MulOpposite.op (map R f (ι R x)) = -MulOpposite.op (ι R (f x))
  rw [map_ι]

/-- Canonical enveloping maps commute with the native antipodes. -/
theorem map_antipode (f : L →ₗ⁅R⁆ L') (a : UniversalEnvelopingAlgebra R L) :
    map R f (HopfAlgebra.antipode R a) = HopfAlgebra.antipode R (map R f a) := by
  apply MulOpposite.op_injective
  change (map R f).op (antipodeToOpposite R L a) =
    antipodeToOpposite R L' (map R f a)
  exact AlgHom.congr_fun (map_antipodeToOpposite R f) a

end Maps

end UniversalEnvelopingAlgebra
