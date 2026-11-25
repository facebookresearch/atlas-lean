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

public import MathlibExt.Algebra.Category.LieModuleCat.Basic
public import MathlibExt.Algebra.Category.LieModuleCat.Restriction
public import MathlibExt.Algebra.Lie.UniversalEnveloping.Induction
public import MathlibExt.Algebra.Lie.UniversalEnveloping.Augmentation
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Original native Lie coefficients as right enveloping modules

Negating the original endomorphism representation and taking its opposite
is an actual Lie homomorphism. Native UEA lift and native opposite Hom
correspondence therefore give the right UEA representation on the original
coefficient carrier. Its ground scalar action is the original one, and its
right generator action is negative the original left Lie action. Native
UEA induction earns equivariance of every original coefficient morphism.
There is no CE, PBW, freeness or projectivity dependency.
-/

@[expose] public section

noncomputable section

universe u v w v' w'

open CategoryTheory MulOpposite

namespace LieModuleCat.RightUniversalEnveloping

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

attribute [local instance] LieRing.ofAssociativeRing

/-- The actual negative opposite of the original native endomorphism Lie representation. -/
def negativeOppositeLie (M : LieModuleCat.{w} R L) : L →ₗ⁅R⁆ (Module.End R M)ᵐᵒᵖ where
  toFun x := op (-(LieModule.toEnd R L M x))
  map_add' x y := by rw [map_add, neg_add, MulOpposite.op_add]
  map_smul' r x := by
    simp only [map_smul, ← smul_neg, RingHom.id_apply]
    rfl
  map_lie' := by
    intro x y
    apply unop_injective
    change -(LieModule.toEnd R L M ⁅x, y⁆) =
      (-(LieModule.toEnd R L M y)) * (-(LieModule.toEnd R L M x)) -
        (-(LieModule.toEnd R L M x)) * (-(LieModule.toEnd R L M y))
    rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, neg_sub]
    simp only [neg_mul, mul_neg, neg_neg]

/-- The original right UEA endomorphism representation, through native lift
and the native opposite algebra-Hom equivalence. -/
def representation (M : LieModuleCat.{w} R L) : Uᵐᵒᵖ →ₐ[R] Module.End R M :=
  AlgHom.opComm (UniversalEnvelopingAlgebra.lift R (negativeOppositeLie R L M))

theorem representation_op_ι (M : LieModuleCat.{w} R L) (x : L) (m : M) :
    representation R L M (op (UniversalEnvelopingAlgebra.ι R x)) m = -⁅x, m⁆ := by
  change (UniversalEnvelopingAlgebra.lift R (negativeOppositeLie R L M)
    (UniversalEnvelopingAlgebra.ι R x)).unop m = _
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- The original scalar action is recovered by the actual algebra-map law. -/
theorem representation_algebraMap (M : LieModuleCat.{w} R L) (r : R) (m : M) :
    representation R L M (algebraMap R Uᵐᵒᵖ r) m = r • m := by
  rw [(representation R L M).commutes]
  rfl

/-- The actual right acting-ring module on the original native Lie carrier. -/
@[instance_reducible]
def representationModule (M : LieModuleCat.{w} R L) : Module Uᵐᵒᵖ M :=
  Module.compHom M (representation R L M).toRingHom

/-- The represented right module retains the original carrier. -/
@[implicit_reducible]
def representObj (M : LieModuleCat.{w} R L) : ModuleCat.{w} Uᵐᵒᵖ :=
  letI := representationModule R L M
  ModuleCat.of Uᵐᵒᵖ M

@[simp]
theorem representObj_smul (M : LieModuleCat.{w} R L) (a : Uᵐᵒᵖ) (m : representObj R L M) :
    a • m = representation R L M a (show M from m) := rfl

theorem representObj_op_ι (M : LieModuleCat.{w} R L) (x : L) (m : M) :
    op (UniversalEnvelopingAlgebra.ι R x) • (show representObj R L M from m) = -⁅x, m⁆ :=
  representation_op_ι R L M x m

/-- The native scalar restriction of the represented right module preserves
the original ground scalar dictionary. -/
theorem representObj_ground_smul (M : LieModuleCat.{w} R L) (r : R) (m : M) :
    r • (show (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj (representObj R L M) from m) =
      r • m :=
  representation_algebraMap R L M r m

/-- Original coefficient maps are equivariant for the actual right UEA actions. -/
theorem representation_map {M M' : LieModuleCat.{w} R L}
    (h : M →ₗ⁅R,L⁆ M') (a : Uᵐᵒᵖ) (m : M) :
    h (representation R L M a m) = representation R L M' a (h m) := by
  have hU : ∀ u : U, ∀ m : M,
      h (representation R L M (op u) m) = representation R L M' (op u) (h m) := by
    intro u
    induction u using UniversalEnvelopingAlgebra.induction R L with
    | algebraMap r =>
        intro m
        change h (representation R L M (algebraMap R Uᵐᵒᵖ r) m) =
          representation R L M' (algebraMap R Uᵐᵒᵖ r) (h m)
        rw [representation_algebraMap, representation_algebraMap, map_smul]
    | ι x =>
        intro m
        rw [representation_op_ι, representation_op_ι, map_neg, h.map_lie]
    | mul u v hu hv =>
        intro m
        simp only [MulOpposite.op_mul, map_mul]
        change h (representation R L M (op v) (representation R L M (op u) m)) =
          representation R L M' (op v) (representation R L M' (op u) (h m))
        rw [hv, hu]
    | add u v hu hv =>
        intro m
        simp only [MulOpposite.op_add, map_add]
        change h (representation R L M (op u) m + representation R L M (op v) m) = _
        rw [map_add, hu, hv]
        rw [LinearMap.add_apply]
  exact hU a.unop m

/-- The actual right UEA morphism supplied by an original native Lie coefficient map. -/
def representMap {M M' : LieModuleCat.{w} R L} (h : M ⟶ M') :
    representObj R L M ⟶ representObj R L M' := by
  let H : M →ₗ⁅R,L⁆ M' := h.hom
  letI := representationModule R L M
  letI := representationModule R L M'
  exact ModuleCat.ofHom
    { toFun := H
      map_add' := H.map_add
      map_smul' := by
        intro a m
        change H (representation R L M a m) = representation R L M' a (H m)
        exact representation_map R L H a m }

/-- The original-carrier representation is a genuine functor on native Lie coefficients. -/
def representFunctor : LieModuleCat.{w} R L ⥤ ModuleCat.{w} Uᵐᵒᵖ where
  obj := representObj R L
  map := representMap R L
  map_id M := by apply ModuleCat.hom_ext; ext m; rfl
  map_comp h k := by apply ModuleCat.hom_ext; ext m; rfl

section LieMaps

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L']
  (f : L →ₗ⁅R⁆ L') {M : LieModuleCat.{w} R L} {M' : LieModuleCat.{w'} R L'}
  (h : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f M')

/-- Every compatible original Lie coefficient map is equivariant for the
actual UEA map and the two original right representations. -/
theorem representation_lieMap (a : U) (m : M) :
    h (representation R L M (op a) m) =
      representation R L' M' (op (UniversalEnvelopingAlgebra.map R f a)) (h m) := by
  have hU : ∀ m : M, h (representation R L M (op a) m) =
      representation R L' M' (op (UniversalEnvelopingAlgebra.map R f a)) (h m) := by
    induction a using UniversalEnvelopingAlgebra.induction R L with
    | algebraMap r =>
        intro m
        rw [(UniversalEnvelopingAlgebra.map R f).commutes]
        change h (representation R L M (algebraMap R Uᵐᵒᵖ r) m) =
          representation R L' M' (algebraMap R (UniversalEnvelopingAlgebra R L')ᵐᵒᵖ r) (h m)
        rw [representation_algebraMap, representation_algebraMap, map_smul]
    | ι x =>
        intro m
        rw [UniversalEnvelopingAlgebra.map_ι, representation_op_ι,
          representation_op_ι, map_neg]
        congr 1
        exact h.map_lie x m
    | mul a b ha hb =>
        intro m
        simp only [MulOpposite.op_mul, map_mul]
        change h (representation R L M (op b) (representation R L M (op a) m)) =
          representation R L' M' (op (UniversalEnvelopingAlgebra.map R f b))
            (representation R L' M' (op (UniversalEnvelopingAlgebra.map R f a)) (h m))
        rw [hb, ha]
    | add a b ha hb =>
        intro m
        simp only [MulOpposite.op_add, map_add]
        change h (representation R L M (op a) m + representation R L M (op b) m) = _
        rw [map_add, ha, hb]
        rw [LinearMap.add_apply]
  exact hU m

/-- The actual native Lie coefficient map, as a genuinely semilinear right
UEA map along the original enveloping map, with independent carrier worlds. -/
def representLieMapSemilinear : representObj R L M →ₛₗ[(UniversalEnvelopingAlgebra.map R f).toRingHom.op]
    representObj R L' M' where
  toFun := h
  map_add' := h.map_add
  map_smul' a m := representation_lieMap R L f h a.unop m

end LieMaps

end LieModuleCat.RightUniversalEnveloping
