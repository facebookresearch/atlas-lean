/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Monad.MonoidalBar
public import Mathlib.CategoryTheory.Monoidal.Internal.Module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Tensor descriptions of relative Bar complexes

This file compares the categorical Bar construction with its tensor description. The algebra
object, coefficient actions, augmentation, and tensor maps are identified through the specified
structural isomorphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MulOpposite
open scoped TensorProduct ModuleCat.Algebra

universe u

namespace ModuleCat.RelativeTensorBar

variable (k R : Type u) [CommRing k] [Ring R] [Algebra k R]

/-- Restriction of the original right coefficient action to the ground ring. -/
abbrev rightUnderlying (M : ModuleCat.{u} Rᵐᵒᵖ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ)).obj M

/-- Restriction of the original left coefficient action to the ground ring. -/
abbrev leftUnderlying (N : ModuleCat.{u} R) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (algebraMap k R)).obj N

/-- The original algebra carrier with its original ground action. -/
abbrev ringUnderlying : ModuleCat.{u} k := ModuleCat.of k R

/-- The internal monoid of the original algebra, without reconstructing its ring. -/
@[instance_reducible]
def ringMonObj : MonObj (ringUnderlying k R) :=
  ModuleCat.MonModuleEquivalenceAlgebra.inverseObj (AlgCat.of k R)

/-- The right coefficient action on the outer tensor factor. -/
def rightAction (M : ModuleCat.{u} Rᵐᵒᵖ) :
    rightUnderlying k R M ⊗ ringUnderlying k R ⟶ rightUnderlying k R M :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun m r => (op r : Rᵐᵒᵖ) • m)
    (by intro m m' r; exact smul_add (op r : Rᵐᵒᵖ) m m')
    (by
      intro c m r
      change (op r : Rᵐᵒᵖ) • ((op (algebraMap k R c) : Rᵐᵒᵖ) • m) =
        (op (algebraMap k R c) : Rᵐᵒᵖ) • ((op r : Rᵐᵒᵖ) • m)
      rw [← mul_smul, ← mul_smul]
      apply congrArg (fun s : Rᵐᵒᵖ => s • m)
      simpa only [op_mul] using congrArg (op : R → Rᵐᵒᵖ) (Algebra.commutes c r))
    (by intro m r s; exact add_smul (op r : Rᵐᵒᵖ) (op s : Rᵐᵒᵖ) m)
    (by
      intro c m r
      rw [Algebra.smul_def]
      change (op (algebraMap k R c * r) : Rᵐᵒᵖ) • m =
        (op (algebraMap k R c) : Rᵐᵒᵖ) • ((op r : Rᵐᵒᵖ) • m)
      rw [op_mul, ← mul_smul]
      apply congrArg (fun s : Rᵐᵒᵖ => s • m)
      simpa only [op_mul] using congrArg (op : R → Rᵐᵒᵖ) (Algebra.commutes c r))

@[simp]
theorem rightAction_tmul (M : ModuleCat.{u} Rᵐᵒᵖ) (m : M) (r : R) :
    (rightAction k R M).hom (m ⊗ₜ[k] r) = (op r : Rᵐᵒᵖ) • m := rfl

/-- The left coefficient action on the last tensor factor. -/
def leftAction (N : ModuleCat.{u} R) :
    ringUnderlying k R ⊗ leftUnderlying k R N ⟶ leftUnderlying k R N :=
  ModuleCat.MonoidalCategory.tensorLift (fun r n => r • n)
    (by intro r s n; exact add_smul r s n)
    (by
      intro c r n
      change (c • r) • n = (algebraMap k R c) • (r • n)
      rw [Algebra.smul_def, mul_smul])
    (by intro r m n; exact smul_add r m n)
    (by
      intro c r n
      change r • ((algebraMap k R c) • n) = (algebraMap k R c) • (r • n)
      rw [← mul_smul, ← mul_smul]
      exact congrArg (fun s : R => s • n) (Algebra.commutes c r).symm)

@[simp]
theorem leftAction_tmul (N : ModuleCat.{u} R) (r : R) (n : N) :
    (leftAction k R N).hom (r ⊗ₜ[k] n) = r • n := rfl

/-- The internal left module of the original coefficient module. -/
@[instance_reducible]
def leftModObj (N : ModuleCat.{u} R) :
    letI : MonObj (ringUnderlying k R) := ringMonObj k R
    ModObj (ringUnderlying k R) (leftUnderlying k R N) := by
  letI : MonObj (ringUnderlying k R) := ringMonObj k R
  exact
    { smul := leftAction k R N
      one_smul := by
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro c n
        change (algebraMap k R c) • n = (algebraMap k R c) • n
        rfl
      mul_smul := by
        apply ModuleCat.MonoidalCategory.tensor_ext₃'
        intro r s n
        change (r * s) • n = r • (s • n)
        exact mul_smul r s n }

/-- Right-action unit law, constructed from the original scalar restriction. -/
theorem rightAction_one (M : ModuleCat.{u} Rᵐᵒᵖ) :
    letI : MonObj (ringUnderlying k R) := ringMonObj k R
    (rightUnderlying k R M ◁ MonObj.one) ≫ rightAction k R M =
      (ρ_ (rightUnderlying k R M)).hom := by
  let : MonObj (ringUnderlying k R) := ringMonObj k R
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m c
  change (op (algebraMap k R c) : Rᵐᵒᵖ) • m =
    (op (algebraMap k R c) : Rᵐᵒᵖ) • m
  rfl

/-- Right-action associativity, preserving noncommutative order. -/
theorem rightAction_assoc (M : ModuleCat.{u} Rᵐᵒᵖ) :
    letI : MonObj (ringUnderlying k R) := ringMonObj k R
    (α_ (rightUnderlying k R M) (ringUnderlying k R) (ringUnderlying k R)).hom ≫
        (rightUnderlying k R M ◁ MonObj.mul) ≫ rightAction k R M =
      (rightAction k R M ▷ ringUnderlying k R) ≫ rightAction k R M := by
  let : MonObj (ringUnderlying k R) := ringMonObj k R
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro m r s
  change (op (r * s) : Rᵐᵒᵖ) • m = (op s : Rᵐᵒᵖ) • ((op r : Rᵐᵒᵖ) • m)
  rw [op_mul, mul_smul]

/-- The right monadic module used by the literal coefficient Bar. -/
def rightModule (M : ModuleCat.{u} Rᵐᵒᵖ) :
    letI : MonObj (ringUnderlying k R) := ringMonObj k R
    Monad.RightModule (Monad.tensorMonad (ringUnderlying k R)) (ModuleCat.{u} k) := by
  letI : MonObj (ringUnderlying k R) := ringMonObj k R
  exact Monad.rightModuleOfRightAction (rightUnderlying k R M) (ringUnderlying k R)
    (rightAction k R M) (rightAction_one k R M) (rightAction_assoc k R M)

/-- The coefficient Bar, with the M action at d₀ and the N action at the last face. -/
abbrev literalBar (M : ModuleCat.{u} Rᵐᵒᵖ) (N : ModuleCat.{u} R) :
    SimplicialObject (ModuleCat.{u} k) :=
  letI : MonObj (ringUnderlying k R) := ringMonObj k R
  letI : ModObj (ringUnderlying k R) (leftUnderlying k R N) := leftModObj k R N
  Monad.monoidalBar (rightUnderlying k R M) (ringUnderlying k R) (leftUnderlying k R N)
    (rightAction k R M) (rightAction_one k R M) (rightAction_assoc k R M) ⋙
      (evaluation (Discrete PUnit.{1}) (ModuleCat.{u} k)).obj (Discrete.mk PUnit.unit)

end ModuleCat.RelativeTensorBar
