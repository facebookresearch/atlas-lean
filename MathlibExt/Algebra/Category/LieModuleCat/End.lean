/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.LieModuleCat.Basic
public import MathlibExt.CategoryTheory.Preadditive.FunctorEnd

/-!
# Endomorphism actions on Lie modules

A linear representation of a coefficient ring that commutes with the Lie
action defines an action by endomorphisms in the category of Lie modules.
Scalar-algebra representations are bundled in the same way.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w z

namespace LieModuleCat

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]
  (X : LieModuleCat.{w} R L) {S : Type z} [Ring S]

/-- Commuting coefficient endomorphisms form an action in the native
Lie-module category. -/
def endRingHomOfLinearAction (ρ : S →+* Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆) : S →+* End X where
  toFun s := End.of { ρ s with map_lie' := fun {x m} => hρ s x m }
  map_one' := by
    apply End.ext
    apply LieModuleHom.ext
    intro m
    change ρ 1 m = m
    rw [map_one]
    rfl
  map_mul' s t := by
    apply End.ext
    apply LieModuleHom.ext
    intro m
    change ρ (s * t) m = ρ s (ρ t m)
    rw [map_mul]
    rfl
  map_zero' := by
    apply End.ext
    apply LieModuleHom.ext
    intro m
    change ρ 0 m = 0
    rw [map_zero]
    rfl
  map_add' s t := by
    apply End.ext
    apply LieModuleHom.ext
    intro m
    change ρ (s + t) m = ρ s m + ρ t m
    rw [map_add]
    rfl

@[simp]
theorem endRingHomOfLinearAction_apply (ρ : S →+* Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆) (s : S) (m : X) :
    ((endRingHomOfLinearAction R L X ρ hρ s).asHom) m = ρ s m := rfl

variable [Algebra R S]

/-- A scalar algebra action commuting with the Lie action is the same scalar algebra
representation on the native Lie-module object. -/
def endAlgHomOfLinearAction (ρ : S →ₐ[R] Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆) : S →ₐ[R] End X :=
  { endRingHomOfLinearAction R L X ρ.toRingHom hρ with
    commutes' := by
      intro r
      apply End.ext
      apply LieModuleHom.ext
      intro m
      change ρ (algebraMap R S r) m = r • m
      rw [ρ.commutes]
      rfl }

@[simp]
theorem endAlgHomOfLinearAction_apply (ρ : S →ₐ[R] Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆) (s : S) (m : X) :
    ((endAlgHomOfLinearAction R L X ρ hρ s).asHom) m = ρ s m := rfl

end LieModuleCat
