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
# Coefficient actions by Lie-module endomorphisms

Let `R` be a commutative ring, `L` an `R`-Lie algebra, and `X` a left `L`-module. A ring
representation `ρ : S → End_R(X)` satisfying `ρ(s)([x,m]) = [x,ρ(s)(m)]` takes values in the
ring of Lie-module endomorphisms of `X`.

If `S` is also an `R`-algebra and `ρ` is an `R`-algebra homomorphism, the induced endomorphism
representation is an `R`-algebra homomorphism. Both constructions act on `m ∈ X` by `ρ(s)(m)`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w z

namespace LieModuleCat

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]
  (X : LieModuleCat.{w} R L) {S : Type z} [Ring S]

/-- A commuting ring action by Lie-module endomorphisms.

For `ρ : S →+* End_R(X)` with `ρ(s)([x,m]) = [x,ρ(s)(m)]`, this is the induced ring
homomorphism `S →+* End(X)` in the category of left `L`-modules. -/
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

/-- The value of a commuting ring endomorphism action.

For `s ∈ S` and `m ∈ X`, the categorical Lie-module endomorphism induced by `ρ(s)` has value
`ρ(s)(m)`. -/
@[simp]
theorem endRingHomOfLinearAction_apply (ρ : S →+* Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆) (s : S) (m : X) :
    ((endRingHomOfLinearAction R L X ρ hρ s).asHom) m = ρ s m := rfl

variable [Algebra R S]

/-- A commuting scalar-algebra action by Lie-module endomorphisms.

For an `R`-algebra `S` and an `R`-algebra representation `ρ : S →ₐ[R] End_R(X)` commuting with
the `L`-action, this is the induced `R`-algebra homomorphism to the categorical endomorphism
algebra of `X`. -/
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

/-- The value of a commuting algebra endomorphism action.

For `s ∈ S` and `m ∈ X`, the Lie-module endomorphism obtained from the commuting algebra
representation has value `ρ(s)(m)`. -/
@[simp]
theorem endAlgHomOfLinearAction_apply (ρ : S →ₐ[R] Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆) (s : S) (m : X) :
    ((endAlgHomOfLinearAction R L X ρ hρ s).asHom) m = ρ s m := rfl

end LieModuleCat
