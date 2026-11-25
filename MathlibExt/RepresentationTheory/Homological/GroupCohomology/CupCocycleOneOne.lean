/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# The cup product of two degree-one group cocycles

For two `k`-linear representations `A` and `B` of a group `G`, this file
constructs the standard inhomogeneous representative-level cup product

`(x ∪ y)(g, h) = x(g) ⊗ g · y(h)`.

The formula is proved to be a two-cocycle when `x` and `y` are one-cocycles,
and is packaged as a curried `k`-linear map.  We also record its image under
the quotient map to `H²` for chosen cocycle representatives.

This file does not prove that the construction descends to a bilinear map on
`H¹` classes.  It makes no claim about continuous or étale cohomology,
comparison maps, norm-residue maps, or the Bloch--Kato theorem.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
variable (A B : Rep k G)

/-- The inhomogeneous degree-`(1, 1)` cup-product cochain. -/
def cupCochainOneOne (x : G → A) (y : G → B) :
    G × G → (A ⊗ B : Rep k G) :=
  fun gh ↦ x gh.1 ⊗ₜ[k] B.ρ gh.1 (y gh.2)

@[simp]
theorem cupCochainOneOne_apply (x : G → A) (y : G → B) (g h : G) :
    cupCochainOneOne A B x y (g, h) = x g ⊗ₜ[k] B.ρ g (y h) :=
  rfl

/-- The cup-product cochain of two one-cocycles is a two-cocycle. -/
theorem cupCochainOneOne_mem_cocycles₂
    (x : cocycles₁ A) (y : cocycles₁ B) :
    cupCochainOneOne A B x y ∈ cocycles₂ (A ⊗ B) := by
  rw [mem_cocycles₂_iff]
  intro g h j
  simp only [cupCochainOneOne_apply]
  rw [(mem_cocycles₁_iff x).1 x.2 g h,
    (mem_cocycles₁_iff y).1 y.2 h j]
  simp only [Rep.tensor_ρ, map_mul, Module.End.mul_apply, map_add,
    TensorProduct.add_tmul, TensorProduct.tmul_add]
  have hTensorAction :
      ((A.ρ.tprod B.ρ) g) (x h ⊗ₜ[k] B.ρ h (y j)) =
        A.ρ g (x h) ⊗ₜ[k] B.ρ g (B.ρ h (y j)) := by
    change TensorProduct.map (A.ρ g) (B.ρ g)
      (x h ⊗ₜ[k] B.ρ h (y j)) = _
    rw [TensorProduct.map_tmul]
  rw [hTensorAction]
  abel

/-- The representative-level degree-`(1, 1)` cup product, linear in each
one-cocycle variable. -/
def cupCocycleOneOne :
    cocycles₁ A →ₗ[k] cocycles₁ B →ₗ[k] cocycles₂ (A ⊗ B) where
  toFun x :=
    { toFun := fun y ↦
        ⟨cupCochainOneOne A B x y,
          cupCochainOneOne_mem_cocycles₂ A B x y⟩
      map_add' := fun y z ↦ by
        apply cocycles₂_ext
        intro g h
        change cupCochainOneOne A B x (y + z) (g, h) =
          cupCochainOneOne A B x y (g, h) +
            cupCochainOneOne A B x z (g, h)
        change x g ⊗ₜ[k] B.ρ g (y h + z h) =
          x g ⊗ₜ[k] B.ρ g (y h) + x g ⊗ₜ[k] B.ρ g (z h)
        rw [map_add, TensorProduct.tmul_add]
      map_smul' := fun r y ↦ by
        apply cocycles₂_ext
        intro g h
        change cupCochainOneOne A B x (r • y) (g, h) =
          r • cupCochainOneOne A B x y (g, h)
        change x g ⊗ₜ[k] B.ρ g (r • y h) =
          r • (x g ⊗ₜ[k] B.ρ g (y h))
        rw [map_smul, TensorProduct.tmul_smul] }
  map_add' := fun x y ↦ by
    ext z g h
    change cupCochainOneOne A B (x + y) z (g, h) =
      cupCochainOneOne A B x z (g, h) +
        cupCochainOneOne A B y z (g, h)
    change (x g + y g) ⊗ₜ[k] B.ρ g (z h) =
      x g ⊗ₜ[k] B.ρ g (z h) + y g ⊗ₜ[k] B.ρ g (z h)
    rw [TensorProduct.add_tmul]
  map_smul' := fun r x ↦ by
    ext y g h
    change cupCochainOneOne A B (r • x) y (g, h) =
      r • cupCochainOneOne A B x y (g, h)
    change (r • x g) ⊗ₜ[k] B.ρ g (y h) =
      r • (x g ⊗ₜ[k] B.ρ g (y h))
    exact (TensorProduct.smul_tmul' r (x g) (B.ρ g (y h))).symm

@[simp]
theorem cupCocycleOneOne_apply
    (x : cocycles₁ A) (y : cocycles₁ B) (g h : G) :
    cupCocycleOneOne A B x y (g, h) =
      x g ⊗ₜ[k] B.ρ g (y h) :=
  rfl

/-- The `H²` class of the cup-product cocycle of two chosen one-cocycle
representatives.  No descent through the quotient maps to `H¹` is asserted. -/
def cupCocycleOneOneClass :
    cocycles₁ A →ₗ[k] cocycles₁ B →ₗ[k] H2 (A ⊗ B) where
  toFun x := (H2π (A ⊗ B)).hom.comp (cupCocycleOneOne A B x)
  map_add' := fun x y ↦ by
    ext z
    simp
  map_smul' := fun r x ↦ by
    ext y
    simp

@[simp]
theorem cupCocycleOneOneClass_apply
    (x : cocycles₁ A) (y : cocycles₁ B) :
    cupCocycleOneOneClass A B x y =
      H2π (A ⊗ B) (cupCocycleOneOne A B x y) :=
  rfl

end groupCohomology
