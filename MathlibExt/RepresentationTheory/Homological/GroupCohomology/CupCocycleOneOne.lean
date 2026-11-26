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
# Cup of two degree-one group cocycle representatives

Let k be a commutative ring, G a group and A,B k-linear representations.
For functions x : G → A and y : G → B, the inhomogeneous cup cochain is
(x ∪ y)(g,h)=x(g) ⊗[k] (g • y(h)).

If x and y are one-cocycles, this is a two-cocycle in the diagonal tensor
representation A ⊗[k] B. The construction is k-linear in each cocycle
variable, and composing with the two-cocycle quotient gives its H² class
for the specified representatives. The domain consists of the chosen
degree-one cocycle representatives.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
variable (A B : Rep k G)

/-- Let k be a commutative ring, G a group and A,B k-linear
representations. For arbitrary functions x : G → A and y : G → B,
the degree-(1,1) cup cochain has value
(g,h) ↦ x(g) ⊗[k] (g • y(h)) in A ⊗[k] B. -/
def cupCochainOneOne (x : G → A) (y : G → B) :
    G × G → (A ⊗ B : Rep k G) :=
  fun gh ↦ x gh.1 ⊗ₜ[k] B.ρ gh.1 (y gh.2)

@[simp]
theorem cupCochainOneOne_apply (x : G → A) (y : G → B) (g h : G) :
    cupCochainOneOne A B x y (g, h) = x g ⊗ₜ[k] B.ρ g (y h) :=
  rfl

/-- Let k be a commutative ring, G a group and A,B representations.
For one-cocycles x and y, the cochain
z(g,h)=x(g) ⊗[k] (g • y(h)) satisfies the two-cocycle equation
g • z(h,l)-z(gh,l)+z(g,hl)-z(g,h)=0. -/
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

/-- For representations A,B of a group G over a commutative ring k,
the cup gives the curried k-bilinear map
Z¹(G,A) →ₗ[k] Z¹(G,B) →ₗ[k] Z²(G,A ⊗[k] B),
with value (x,y) ↦ ((g,h) ↦ x(g) ⊗ (g • y(h))). -/
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

/-- For representations A,B of a group G over a commutative ring k,
the representative-level cup followed by the degree-two quotient gives
Z¹(G,A) →ₗ[k] Z¹(G,B) →ₗ[k] H²(G,A ⊗[k] B).
It sends the chosen pair (x,y) to the class of their cup two-cocycle. -/
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
