/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThree

/-!
# Cup products of one- and two-cocycles

Let `G` be a group and `k` a commutative ring in the same universe, and let `A,B` be
`k`-representations of `G`. The inhomogeneous formula `(x ∪ y)(g,h,j) = x(g) ⊗ g·y(h,j)` gives
a bilinear map `Z¹(G,A) × Z²(G,B) → Z³(G,A ⊗ B)`. Composing with the projection of
three-cocycles gives a bilinear map to `H³(G,A ⊗ B)` on these chosen representatives.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

universe u

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
variable (A B : Rep k G)

/-- For representations `A,B` of a group `G` over a commutative ring `k`, functions `x : G → A`
and `y : G × G → B` determine the three-cochain `cupCochainOneTwo A B x y`, with value
`(g,h,j) ↦ x(g) ⊗ₜ[k] B.ρ g (y(h,j))`. -/
def cupCochainOneTwo (x : G → A) (y : G × G → B) :
    G × G × G → (A ⊗ B : Rep k G) :=
  fun p => x p.1 ⊗ₜ[k] B.ρ p.1 (y (p.2.1, p.2.2))

@[simp]
theorem cupCochainOneTwo_apply (x : G → A) (y : G × G → B)
    (g h j : G) :
    cupCochainOneTwo A B x y (g, h, j) =
      x g ⊗ₜ[k] B.ρ g (y (h, j)) :=
  rfl

/-- Let `A,B` be representations of a group `G` over a commutative ring `k`. If `x ∈ Z¹(G,A)` and
`y ∈ Z²(G,B)`, then `z(g,h,j) = x(g) ⊗ₜ[k] g·y(h,j)` belongs to `Z³(G,A ⊗ B)`. Its
inhomogeneous differential is `g·z(h,i,j) - z(gh,i,j) + z(g,hi,j) - z(g,h,ij) + z(g,h,i) = 0`. -/
theorem cupCochainOneTwo_mem_cocycles₃
    (x : cocycles₁ A) (y : cocycles₂ B) :
    cupCochainOneTwo A B x y ∈ cocycles₃ (A ⊗ B) := by
  rw [mem_cocycles₃_def]
  intro g h i j
  simp only [cupCochainOneTwo_apply]
  rw [(mem_cocycles₁_iff x).1 x.2 g h]
  have hy := (mem_cocycles₂_def y).1 y.2 h i j
  have hAction :
      ((A.ρ.tprod B.ρ) g)
          (x h ⊗ₜ[k] B.ρ h (y (i, j))) =
        A.ρ g (x h) ⊗ₜ[k] B.ρ g (B.ρ h (y (i, j))) := by
    change TensorProduct.map (A.ρ g) (B.ρ g)
      (x h ⊗ₜ[k] B.ρ h (y (i, j))) = _
    rw [TensorProduct.map_tmul]
  change ((A ⊗ B : Rep k G).ρ g)
      (x h ⊗ₜ[k] B.ρ h (y (i, j))) = _ at hAction
  rw [hAction, TensorProduct.add_tmul, map_mul B.ρ g h,
    Module.End.mul_apply]
  calc
    _ = -(x g ⊗ₜ[k] B.ρ g
        (B.ρ h (y (i, j)) - y (h * i, j) +
          y (h, i * j) - y (h, i))) := by
      rw [map_sub, map_add, map_sub, TensorProduct.tmul_sub,
        TensorProduct.tmul_add, TensorProduct.tmul_sub]
      abel
    _ = -(x g ⊗ₜ[k] B.ρ g 0) := congrArg
      (fun q => -(x g ⊗ₜ[k] B.ρ g q)) hy
    _ = 0 := by simp

/-- For representations `A,B` of a group `G` over a commutative ring `k`, the `k`-bilinear map
`Z¹(G,A) →ₗ[k] Z²(G,B) →ₗ[k] Z³(G,A ⊗ B)` sends `(x,y)` to the cocycle `(g,h,j) ↦ x(g) ⊗ₜ[k]
g·y(h,j)`. -/
def cupCocycleOneTwo :
    cocycles₁ A →ₗ[k] cocycles₂ B →ₗ[k] cocycles₃ (A ⊗ B) where
  toFun x :=
    { toFun := fun y =>
        ⟨cupCochainOneTwo A B x y,
          cupCochainOneTwo_mem_cocycles₃ A B x y⟩
      map_add' := fun y z => by
        apply cocycles₃_ext
        intro g h j
        change x g ⊗ₜ[k] B.ρ g (y (h, j) + z (h, j)) = _
        rw [map_add, TensorProduct.tmul_add]
        rfl
      map_smul' := fun r y => by
        apply cocycles₃_ext
        intro g h j
        change x g ⊗ₜ[k] B.ρ g (r • y (h, j)) =
          r • (x g ⊗ₜ[k] B.ρ g (y (h, j)))
        rw [map_smul, TensorProduct.tmul_smul] }
  map_add' := fun x y => by
    ext z g h j
    change (x g + y g) ⊗ₜ[k] B.ρ g (z (h, j)) = _
    rw [TensorProduct.add_tmul]
    rfl
  map_smul' := fun r x => by
    ext y g h j
    change (r • x g) ⊗ₜ[k] B.ρ g (y (h, j)) =
      r • (x g ⊗ₜ[k] B.ρ g (y (h, j)))
    exact (TensorProduct.smul_tmul' r (x g) (B.ρ g (y (h, j)))).symm

@[simp]
theorem cupCocycleOneTwo_apply
    (x : cocycles₁ A) (y : cocycles₂ B) (g h j : G) :
    cupCocycleOneTwo A B x y (g, h, j) =
      x g ⊗ₜ[k] B.ρ g (y (h, j)) :=
  rfl

/-- For representations `A,B` of a group `G` over a commutative ring `k`, the bilinear map
`Z¹(G,A) →ₗ[k] Z²(G,B) →ₗ[k] H³(G,A ⊗ B)` sends `(x,y)` to `H3π (A ⊗ B) (cupCocycleOneTwo A B
x y)`, the class of `(g,h,j) ↦ x(g) ⊗ₜ[k] g·y(h,j)`. -/
def cupCocycleOneTwoClass :
    cocycles₁ A →ₗ[k] cocycles₂ B →ₗ[k] H3 (A ⊗ B) where
  toFun x := (H3π (A ⊗ B)).hom.comp (cupCocycleOneTwo A B x)
  map_add' := fun x y => by ext z; simp
  map_smul' := fun r x => by ext y; simp

@[simp]
theorem cupCocycleOneTwoClass_apply
    (x : cocycles₁ A) (y : cocycles₂ B) :
    cupCocycleOneTwoClass A B x y =
      H3π (A ⊗ B) (cupCocycleOneTwo A B x y) :=
  rfl

end groupCohomology
