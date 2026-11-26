/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupCocycleOneTwo
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Cup products of degree-one and degree-two classes

Let `G` be a group, `k` a commutative ring, and `A,B` representations. The cocycle formula `(x
∪ y)(g,h,j) = x(g) ⊗ g·y(h,j)` descends to a bilinear map `H¹(G,A) × H²(G,B) → H³(G,A ⊗ B)`.

For a two-cocycle `y`, `(d⁰a) ∪ y = d²((g,h) ↦ a ⊗ y(g,h))`. For a one-cocycle `x` and a
one-cochain `b`, `x ∪ (d¹b) = d²((g,h) ↦ -(x(g) ⊗ g·b(h)))`. These identities make the cup
class independent of both representatives.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

universe u

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
variable (A B : Rep k G)

/-- Let `A,B` be representations of a group `G` over a commutative ring `k`, `a : A`, and `y ∈
Z²(G,B)`. Then `cupCochainOneTwo A B (d₀₁ A a) y = d₂₃ (A ⊗ B) (fun (g,h) => a ⊗ₜ[k] y(g,h))`.
Here `d⁰a(g) = g·a - a` and `d²t(g,h,j) = g·t(h,j) - t(gh,j) + t(g,hj) - t(g,h)`. -/
theorem cupCochainOneTwo_d₀₁_left
    (a : A) (y : cocycles₂ B) :
    cupCochainOneTwo A B (d₀₁ A a) y =
      d₂₃ (A ⊗ B) (fun p => a ⊗ₜ[k] y p) := by
  funext p
  rcases p with ⟨g, h, j⟩
  change (A.ρ g a - a) ⊗ₜ[k] B.ρ g (y (h, j)) =
    (A.ρ.tprod B.ρ) g (a ⊗ₜ[k] y (h, j)) -
      a ⊗ₜ[k] y (g * h, j) + a ⊗ₜ[k] y (g, h * j) -
      a ⊗ₜ[k] y (g, h)
  have hAction :
      (A.ρ.tprod B.ρ) g (a ⊗ₜ[k] y (h, j)) =
        A.ρ g a ⊗ₜ[k] B.ρ g (y (h, j)) := by
    change TensorProduct.map (A.ρ g) (B.ρ g)
      (a ⊗ₜ[k] y (h, j)) = _
    rw [TensorProduct.map_tmul]
  rw [TensorProduct.sub_tmul, hAction]
  have hy := (mem_cocycles₂_def y).1 y.2 g h j
  have hy' : B.ρ g (y (h, j)) =
      y (g * h, j) - y (g, h * j) + y (g, h) := by
    rw [← sub_eq_zero]
    calc
      _ = B.ρ g (y (h, j)) - y (g * h, j) +
          y (g, h * j) - y (g, h) := by abel
      _ = 0 := hy
  rw [hy']
  simp only [TensorProduct.tmul_add, TensorProduct.tmul_sub]
  abel

/-- Let `A,B` be representations of a group `G` over a commutative ring `k`, `x ∈ Z¹(G,A)`, and `b
: G → B` an arbitrary one-cochain. Then `x ∪ d¹b = d²((g,h) ↦ -(x(g) ⊗ₜ[k] g·b(h)))`, where
`d¹b(g,h) = g·b(h) - b(gh) + b(g)` and `d²t(g,h,j) = g·t(h,j) - t(gh,j) + t(g,hj) - t(g,h)`. -/
theorem cupCochainOneTwo_d₁₂_right
    (x : cocycles₁ A) (b : G → B) :
    cupCochainOneTwo A B x (d₁₂ B b) =
      d₂₃ (A ⊗ B)
        (fun p => -(x p.1 ⊗ₜ[k] B.ρ p.1 (b p.2))) := by
  funext p
  rcases p with ⟨g, h, j⟩
  change x g ⊗ₜ[k] B.ρ g
      (B.ρ h (b j) - b (h * j) + b h) =
    (A.ρ.tprod B.ρ) g (-(x h ⊗ₜ[k] B.ρ h (b j))) -
      (-(x (g * h) ⊗ₜ[k] B.ρ (g * h) (b j))) +
      (-(x g ⊗ₜ[k] B.ρ g (b (h * j)))) -
      (-(x g ⊗ₜ[k] B.ρ g (b h)))
  have hAction :
      (A.ρ.tprod B.ρ) g (-(x h ⊗ₜ[k] B.ρ h (b j))) =
        -(A.ρ g (x h) ⊗ₜ[k] B.ρ g (B.ρ h (b j))) := by
    rw [map_neg]
    change -TensorProduct.map (A.ρ g) (B.ρ g)
      (x h ⊗ₜ[k] B.ρ h (b j)) = _
    rw [TensorProduct.map_tmul]
  rw [hAction,
    (mem_cocycles₁_iff x).1 x.2 g h,
    map_mul B.ρ g h, Module.End.mul_apply]
  simp only [map_add, map_sub, TensorProduct.tmul_sub,
    TensorProduct.tmul_add, TensorProduct.add_tmul]
  abel

/-- For representations `A,B` of a group `G` over a commutative ring `k`, `ker (H1π A) ≤ ker
(cupCocycleOneTwoClass A B)`. Thus any one-cocycle `x` with zero class in `H¹(G,A)` has `[x ∪
y] = 0` in `H³(G,A ⊗ B)` for every two-cocycle `y ∈ Z²(G,B)`. -/
theorem cupCocycleOneTwoClass_ker_left :
    LinearMap.ker (H1π A).hom ≤
      LinearMap.ker (cupCocycleOneTwoClass A B) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  apply LinearMap.ext
  intro y
  change H3π (A ⊗ B) (cupCocycleOneTwo A B x y) = 0
  apply (H3π_eq_zero_iff _).2
  have hxb : (x : G → A) ∈ coboundaries₁ A :=
    (H1π_eq_zero_iff x).1 hx
  rcases hxb with ⟨a, ha⟩
  have hxEq : x = ⟨d₀₁ A a, d₀₁_apply_mem_cocycles₁ a⟩ := by
    apply cocycles₁_ext
    intro g
    exact congrFun ha.symm g
  rw [hxEq]
  refine ⟨fun p => a ⊗ₜ[k] y p, ?_⟩
  exact (cupCochainOneTwo_d₀₁_left A B a y).symm

/-- For representations `A,B` of a group `G` over a commutative ring `k`, `ker (H2π B) ≤ ker
(cupCocycleOneTwoClass A B).flip`. Thus any two-cocycle `y` with zero class in `H²(G,B)` has
`[x ∪ y] = 0` in `H³(G,A ⊗ B)` for every one-cocycle `x ∈ Z¹(G,A)`. -/
theorem cupCocycleOneTwoClass_ker_right :
    LinearMap.ker (H2π B).hom ≤
      LinearMap.ker (cupCocycleOneTwoClass A B).flip := by
  intro y hy
  rw [LinearMap.mem_ker] at hy ⊢
  apply LinearMap.ext
  intro x
  change H3π (A ⊗ B) (cupCocycleOneTwo A B x y) = 0
  apply (H3π_eq_zero_iff _).2
  have hyb : (y : G × G → B) ∈ coboundaries₂ B :=
    (H2π_eq_zero_iff y).1 hy
  rcases hyb with ⟨b, hb⟩
  have hyEq : y = ⟨d₁₂ B b, d₁₂_apply_mem_cocycles₂ b⟩ := by
    apply cocycles₂_ext
    intro g h
    exact congrFun hb.symm (g, h)
  rw [hyEq]
  refine ⟨fun p => -(x p.1 ⊗ₜ[k] B.ρ p.1 (b p.2)), ?_⟩
  exact (cupCochainOneTwo_d₁₂_right A B x b).symm

/-- For representations `A,B` of a group `G` over a commutative ring `k`, the bilinear map
`H¹(G,A) →ₗ[k] H²(G,B) →ₗ[k] H³(G,A ⊗ B)` sends the classes of a one-cocycle `x` and a
two-cocycle `y` to the class of `(g,h,j) ↦ x(g) ⊗ₜ[k] g·y(h,j)`. -/
noncomputable def cupOneTwo :
    H1 A →ₗ[k] H2 B →ₗ[k] H3 (A ⊗ B) :=
  let q := LinearMap.liftQ₂
    (LinearMap.ker (H1π A).hom)
    (LinearMap.ker (H2π B).hom)
    (cupCocycleOneTwoClass A B)
    (cupCocycleOneTwoClass_ker_left A B)
    (cupCocycleOneTwoClass_ker_right A B)
  let eA := (H1π A).hom.quotKerEquivOfSurjective
    ((ModuleCat.epi_iff_surjective (H1π A)).1 inferInstance)
  let eB := (H2π B).hom.quotKerEquivOfSurjective
    ((ModuleCat.epi_iff_surjective (H2π B)).1 inferInstance)
  { toFun := fun x => (q (eA.symm x)).comp eB.symm.toLinearMap
    map_add' := fun x y => by ext z; simp
    map_smul' := fun r x => by ext y; simp }

/-- Let `A,B` be representations of a group `G` over a commutative ring `k`, `x ∈ Z¹(G,A)`, and `y
∈ Z²(G,B)`. Then `cupOneTwo A B (H1π A x) (H2π B y) = H3π (A ⊗ B) (cupCocycleOneTwo A B x y)`,
the class of `(g,h,j) ↦ x(g) ⊗ₜ[k] g·y(h,j)`. -/
@[simp]
theorem cupOneTwo_H1π_H2π
    (x : cocycles₁ A) (y : cocycles₂ B) :
    cupOneTwo A B (H1π A x) (H2π B y) =
      H3π (A ⊗ B) (cupCocycleOneTwo A B x y) := by
  change LinearMap.liftQ₂
      (LinearMap.ker (H1π A).hom)
      (LinearMap.ker (H2π B).hom)
      (cupCocycleOneTwoClass A B)
      (cupCocycleOneTwoClass_ker_left A B)
      (cupCocycleOneTwoClass_ker_right A B)
      (((H1π A).hom.quotKerEquivOfSurjective
        ((ModuleCat.epi_iff_surjective (H1π A)).1 inferInstance)).symm
          (H1π A x))
      (((H2π B).hom.quotKerEquivOfSurjective
        ((ModuleCat.epi_iff_surjective (H2π B)).1 inferInstance)).symm
          (H2π B y)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

end groupCohomology
