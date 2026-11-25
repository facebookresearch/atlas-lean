/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupCocycleOneOne
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# The descended degree-`(1, 1)` cup product

For a discrete group `G` (in particular, for a finite group) and two
`k`-linear representations `A` and `B`, this file descends the representative
cocycle formula

`(x ∪ y)(g, h) = x(g) ⊗ g · y(h)`

through both degree-one quotient maps.  The result is a genuine bilinear map
`H¹(G, A) →ₗ[k] H¹(G, B) →ₗ[k] H²(G, A ⊗ B)`.  The two
coboundary formulas used for the descent are recorded explicitly.

Nonclaims: no continuous or étale cohomology, no comparison map, no Kummer
map, no norm-residue map, and no Bloch--Kato theorem.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
variable (A B : Rep k G)

/-- Replacing the left one-cocycle by the coboundary of `a` changes the cup
representative to the coboundary of `g ↦ a ⊗ y(g)`. -/
theorem cupCochainOneOne_d₀₁_left
    (a : A) (y : cocycles₁ B) :
    cupCochainOneOne A B (d₀₁ A a) y =
      d₁₂ (A ⊗ B) (fun g ↦ a ⊗ₜ[k] y g) := by
  funext gh
  rcases gh with ⟨g, h⟩
  change (A.ρ g a - a) ⊗ₜ[k] B.ρ g (y h) =
    (A.ρ.tprod B.ρ) g (a ⊗ₜ[k] y h) -
      a ⊗ₜ[k] y (g * h) + a ⊗ₜ[k] y g
  have hAction :
      (A.ρ.tprod B.ρ) g (a ⊗ₜ[k] y h) =
        A.ρ g a ⊗ₜ[k] B.ρ g (y h) := by
    change TensorProduct.map (A.ρ g) (B.ρ g) (a ⊗ₜ[k] y h) = _
    rw [TensorProduct.map_tmul]
  rw [TensorProduct.sub_tmul, hAction,
    (mem_cocycles₁_iff y).1 y.2 g h, TensorProduct.tmul_add]
  abel

/-- Replacing the right one-cocycle by the coboundary of `b` changes the cup
representative to the coboundary of `g ↦ -(x(g) ⊗ g · b)`. -/
theorem cupCochainOneOne_d₀₁_right
    (x : cocycles₁ A) (b : B) :
    cupCochainOneOne A B x (d₀₁ B b) =
      d₁₂ (A ⊗ B) (fun g ↦ -(x g ⊗ₜ[k] B.ρ g b)) := by
  funext gh
  rcases gh with ⟨g, h⟩
  change x g ⊗ₜ[k] B.ρ g (B.ρ h b - b) =
    (A.ρ.tprod B.ρ) g (-(x h ⊗ₜ[k] B.ρ h b)) -
      (-(x (g * h) ⊗ₜ[k] B.ρ (g * h) b)) +
        (-(x g ⊗ₜ[k] B.ρ g b))
  have hAction :
      (A.ρ.tprod B.ρ) g (-(x h ⊗ₜ[k] B.ρ h b)) =
        -(A.ρ g (x h) ⊗ₜ[k] B.ρ g (B.ρ h b)) := by
    rw [map_neg]
    change -TensorProduct.map (A.ρ g) (B.ρ g)
      (x h ⊗ₜ[k] B.ρ h b) = _
    rw [TensorProduct.map_tmul]
  rw [map_sub, TensorProduct.tmul_sub,
    hAction, (mem_cocycles₁_iff x).1 x.2 g h, map_mul B.ρ g h,
    Module.End.mul_apply, TensorProduct.add_tmul]
  abel

/-- The representative cup class annihilates the kernel of `H1π` in its
left variable. -/
theorem cupCocycleOneOneClass_ker_left :
    LinearMap.ker (H1π A).hom ≤
      LinearMap.ker (cupCocycleOneOneClass A B) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  apply LinearMap.ext
  intro y
  change H2π (A ⊗ B) (cupCocycleOneOne A B x y) = 0
  apply (H2π_eq_zero_iff _).2
  have hxb : (x : G → A) ∈ coboundaries₁ A :=
    (H1π_eq_zero_iff x).1 hx
  rcases hxb with ⟨a, ha⟩
  have hxEq : x = ⟨d₀₁ A a, d₀₁_apply_mem_cocycles₁ a⟩ := by
    apply cocycles₁_ext
    intro g
    exact congrFun ha.symm g
  rw [hxEq]
  refine ⟨fun g ↦ a ⊗ₜ[k] y g, ?_⟩
  change d₁₂ (A ⊗ B) (fun g ↦ a ⊗ₜ[k] y g) =
    cupCochainOneOne A B (d₀₁ A a) y
  exact (cupCochainOneOne_d₀₁_left A B a y).symm

/-- The representative cup class annihilates the kernel of `H1π` in its
right variable. -/
theorem cupCocycleOneOneClass_ker_right :
    LinearMap.ker (H1π B).hom ≤
      LinearMap.ker (cupCocycleOneOneClass A B).flip := by
  intro y hy
  rw [LinearMap.mem_ker] at hy ⊢
  apply LinearMap.ext
  intro x
  change H2π (A ⊗ B) (cupCocycleOneOne A B x y) = 0
  apply (H2π_eq_zero_iff _).2
  have hyb : (y : G → B) ∈ coboundaries₁ B :=
    (H1π_eq_zero_iff y).1 hy
  rcases hyb with ⟨b, hb⟩
  have hyEq : y = ⟨d₀₁ B b, d₀₁_apply_mem_cocycles₁ b⟩ := by
    apply cocycles₁_ext
    intro g
    exact congrFun hb.symm g
  rw [hyEq]
  refine ⟨fun g ↦ -(x g ⊗ₜ[k] B.ρ g b), ?_⟩
  change d₁₂ (A ⊗ B) (fun g ↦ -(x g ⊗ₜ[k] B.ρ g b)) =
    cupCochainOneOne A B x (d₀₁ B b)
  exact (cupCochainOneOne_d₀₁_right A B x b).symm

/-- The degree-`(1, 1)` cup product on genuine group-cohomology classes. -/
noncomputable def cupOneOne :
    H1 A →ₗ[k] H1 B →ₗ[k] H2 (A ⊗ B) :=
  let q := LinearMap.liftQ₂
    (LinearMap.ker (H1π A).hom)
    (LinearMap.ker (H1π B).hom)
    (cupCocycleOneOneClass A B)
    (cupCocycleOneOneClass_ker_left A B)
    (cupCocycleOneOneClass_ker_right A B)
  let eA := (H1π A).hom.quotKerEquivOfSurjective
    ((ModuleCat.epi_iff_surjective (H1π A)).1 inferInstance)
  let eB := (H1π B).hom.quotKerEquivOfSurjective
    ((ModuleCat.epi_iff_surjective (H1π B)).1 inferInstance)
  { toFun := fun x ↦ (q (eA.symm x)).comp eB.symm.toLinearMap
    map_add' := fun x y ↦ by
      ext z
      simp
    map_smul' := fun r x ↦ by
      ext z
      simp }

/-- The descended cup product computes as the representative cup cocycle
followed by `H2π` on classes presented by `H1π`. -/
@[simp]
theorem cupOneOne_H1π_H1π
    (x : cocycles₁ A) (y : cocycles₁ B) :
    cupOneOne A B (H1π A x) (H1π B y) =
      H2π (A ⊗ B) (cupCocycleOneOne A B x y) := by
  change LinearMap.liftQ₂
      (LinearMap.ker (H1π A).hom)
      (LinearMap.ker (H1π B).hom)
      (cupCocycleOneOneClass A B)
      (cupCocycleOneOneClass_ker_left A B)
      (cupCocycleOneOneClass_ker_right A B)
      (((H1π A).hom.quotKerEquivOfSurjective
        ((ModuleCat.epi_iff_surjective (H1π A)).1 inferInstance)).symm
          (H1π A x))
      (((H1π B).hom.quotKerEquivOfSurjective
        ((ModuleCat.epi_iff_surjective (H1π B)).1 inferInstance)).symm
          (H1π B y)) =
    H2π (A ⊗ B) (cupCocycleOneOne A B x y)
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

end groupCohomology
