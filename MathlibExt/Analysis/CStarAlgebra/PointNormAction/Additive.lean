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

public import MathlibExt.Analysis.CStarAlgebra.PointNormAction
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Additive point-norm actions on C-star algebras

Additive point-norm actions are the definitional specialization of
`PointNormCStarAction` to `Multiplicative G`.  This supplies additive notation
without introducing a second action carrier or any ambient action instances.
-/

@[expose] public section

open scoped CStarAlgebra

universe uG uH uA uB uC uD uX

noncomputable section

/-- Let `G` be an additive monoid equipped with a topology, and let `A` be possibly nonunital
complex C*-algebras. Specify actions by star-algebra automorphisms with continuous coefficient
orbits in the norm topology.

A point-norm continuous additive action, definitionally represented as a multiplicative action
of `Multiplicative G`. -/
abbrev PointNormCStarAddAction
    (G : Type uG) (A : Type uA)
    [AddMonoid G] [TopologicalSpace G] [NonUnitalCStarAlgebra A] :=
  PointNormCStarAction (Multiplicative G) A

namespace PointNormCStarAddAction

variable {G : Type uG} {H : Type uH}
variable {A : Type uA} {B : Type uB}
variable [TopologicalSpace G] [TopologicalSpace H]
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

section AddMonoid

variable [AddMonoid G]

/-- Let `G` be an additive monoid equipped with a topology, and let `A` be possibly nonunital
complex C*-algebras. Specify actions by star-algebra automorphisms with continuous coefficient
orbits in the norm topology.

The automorphism at one additive-monoid element. -/
def aut (α : PointNormCStarAddAction G A) (g : G) : A ≃⋆ₐ[ℂ] A :=
  PointNormCStarAction.aut α (Multiplicative.ofAdd g)

@[simp]
theorem aut_zero (α : PointNormCStarAddAction G A) : α.aut 0 = 1 :=
  PointNormCStarAction.aut_one α

@[simp]
theorem aut_add (α : PointNormCStarAddAction G A) (g h : G) :
    α.aut (g + h) = α.aut g * α.aut h :=
  PointNormCStarAction.aut_mul α g h

@[simp]
theorem apply_zero (α : PointNormCStarAddAction G A) (a : A) : α (0 : G) a = a :=
  PointNormCStarAction.apply_one α a

@[simp]
theorem apply_add (α : PointNormCStarAddAction G A) (g h : G) (a : A) :
    α (g + h) a = α g (α h a) :=
  PointNormCStarAction.apply_mul α g h a

@[simp]
theorem apply_zero_elem (α : PointNormCStarAddAction G A) (g : G) : α g 0 = 0 :=
  PointNormCStarAction.apply_zero α g

@[simp]
theorem apply_add_elem (α : PointNormCStarAddAction G A) (g : G) (a b : A) :
    α g (a + b) = α g a + α g b :=
  PointNormCStarAction.apply_add α g a b

@[simp]
theorem apply_mul_elem (α : PointNormCStarAddAction G A) (g : G) (a b : A) :
    α g (a * b) = α g a * α g b :=
  PointNormCStarAction.apply_mul_elem α g a b

@[simp]
theorem apply_star (α : PointNormCStarAddAction G A) (g : G) (a : A) :
    α g (star a) = star (α g a) :=
  PointNormCStarAction.apply_star α g a

@[simp]
theorem apply_smul (α : PointNormCStarAddAction G A) (g : G) (z : ℂ) (a : A) :
    α g (z • a) = z • α g a :=
  PointNormCStarAction.apply_smul α g z a

theorem norm_apply (α : PointNormCStarAddAction G A) (g : G) (a : A) :
    ‖α g a‖ = ‖a‖ :=
  PointNormCStarAction.norm_apply α g a

theorem dist_apply (α : PointNormCStarAddAction G A) (g : G) (a b : A) :
    dist (α g a) (α g b) = dist a b :=
  PointNormCStarAction.dist_apply α g a b

theorem continuous_apply
    {X : Type uX} [TopologicalSpace X]
    (α : PointNormCStarAddAction G A)
    {g : X → G} {a : X → A}
    (hg : Continuous g) (ha : Continuous a) :
    Continuous fun x ↦ α (g x) (a x) :=
  PointNormCStarAction.continuous_apply α hg ha

theorem continuous_action (α : PointNormCStarAddAction G A) :
    Continuous fun p : G × A ↦ α p.1 p.2 :=
  PointNormCStarAction.continuous_action α

/-! ## Equivariant homomorphisms -/

/-- Let `G` be an additive monoid equipped with a topology, and let `A` and `B` be possibly
nonunital complex C*-algebras. Specify actions by star-algebra automorphisms with continuous
coefficient orbits in the norm topology.

An equivariant homomorphism between additive point-norm actions. -/
abbrev Hom (α : PointNormCStarAddAction G A) (β : PointNormCStarAddAction G B) :=
  PointNormCStarAction.Hom α β

namespace Hom

variable {α : PointNormCStarAddAction G A} {β : PointNormCStarAddAction G B}

@[simp]
theorem equivariant (φ : Hom α β) (g : G) (a : A) :
    φ (α g a) = β g (φ a) :=
  PointNormCStarAction.Hom.equivariant φ g a

/-- Let `G` be an additive monoid equipped with a topology, and let `A` be possibly nonunital
complex C*-algebras. Specify actions by star-algebra automorphisms with continuous coefficient
orbits in the norm topology.

The identity equivariant homomorphism. -/
def id (α : PointNormCStarAddAction G A) : Hom α α :=
  PointNormCStarAction.Hom.id α

@[simp]
theorem id_apply (α : PointNormCStarAddAction G A) (a : A) : id α a = a :=
  PointNormCStarAction.Hom.id_apply α a

/-- Let `G` be an additive monoid equipped with a topology, and let `A`, `B` and `C` be possibly
nonunital complex C*-algebras. Specify actions by star-algebra automorphisms with continuous
coefficient orbits in the norm topology.

Composition of equivariant homomorphisms. -/
def comp {C : Type uC} [NonUnitalCStarAlgebra C]
    {γ : PointNormCStarAddAction G C}
    (ψ : Hom β γ) (φ : Hom α β) : Hom α γ :=
  PointNormCStarAction.Hom.comp ψ φ

@[simp]
theorem comp_apply {C : Type uC} [NonUnitalCStarAlgebra C]
    {γ : PointNormCStarAddAction G C}
    (ψ : Hom β γ) (φ : Hom α β) (a : A) :
    comp ψ φ a = ψ (φ a) :=
  PointNormCStarAction.Hom.comp_apply ψ φ a

@[simp]
theorem id_comp (φ : Hom α β) : comp (id β) φ = φ :=
  PointNormCStarAction.Hom.id_comp φ

@[simp]
theorem comp_id (φ : Hom α β) : comp φ (id α) = φ :=
  PointNormCStarAction.Hom.comp_id φ

theorem comp_assoc
    {C : Type uC} {D : Type uD}
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    {γ : PointNormCStarAddAction G C} {δ : PointNormCStarAddAction G D}
    (χ : Hom γ δ) (ψ : Hom β γ) (φ : Hom α β) :
    comp (comp χ ψ) φ = comp χ (comp ψ φ) :=
  PointNormCStarAction.Hom.comp_assoc χ ψ φ

end Hom

end AddMonoid

section AddGroup

variable [AddGroup G]

@[simp]
theorem aut_neg (α : PointNormCStarAddAction G A) (g : G) :
    α.aut (-g) = (α.aut g)⁻¹ :=
  PointNormCStarAction.aut_inv α g

@[simp]
theorem apply_neg_apply (α : PointNormCStarAddAction G A) (g : G) (a : A) :
    α (-g) (α g a) = a :=
  PointNormCStarAction.apply_inv_apply α g a

@[simp]
theorem apply_apply_neg (α : PointNormCStarAddAction G A) (g : G) (a : A) :
    α g (α (-g) a) = a :=
  PointNormCStarAction.apply_apply_inv α g a

end AddGroup

/-! ## The integer action generated by one automorphism -/

/-- Let `A` and, when present, `B` be possibly nonunital complex C*-algebras with the specified
star-algebra automorphisms. The integer group has its usual discrete topology.

The additive action of `ℤ` generated by a star-algebra automorphism. The generator `1` acts by
`σ`. -/
def integerAction
    {A : Type uA} [NonUnitalCStarAlgebra A]
    (σ : A ≃⋆ₐ[ℂ] A) : PointNormCStarAddAction ℤ A where
  toMonoidHom := zpowersHom (A ≃⋆ₐ[ℂ] A) σ
  continuous_orbit := fun _ ↦ continuous_of_discreteTopology

@[simp]
theorem integerAction_apply
    {A : Type uA} [NonUnitalCStarAlgebra A]
    (σ : A ≃⋆ₐ[ℂ] A) (n : ℤ) (a : A) :
    integerAction σ n a = (σ ^ n) a :=
  rfl

@[simp]
theorem integerAction_zero
    {A : Type uA} [NonUnitalCStarAlgebra A]
    (σ : A ≃⋆ₐ[ℂ] A) (a : A) :
    integerAction σ (0 : ℤ) a = a := by
  rw [integerAction_apply]
  simp

@[simp]
theorem integerAction_one
    {A : Type uA} [NonUnitalCStarAlgebra A]
    (σ : A ≃⋆ₐ[ℂ] A) (a : A) :
    integerAction σ (1 : ℤ) a = σ a := by
  rw [integerAction_apply]
  simp

@[simp]
theorem integerAction_neg_one
    {A : Type uA} [NonUnitalCStarAlgebra A]
    (σ : A ≃⋆ₐ[ℂ] A) (a : A) :
    integerAction σ (-1 : ℤ) a = σ⁻¹ a := by
  rw [integerAction_apply]
  simp

namespace Hom

/-- Let `A` and, when present, `B` be possibly nonunital complex C*-algebras with the specified
star-algebra automorphisms. The integer group has its usual discrete topology.

Equivariance of integer actions at their chosen generators. -/
@[simp]
theorem integerAction_equivariant
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {α : A ≃⋆ₐ[ℂ] A} {β : B ≃⋆ₐ[ℂ] B}
    (φ : Hom (integerAction α) (integerAction β)) (a : A) :
    φ (α a) = β (φ a) := by
  have h := PointNormCStarAction.Hom.equivariant
    φ (Multiplicative.ofAdd (1 : ℤ)) a
  change φ ((α ^ (1 : ℤ)) a) = (β ^ (1 : ℤ)) (φ a) at h
  simpa only [zpow_one] using h

end Hom

end PointNormCStarAddAction
