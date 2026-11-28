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

public import MathlibExt.Analysis.CStarAlgebra.Extension.BusbyRelations
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Actual weak unitary homomorphism classes

The existing multiplier quotient and homomorphism carriers are retained.
All maps and equivalence laws are constructed from their actual algebraic
operations, without a stable-sum, quotient-group or source-model assumption.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra Matrix MultiplierAlgebra

universe uC uP uQ uA

namespace CStarExtension

variable {C : Type uC} {P : Type uP}
variable [NonUnitalNonAssocSemiring C] [DistribMulAction ℂ C] [StarAddMonoid C]
variable [NonUnitalCStarAlgebra P]

attribute [local instance] CStarExtension.outerCStarAlgebra

/-- **Reflexivity of weak Busby equivalence.** Let `A` be a nonunital, possibly nonassociative semiring
with a distributive complex scalar action and an additive star operation, and let `B` be a nonunital
complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A → M(B)/B`,
where `M(B)` is the multiplier algebra. Weak unitary equivalence, defined by unitary conjugation in
`M(B)/B`, is reflexive. -/
theorem weakly_unitary_equivalent_refl (tau : BusbyHom C P) :
    WeaklyUnitaryEquivalent tau tau := by
  let _ : CStarAlgebra (OuterMultiplier P) := outerMultiplierCStarAlgebra P
  refine ⟨1, ?_⟩
  intro a
  change tau a = (1 : OuterMultiplier P) * tau a * star (1 : OuterMultiplier P)
  rw [star_one, one_mul, mul_one]

/-- **Symmetry of weak Busby equivalence.** Let `A` be a nonunital, possibly nonassociative semiring
with a distributive complex scalar action and an additive star operation, and let `B` be a nonunital
complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A → M(B)/B`,
where `M(B)` is the multiplier algebra. Weak unitary equivalence of two Busby homomorphisms holds in
either order. -/
theorem weakly_unitary_equivalent_symm
    {tau₁ tau₂ : BusbyHom C P} (h : WeaklyUnitaryEquivalent tau₁ tau₂) :
    WeaklyUnitaryEquivalent tau₂ tau₁ := by
  let _ : CStarAlgebra (OuterMultiplier P) := outerMultiplierCStarAlgebra P
  obtain ⟨v, hv⟩ := h
  refine ⟨star v, ?_⟩
  intro a
  have hvalue : tau₂ a =
      Unitary.conjStarAlgAut ℂ (OuterMultiplier P) v (tau₁ a) := by
    simpa only [Unitary.conjStarAlgAut_apply] using hv a
  calc
    tau₁ a = (Unitary.conjStarAlgAut ℂ (OuterMultiplier P) v).symm (tau₂ a) := by
      rw [hvalue]
      exact ((Unitary.conjStarAlgAut ℂ
        (OuterMultiplier P) v).symm_apply_apply (tau₁ a)).symm
    _ = Unitary.conjStarAlgAut ℂ (OuterMultiplier P) (star v) (tau₂ a) := by
      rw [Unitary.conjStarAlgAut_symm]
    _ = ((star v : unitary (OuterMultiplier P)) : OuterMultiplier P) * tau₂ a *
        star ((star v : unitary (OuterMultiplier P)) : OuterMultiplier P) := by
      rw [Unitary.conjStarAlgAut_apply]

/-- **Transitivity of weak Busby equivalence.** Let `A` be a nonunital, possibly nonassociative semiring
with a distributive complex scalar action and an additive star operation, and let `B` be a nonunital
complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A → M(B)/B`,
where `M(B)` is the multiplier algebra. Two consecutive weak unitary equivalences of Busby
homomorphisms imply a weak unitary equivalence of the first and third. -/
theorem weakly_unitary_equivalent_trans
    {tau₁ tau₂ tau₃ : BusbyHom C P}
    (h₁₂ : WeaklyUnitaryEquivalent tau₁ tau₂)
    (h₂₃ : WeaklyUnitaryEquivalent tau₂ tau₃) :
    WeaklyUnitaryEquivalent tau₁ tau₃ := by
  let _ : CStarAlgebra (OuterMultiplier P) := outerMultiplierCStarAlgebra P
  obtain ⟨u, hu⟩ := h₁₂
  obtain ⟨v, hv⟩ := h₂₃
  refine ⟨v * u, ?_⟩
  intro a
  have hvalue : tau₂ a =
      Unitary.conjStarAlgAut ℂ (OuterMultiplier P) u (tau₁ a) := by
    simpa only [Unitary.conjStarAlgAut_apply] using hu a
  calc
    tau₃ a = Unitary.conjStarAlgAut ℂ (OuterMultiplier P) v (tau₂ a) := by
      simpa only [Unitary.conjStarAlgAut_apply] using hv a
    _ = Unitary.conjStarAlgAut ℂ (OuterMultiplier P) v
        (Unitary.conjStarAlgAut ℂ (OuterMultiplier P) u (tau₁ a)) := by
      rw [hvalue]
    _ = Unitary.conjStarAlgAut ℂ (OuterMultiplier P) (v * u) (tau₁ a) :=
      (Unitary.conjStarAlgAut_mul_apply v u (tau₁ a)).symm
    _ = ((v * u : unitary (OuterMultiplier P)) : OuterMultiplier P) * tau₁ a *
        star ((v * u : unitary (OuterMultiplier P)) : OuterMultiplier P) := by
      rw [Unitary.conjStarAlgAut_apply]

/-- **Equivalence relation of weak Busby conjugacy.** Let `A` be a nonunital, possibly nonassociative
semiring with a distributive complex scalar action and an additive star operation, and let `B` be a
nonunital complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A →
M(B)/B`, where `M(B)` is the multiplier algebra. Weak unitary equivalence is an equivalence relation
on the set of Busby homomorphisms. -/
@[instance_reducible]
noncomputable def weakUnitaryHomSetoid (C : Type uC) (P : Type uP)
    [NonUnitalNonAssocSemiring C] [DistribMulAction ℂ C] [StarAddMonoid C]
    [NonUnitalCStarAlgebra P] : Setoid (BusbyHom C P) where
  r := WeaklyUnitaryEquivalent
  iseqv := ⟨weakly_unitary_equivalent_refl,
    weakly_unitary_equivalent_symm, weakly_unitary_equivalent_trans⟩

/-- **Weak unitary classes of Busby homomorphisms.** Let `A` be a nonunital, possibly nonassociative
semiring with a distributive complex scalar action and an additive star operation, and let `B` be a
nonunital complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A →
M(B)/B`, where `M(B)` is the multiplier algebra. This is the quotient of all Busby homomorphisms by
unitary conjugacy in the outer multiplier algebra. -/
abbrev UnitaryHomClasses (C : Type uC) (P : Type uP)
    [NonUnitalNonAssocSemiring C] [DistribMulAction ℂ C] [StarAddMonoid C]
    [NonUnitalCStarAlgebra P] :=
  Quotient (weakUnitaryHomSetoid C P)

namespace UnitaryHomClasses

/-- **Class of a Busby homomorphism.** Let `A` be a nonunital, possibly nonassociative semiring with a
distributive complex scalar action and an additive star operation, and let `B` be a nonunital
complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A → M(B)/B`,
where `M(B)` is the multiplier algebra. Each Busby homomorphism determines its class modulo unitary
conjugacy in `M(B)/B`. -/
noncomputable def mk (tau : BusbyHom C P) : UnitaryHomClasses C P :=
  Quotient.mk (weakUnitaryHomSetoid C P) tau

/-- **Equality of weak unitary Busby classes.** Let `A` be a nonunital, possibly nonassociative semiring
with a distributive complex scalar action and an additive star operation, and let `B` be a nonunital
complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A → M(B)/B`,
where `M(B)` is the multiplier algebra. Two homomorphisms have the same class exactly when they are
conjugate by a unitary of `M(B)/B`. -/
theorem mk_eq_mk_iff (tau₁ tau₂ : BusbyHom C P) :
    mk tau₁ = mk tau₂ ↔ WeaklyUnitaryEquivalent tau₁ tau₂ :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- **Liftable representative of a Busby class.** Let `A` be a nonunital, possibly nonassociative
semiring with a distributive complex scalar action and an additive star operation, and let `B` be a
nonunital complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A →
M(B)/B`, where `M(B)` is the multiplier algebra. A weak unitary class has this property when at
least one of its Busby homomorphisms lifts to a nonunital complex star homomorphism into `M(B)`. -/
def HasLiftableRepresentative (x : UnitaryHomClasses C P) : Prop :=
  ∃ tau : BusbyHom C P, mk tau = x ∧ IsTrivial tau

/-- **Liftability of the zero Busby class.** Let `A` be a nonunital, possibly nonassociative semiring
with a distributive complex scalar action and an additive star operation, and let `B` be a nonunital
complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A → M(B)/B`,
where `M(B)` is the multiplier algebra. The class of the zero homomorphism contains a representative
lifting to the zero homomorphism into `M(B)`. -/
theorem zero_hasLiftableRepresentative :
    HasLiftableRepresentative (mk (0 : BusbyHom C P)) :=
  ⟨0, rfl, zero_is_trivial⟩

end UnitaryHomClasses

/-- **Strong Busby conjugacy preserves liftability.** Let `A` be a nonunital, possibly nonassociative
semiring with a distributive complex scalar action and an additive star operation, and let `B` be a
nonunital complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A →
M(B)/B`, where `M(B)` is the multiplier algebra. If `τ₁` lifts to `M(B)` and `τ₂` is strongly
unitarily equivalent to `τ₁`, then `τ₂` also lifts to `M(B)`. -/
theorem isTrivial_of_strongly_unitary_equivalent
    {tau₁ tau₂ : BusbyHom C P} (h : StronglyUnitaryEquivalent tau₁ tau₂)
    (hLift : IsTrivial tau₁) : IsTrivial tau₂ := by
  let _ : CStarAlgebra (OuterMultiplier P) := outerMultiplierCStarAlgebra P
  obtain ⟨u, hu⟩ := h
  obtain ⟨rho, hrho⟩ := hLift
  let q := outerQuotientMap (A := P)
  let alpha := Unitary.conjStarAlgAut ℂ (DoubleCentralizer ℂ P) u
  refine ⟨alpha.toStarAlgHom.toNonUnitalStarAlgHom.comp rho, ?_⟩
  apply NonUnitalStarAlgHom.ext
  intro a
  have hvalue := congrArg (fun eta : BusbyHom C P => eta a) hrho
  change q (rho a) = tau₁ a at hvalue
  change q ((u : DoubleCentralizer ℂ P) * rho a *
    star (u : DoubleCentralizer ℂ P)) = tau₂ a
  rw [map_mul, map_mul, map_star, hvalue]
  exact (hu a).symm

end CStarExtension
