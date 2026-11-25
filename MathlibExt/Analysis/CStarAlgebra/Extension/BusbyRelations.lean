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

public import MathlibExt.Analysis.CStarAlgebra.Extension.BusbyDefs
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Unitary equivalence and literal lifts of Busby homomorphisms

The predicates use actual multiplier or outer-multiplier unitaries and actual
multiplier-valued star-homomorphic lifts. They require only the algebraic
source of `BusbyHom`. All coefficient operations and the quotient map are
those of the existing multiplier algebra.

The strong-equivalence calculus preserves the explicit Section 15 unitary
proof chain. No stable sum, quotient class, source proof, or inverse theorem
is imported or assumed. The quotient C-star factory is activated only locally.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra MultiplierAlgebra

namespace CStarExtension

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalNonAssocSemiring A] [DistribMulAction ℂ A] [StarAddMonoid A]
variable [NonUnitalCStarAlgebra B]

attribute [local instance] CStarExtension.outerCStarAlgebra

/-- **Strong unitary equivalence of Busby maps.** Let `A` be a nonunital, possibly nonassociative
semiring with a distributive complex scalar action and an additive star operation, and let `B` be a
nonunital complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A →
M(B)/B`, where `M(B)` is the multiplier algebra. Two such homomorphisms are strongly unitarily
equivalent when one is obtained from the other by conjugation by the image in `M(B)/B` of a unitary
of `M(B)`. -/
def StronglyUnitaryEquivalent (tau₁ tau₂ : BusbyHom A B) : Prop :=
  ∃ u : unitary 𝓜(ℂ, B), ∀ a : A,
    tau₂ a = outerQuotientMap (u : 𝓜(ℂ, B)) * tau₁ a *
      star (outerQuotientMap (u : 𝓜(ℂ, B)))

/-- **Weak unitary equivalence of Busby maps.** Let `A` be a nonunital, possibly nonassociative semiring
with a distributive complex scalar action and an additive star operation, and let `B` be a nonunital
complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A → M(B)/B`,
where `M(B)` is the multiplier algebra. Two such homomorphisms are weakly unitarily equivalent when
one is obtained from the other by conjugation by a unitary of `M(B)/B`. -/
def WeaklyUnitaryEquivalent (tau₁ tau₂ : BusbyHom A B) : Prop :=
  ∃ v : unitary (OuterMultiplier B), ∀ a : A,
    tau₂ a = (v : OuterMultiplier B) * tau₁ a * star (v : OuterMultiplier B)

/-- **Trivial Busby homomorphism.** Let `A` be a nonunital, possibly nonassociative semiring with a
distributive complex scalar action and an additive star operation, and let `B` be a nonunital
complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A → M(B)/B`,
where `M(B)` is the multiplier algebra. It is trivial when it lifts to a nonunital complex star
homomorphism `A → M(B)` through the quotient `M(B) → M(B)/B`. -/
def IsTrivial (tau : BusbyHom A B) : Prop :=
  ∃ rho : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B),
    (outerQuotientMap (A := B)).toNonUnitalStarAlgHom.comp rho = tau

/-- **Reflexivity of strong Busby equivalence.** Let `A` be a nonunital, possibly nonassociative
semiring with a distributive complex scalar action and an additive star operation, and let `B` be a
nonunital complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A →
M(B)/B`, where `M(B)` is the multiplier algebra. Strong unitary equivalence, defined by
multiplier-unitary conjugation, is reflexive. -/
theorem strongly_unitary_equivalent_refl
    (tau : BusbyHom A B) :
    StronglyUnitaryEquivalent tau tau := by
  let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  refine ⟨1, ?_⟩
  intro a
  change tau a = outerQuotientMap (1 : 𝓜(ℂ, B)) * tau a *
    star (outerQuotientMap (1 : 𝓜(ℂ, B)))
  rw [map_one, star_one, one_mul, mul_one]

/-- **Symmetry of strong Busby equivalence.** Let `A` be a nonunital, possibly nonassociative semiring
with a distributive complex scalar action and an additive star operation, and let `B` be a nonunital
complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A → M(B)/B`,
where `M(B)` is the multiplier algebra. If two Busby homomorphisms are strongly unitarily
equivalent, they are strongly unitarily equivalent in the opposite order. -/
theorem strongly_unitary_equivalent_symm
    {tau₁ tau₂ : BusbyHom A B}
    (h : StronglyUnitaryEquivalent tau₁ tau₂) :
    StronglyUnitaryEquivalent tau₂ tau₁ := by
  let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  obtain ⟨u, hu⟩ := h
  let q := outerQuotientMap (A := B)
  let qU : unitary (OuterMultiplier B) :=
    Unitary.map (StarMonoidHom.ofClass q) u
  refine ⟨star u, ?_⟩
  intro a
  have hua : tau₂ a =
      Unitary.conjStarAlgAut ℂ (OuterMultiplier B) qU (tau₁ a) := by
    simpa only [Unitary.conjStarAlgAut_apply, qU, Unitary.coe_map,
      StarMonoidHom.ofClass_coe, q] using hu a
  calc
    tau₁ a =
        (Unitary.conjStarAlgAut ℂ (OuterMultiplier B) qU).symm (tau₂ a) := by
      rw [hua]
      exact ((Unitary.conjStarAlgAut ℂ
        (OuterMultiplier B) qU).symm_apply_apply (tau₁ a)).symm
    _ = Unitary.conjStarAlgAut ℂ (OuterMultiplier B) (star qU) (tau₂ a) := by
      rw [Unitary.conjStarAlgAut_symm]
    _ = q ((star u : unitary 𝓜(ℂ, B)) : 𝓜(ℂ, B)) * tau₂ a *
        star (q ((star u : unitary 𝓜(ℂ, B)) : 𝓜(ℂ, B))) := by
      simp only [Unitary.conjStarAlgAut_apply, qU, Unitary.coe_star,
        Unitary.coe_map, StarMonoidHom.ofClass_coe, map_star]

/-- **Transitivity of strong Busby equivalence.** Let `A` be a nonunital, possibly nonassociative
semiring with a distributive complex scalar action and an additive star operation, and let `B` be a
nonunital complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A →
M(B)/B`, where `M(B)` is the multiplier algebra. If the first and second Busby homomorphisms are
strongly unitarily equivalent, and the second and third are strongly unitarily equivalent, so are
the first and third. -/
theorem strongly_unitary_equivalent_trans
    {tau₁ tau₂ tau₃ : BusbyHom A B}
    (h₁₂ : StronglyUnitaryEquivalent tau₁ tau₂)
    (h₂₃ : StronglyUnitaryEquivalent tau₂ tau₃) :
    StronglyUnitaryEquivalent tau₁ tau₃ := by
  let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  obtain ⟨u, hu⟩ := h₁₂
  obtain ⟨v, hv⟩ := h₂₃
  let q := outerQuotientMap (A := B)
  let qU : unitary (OuterMultiplier B) :=
    Unitary.map (StarMonoidHom.ofClass q) u
  let qV : unitary (OuterMultiplier B) :=
    Unitary.map (StarMonoidHom.ofClass q) v
  refine ⟨v * u, ?_⟩
  intro a
  have hua : tau₂ a =
      Unitary.conjStarAlgAut ℂ (OuterMultiplier B) qU (tau₁ a) := by
    simpa only [Unitary.conjStarAlgAut_apply, qU, Unitary.coe_map,
      StarMonoidHom.ofClass_coe, q] using hu a
  have hva : tau₃ a =
      Unitary.conjStarAlgAut ℂ (OuterMultiplier B) qV (tau₂ a) := by
    simpa only [Unitary.conjStarAlgAut_apply, qV, Unitary.coe_map,
      StarMonoidHom.ofClass_coe, q] using hv a
  calc
    tau₃ a = Unitary.conjStarAlgAut ℂ (OuterMultiplier B) qV (tau₂ a) := hva
    _ = Unitary.conjStarAlgAut ℂ (OuterMultiplier B) qV
        (Unitary.conjStarAlgAut ℂ (OuterMultiplier B) qU (tau₁ a)) := by rw [hua]
    _ = Unitary.conjStarAlgAut ℂ (OuterMultiplier B) (qV * qU) (tau₁ a) :=
      (Unitary.conjStarAlgAut_mul_apply qV qU (tau₁ a)).symm
    _ = q ((v * u : unitary 𝓜(ℂ, B)) : 𝓜(ℂ, B)) * tau₁ a *
        star (q ((v * u : unitary 𝓜(ℂ, B)) : 𝓜(ℂ, B))) := by
      have hProduct : ((qV * qU : unitary (OuterMultiplier B)) : OuterMultiplier B) =
          q ((v * u : unitary 𝓜(ℂ, B)) : 𝓜(ℂ, B)) := by
        simp only [qV, qU, Submonoid.coe_mul, Unitary.coe_map,
          StarMonoidHom.ofClass_coe, map_mul q]
      rw [Unitary.conjStarAlgAut_apply, hProduct]

/-- **Zero Busby homomorphism is trivial.** Let `A` be a nonunital, possibly nonassociative semiring
with a distributive complex scalar action and an additive star operation, and let `B` be a nonunital
complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A → M(B)/B`,
where `M(B)` is the multiplier algebra. The zero Busby homomorphism lifts to the zero homomorphism
into `M(B)`. -/
theorem zero_is_trivial : IsTrivial (0 : BusbyHom A B) := by
  refine ⟨0, ?_⟩
  apply NonUnitalStarAlgHom.ext
  intro a
  change outerQuotientMap (0 : 𝓜(ℂ, B)) = (0 : OuterMultiplier B)
  exact map_zero (outerQuotientMap (A := B))

end CStarExtension
