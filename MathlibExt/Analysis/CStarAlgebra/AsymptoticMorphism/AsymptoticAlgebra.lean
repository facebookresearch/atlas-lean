/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.VanishingIdeal
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Basic

import Mathlib.Order.LatticeIntervals
import Mathlib.Topology.Order.Compact

/-!
# The asymptotic C-star algebra and lifted families

Let B be a nonunital complex C-star algebra and T=AsymptoticTime=[1,∞). Write
B∞=AsymptoticAlgebra B=C_b(T,B)/C₀(T,B), and q_B:C_b(T,B)→B∞ for the quotient map. The
quotient norm is ‖q_B(F)‖=inf{‖F+h‖∞:h∈C₀(T,B)}, where ‖F‖∞=sup_t‖F(t)‖. The quotient is a
nonunital complex C-star algebra. A bounded continuous function represents zero precisely when
it tends to zero at infinity. For a star homomorphism ρ:A→B∞, any choice of representatives
F_a with q_B(F_a)=ρ(a) defines an asymptotic family φ_t(a)=F_a(t); all such choices are
strictly equivalent.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter
open scoped ZeroAtInfty BoundedContinuousFunction

noncomputable section

universe uA uB

/-- **Quotient by functions vanishing at infinity.**

Let B be a nonunital complex C-star algebra and T=AsymptoticTime=[1,∞). Write
B∞=AsymptoticAlgebra B=C_b(T,B)/C₀(T,B), and q_B:C_b(T,B)→B∞ for the quotient map. The ideal
C₀(T,B) consists of bounded continuous functions F with ‖F(t)‖→0 as t→∞. The quotient norm is
‖q_B(F)‖=inf{‖F+h‖∞:h∈C₀(T,B)}, where ‖F‖∞=sup_t‖F(t)‖.
-/
abbrev AsymptoticAlgebra (B : Type uB) [NonUnitalCStarAlgebra B] :=
  (BoundedContinuousFunction.vanishingIdeal AsymptoticTime B).Quotient

namespace AsymptoticAlgebra

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **C-star algebra of asymptotic function classes.**

Let B be a nonunital complex C-star algebra and T=AsymptoticTime=[1,∞). Write
B∞=AsymptoticAlgebra B=C_b(T,B)/C₀(T,B), and q_B:C_b(T,B)→B∞ for the quotient map. The
quotient norm is ‖q_B(F)‖=inf{‖F+h‖∞:h∈C₀(T,B)}, where ‖F‖∞=sup_t‖F(t)‖. Pointwise addition,
multiplication, complex scaling and star descend to B∞. With this quotient norm it is a
nonunital complex C-star algebra, satisfying ‖star(x)*x‖=‖x‖².
-/
@[instance_reducible]
def cStarAlgebra (B : Type uB) [NonUnitalCStarAlgebra B] :
    NonUnitalCStarAlgebra (AsymptoticAlgebra B) :=
  (BoundedContinuousFunction.vanishingIdeal AsymptoticTime B).quotientCStarAlgebra

attribute [local instance] cStarAlgebra

/-- **Asymptotic quotient homomorphism.**

Let B be a nonunital complex C-star algebra and T=AsymptoticTime=[1,∞). Write
B∞=AsymptoticAlgebra B=C_b(T,B)/C₀(T,B), and q_B:C_b(T,B)→B∞ for the quotient map. The map
quotientMap B=q_B sends a bounded continuous time function F to its class modulo C₀(T,B); it
is a nonunital complex star homomorphism.
-/
def quotientMap (B : Type uB) [NonUnitalCStarAlgebra B] :
    (AsymptoticTime →ᵇ B) →⋆ₙₐ[ℂ] AsymptoticAlgebra B :=
  (BoundedContinuousFunction.vanishingIdeal AsymptoticTime B).quotientMap

private theorem ray_cocompact_eq_atTop :
    cocompact AsymptoticTime = (atTop : Filter AsymptoticTime) := by
  let : OrderBot AsymptoticTime := Set.Ici.orderBot
  let : NoMaxOrder AsymptoticTime :=
    ⟨fun t =>
      ⟨⟨(t : ℝ) + 1, t.property.trans (le_add_of_nonneg_right zero_le_one)⟩,
        lt_add_one (t : ℝ)⟩⟩
  let : ClosedIciTopology AsymptoticTime :=
    ⟨fun t => (isClosed_Ici : IsClosed (Set.Ici (t : ℝ))).preimage
      continuous_subtype_val⟩
  let : CompactIccSpace AsymptoticTime :=
    ⟨fun {a b} => by
      apply Subtype.isCompact_iff.mpr
      have himage : Subtype.val '' (Set.Icc a b : Set AsymptoticTime) =
          Set.Icc (a : ℝ) (b : ℝ) := by
        ext x
        constructor
        · rintro ⟨t, ht, rfl⟩
          exact ht
        · intro hx
          exact ⟨⟨x, a.property.trans hx.1⟩, hx, rfl⟩
      rw [himage]
      exact isCompact_Icc⟩
  exact cocompact_eq_atTop

/-- **Vanishing ideal characterized by the time limit.**

Let B be a nonunital complex C-star algebra and T=AsymptoticTime=[1,∞). Write
B∞=AsymptoticAlgebra B=C_b(T,B)/C₀(T,B), and q_B:C_b(T,B)→B∞ for the quotient map. For
F∈C_b(T,B), F belongs to the closed star ideal C₀(T,B) exactly when F(t)→0 in norm as t→∞.
-/
theorem mem_vanishingIdeal_iff (f : AsymptoticTime →ᵇ B) :
    f ∈ BoundedContinuousFunction.vanishingIdeal AsymptoticTime B ↔
      Tendsto f atTop (nhds 0) := by
  rw [BoundedContinuousFunction.mem_vanishingIdeal_iff, ray_cocompact_eq_atTop]

/-- **Zero quotient class characterized by vanishing at infinity.**

Let B be a nonunital complex C-star algebra and T=AsymptoticTime=[1,∞). Write
B∞=AsymptoticAlgebra B=C_b(T,B)/C₀(T,B), and q_B:C_b(T,B)→B∞ for the quotient map. For
F∈C_b(T,B), q_B(F)=0 if and only if F(t)→0 in B as t→∞.
-/
theorem quotientMap_eq_zero_iff (f : AsymptoticTime →ᵇ B) :
    quotientMap B f = 0 ↔ Tendsto f atTop (nhds 0) := by
  change (BoundedContinuousFunction.vanishingIdeal AsymptoticTime B).quotientMap f = 0 ↔ _
  rw [ClosedStarIdeal.quotientMap_eq_zero_iff, mem_vanishingIdeal_iff]

/-- **Equality of asymptotic classes characterized by a vanishing difference.**

Let B be a nonunital complex C-star algebra and T=AsymptoticTime=[1,∞). Write
B∞=AsymptoticAlgebra B=C_b(T,B)/C₀(T,B), and q_B:C_b(T,B)→B∞ for the quotient map. For
F,G∈C_b(T,B), q_B(F)=q_B(G) if and only if F(t)-G(t)→0 in B as t→∞.
-/
theorem quotientMap_eq_iff (f g : AsymptoticTime →ᵇ B) :
    quotientMap B f = quotientMap B g ↔
      Tendsto (fun t => f t - g t) atTop (nhds 0) := by
  rw [← sub_eq_zero, ← map_sub, quotientMap_eq_zero_iff]
  rfl

/-- **A function vanishing at infinity has zero class.**

Let B be a nonunital complex C-star algebra and T=AsymptoticTime=[1,∞). Write
B∞=AsymptoticAlgebra B=C_b(T,B)/C₀(T,B), and q_B:C_b(T,B)→B∞ for the quotient map. For
f∈C₀(T,B), its bounded continuous representative f.toBCF has q_B(f.toBCF)=0.
-/
theorem quotientMap_toBCF (f : C₀(AsymptoticTime, B)) :
    quotientMap B f.toBCF = 0 :=
  ((BoundedContinuousFunction.vanishingIdeal AsymptoticTime B).quotientMap_eq_zero_iff
    f.toBCF).2 (BoundedContinuousFunction.toBCF_mem_vanishingIdeal f)

/-- **Surjectivity of the asymptotic quotient map.**

Let B be a nonunital complex C-star algebra and T=AsymptoticTime=[1,∞). Write
B∞=AsymptoticAlgebra B=C_b(T,B)/C₀(T,B), and q_B:C_b(T,B)→B∞ for the quotient map. Every x∈B∞
has a bounded continuous representative F∈C_b(T,B) with q_B(F)=x.
-/
theorem quotientMap_surjective (B : Type uB) [NonUnitalCStarAlgebra B] :
    Function.Surjective (quotientMap B) :=
  (BoundedContinuousFunction.vanishingIdeal AsymptoticTime B).quotientMap_surjective

/-- **Asymptotic morphism from quotient-homomorphism lifts.**

Let B be a nonunital complex C-star algebra and T=AsymptoticTime=[1,∞). Write
B∞=AsymptoticAlgebra B=C_b(T,B)/C₀(T,B), and q_B:C_b(T,B)→B∞ for the quotient map. Let A also
be a nonunital complex C-star algebra and ρ:A→B∞ a nonunital complex star homomorphism. Choose
F:A→C_b(T,B) with q_B(F(a))=ρ(a) for every a. The family ofLift ρ F hF:A→B is φ_t(a)=F(a)(t).
Its four algebraic defects tend to zero because their quotient classes are zero, and each
coefficient orbit is continuous.
-/
def ofLift (ρ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B)
    (F : A → AsymptoticTime →ᵇ B)
    (hF : ∀ a : A, quotientMap B (F a) = ρ a) : AsymptoticMorphism A B where
  toFun t a := F a t
  continuous_orbit a := (F a).continuous
  add_defect_tendsto a b := by
    have hzero : quotientMap B (F (a + b) - (F a + F b)) = 0 := by
      simp only [map_sub, map_add, hF, sub_self]
    have h := (quotientMap_eq_zero_iff _).1 hzero
    exact h.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
      simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.add_apply])
  smul_defect_tendsto z a := by
    have hzero : quotientMap B (F (z • a) - z • F a) = 0 := by
      simp only [map_sub, map_smul, hF, sub_self]
    have h := (quotientMap_eq_zero_iff _).1 hzero
    exact h.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
      simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply])
  mul_defect_tendsto a b := by
    have hzero : quotientMap B (F (a * b) - F a * F b) = 0 := by
      simp only [map_sub, map_mul, hF, sub_self]
    have h := (quotientMap_eq_zero_iff _).1 hzero
    exact h.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
      simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.mul_apply])
  star_defect_tendsto a := by
    have hzero : quotientMap B (F (star a) - star (F a)) = 0 := by
      simp only [map_sub, map_star, hF, sub_self]
    have h := (quotientMap_eq_zero_iff _).1 hzero
    exact h.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
      simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.star_apply])

/-- **Value of a lifted asymptotic family.**

Let B be a nonunital complex C-star algebra and T=AsymptoticTime=[1,∞). Write
B∞=AsymptoticAlgebra B=C_b(T,B)/C₀(T,B), and q_B:C_b(T,B)→B∞ for the quotient map. Let A also
be a nonunital complex C-star algebra and ρ:A→B∞ a nonunital complex star homomorphism. Choose
F:A→C_b(T,B) with q_B(F(a))=ρ(a) for every a. For t∈T and a∈A, ofLift ρ F hF t a=F(a)(t).
-/
@[simp]
theorem ofLift_apply (ρ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B)
    (F : A → AsymptoticTime →ᵇ B)
    (hF : ∀ a : A, quotientMap B (F a) = ρ a)
    (t : AsymptoticTime) (a : A) : ofLift ρ F hF t a = F a t := by
  rfl

/-- **Strict equivalence of two quotient-homomorphism lifts.**

Let B be a nonunital complex C-star algebra and T=AsymptoticTime=[1,∞). Write
B∞=AsymptoticAlgebra B=C_b(T,B)/C₀(T,B), and q_B:C_b(T,B)→B∞ for the quotient map. Let A be a
nonunital complex C-star algebra, ρ:A→B∞ a nonunital complex star homomorphism and
F,G:A→C_b(T,B) satisfy q_B(F(a))=q_B(G(a))=ρ(a). Then F(a)(t)-G(a)(t)→0 for every a as t→∞, so
the two lifted asymptotic families are strictly equivalent.
-/
theorem strictlyEquivalent_ofLift (ρ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B)
    (F G : A → AsymptoticTime →ᵇ B)
    (hF : ∀ a : A, quotientMap B (F a) = ρ a)
    (hG : ∀ a : A, quotientMap B (G a) = ρ a) :
    AsymptoticMorphism.StrictlyEquivalent (ofLift ρ F hF) (ofLift ρ G hG) := by
  intro a
  have h := (quotientMap_eq_iff (F a) (G a)).1 ((hF a).trans (hG a).symm)
  simpa only [ofLift_apply] using h

/-- **Asymptotic family associated with a quotient homomorphism.**

Let B be a nonunital complex C-star algebra and T=AsymptoticTime=[1,∞). Write
B∞=AsymptoticAlgebra B=C_b(T,B)/C₀(T,B), and q_B:C_b(T,B)→B∞ for the quotient map. Let A be a
nonunital complex C-star algebra and ρ:A→B∞ a nonunital complex star homomorphism. Choose a
bounded continuous representative F_a of ρ(a) for each a. The asymptotic morphism ofHom ρ is
the family φ_t(a)=F_a(t).
-/
def ofHom (ρ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B) : AsymptoticMorphism A B :=
  ofLift ρ
    (fun a => Classical.choose (quotientMap_surjective B (ρ a)))
    (fun a => Classical.choose_spec (quotientMap_surjective B (ρ a)))

/-- **Coefficient values of the chosen quotient lift.**

Let B be a nonunital complex C-star algebra and T=AsymptoticTime=[1,∞). Write
B∞=AsymptoticAlgebra B=C_b(T,B)/C₀(T,B), and q_B:C_b(T,B)→B∞ for the quotient map. Let A be a
nonunital complex C-star algebra and ρ:A→B∞ a nonunital complex star homomorphism. For the
representative F_a∈C_b(T,B) chosen with q_B(F_a)=ρ(a) in ofHom ρ, its coefficient values are
ofHom ρ t a=F_a(t).
-/
@[simp]
theorem ofHom_apply (ρ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B)
    (t : AsymptoticTime) (a : A) :
    ofHom ρ t a =
      (Classical.choose (quotientMap_surjective B (ρ a)) : AsymptoticTime →ᵇ B) t := by
  rfl

end AsymptoticAlgebra
