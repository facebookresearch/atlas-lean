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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.AsymptoticAlgebra
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Bounds

/-!
# Asymptotic morphisms and homomorphisms into the quotient algebra

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. For an asymptotic star morphism φ:A→B, write
F_a(t)=φ_t(a) for its bounded continuous coefficient orbit, and Φφ(a)=q_B(F_a). Two families
φ,ψ are strictly equivalent when φ_t(a)-ψ_t(a)→0 in norm as t→∞ for every a∈A. For each φ,
Φφ:A→B∞ is a nonunital complex star homomorphism. It gives a bijection between
strict-equivalence classes of asymptotic morphisms A→B and nonunital complex star
homomorphisms A→B∞.

Reference: Blackadar, K-Theory for Operator Algebras (1998), 25.1.3–25.1.4(a).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped ZeroAtInfty BoundedContinuousFunction

noncomputable section

namespace AsymptoticMorphism

universe uA uB

attribute [local instance] _root_.AsymptoticAlgebra.cStarAlgebra

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Bounded continuous orbit of an asymptotic coefficient.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. For an asymptotic star morphism φ:A→B, write
F_a(t)=φ_t(a) for its bounded continuous coefficient orbit, and Φφ(a)=q_B(F_a). The function
orbitBCF φ a∈C_b(T,B) is F_a:t↦φ_t(a), using the boundedness of each asymptotic coefficient
orbit.
-/
@[no_expose]
def orbitBCF (φ : AsymptoticMorphism A B) (a : A) : AsymptoticTime →ᵇ B where
  toFun t := φ t a
  continuous_toFun := by
    simpa only [_root_.AsymptoticMorphism.toFun_eq_coe] using
      _root_.AsymptoticMorphism.continuous_orbit φ a
  map_bounded' := by
    obtain ⟨C, hC⟩ := (_root_.AsymptoticMorphism.norm_bounded_and_eventually_contractive φ a).1
    refine ⟨C + C, fun s t => ?_⟩
    exact (dist_le_norm_add_norm (φ s a) (φ t a)).trans
      (add_le_add (hC s) (hC t))

/-- **Value of a bounded asymptotic orbit.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. For an asymptotic star morphism φ:A→B, write
F_a(t)=φ_t(a) for its bounded continuous coefficient orbit, and Φφ(a)=q_B(F_a). For a∈A and
t≥1, orbitBCF φ a t=φ_t(a).
-/
@[simp]
theorem orbitBCF_apply (φ : AsymptoticMorphism A B)
    (a : A) (t : AsymptoticTime) : orbitBCF φ a t = φ t a := by
  rfl

/-- **Quotient homomorphism defined by an asymptotic family.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. For an asymptotic star morphism φ:A→B, write
F_a(t)=φ_t(a) for its bounded continuous coefficient orbit, and Φφ(a)=q_B(F_a). The map toHom
φ:A→B∞ is the nonunital complex star homomorphism Φφ:a↦q_B(t↦φ_t(a)).
-/
@[no_expose]
def toHom (φ : AsymptoticMorphism A B) : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B where
  toFun a := _root_.AsymptoticAlgebra.quotientMap B (orbitBCF φ a)
  map_zero' := by
    apply (_root_.AsymptoticAlgebra.quotientMap_eq_zero_iff _).2
    have ht : Tendsto (fun t : AsymptoticTime => φ t (0 : A)) atTop (nhds (0 : B)) :=
      _root_.AsymptoticMorphism.zero_tendsto φ
    exact ht.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
      simp only [orbitBCF_apply])
  map_add' := by
    intro a b
    have h :
        _root_.AsymptoticAlgebra.quotientMap B
          (orbitBCF φ (a + b) - (orbitBCF φ a + orbitBCF φ b)) = 0 := by
      apply (_root_.AsymptoticAlgebra.quotientMap_eq_zero_iff _).2
      have ht : Tendsto (fun t : AsymptoticTime =>
          φ t (a + b) - (φ t a + φ t b)) atTop (nhds (0 : B)) := by
        simpa only [_root_.AsymptoticMorphism.toFun_eq_coe] using
          _root_.AsymptoticMorphism.add_defect_tendsto φ a b
      exact ht.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
        simp only [BoundedContinuousFunction.sub_apply,
          BoundedContinuousFunction.add_apply, orbitBCF_apply])
    rw [map_sub, map_add, sub_eq_zero] at h
    exact h
  map_smul' := by
    intro z a
    have h :
        _root_.AsymptoticAlgebra.quotientMap B
          (orbitBCF φ (z • a) - z • orbitBCF φ a) = 0 := by
      apply (_root_.AsymptoticAlgebra.quotientMap_eq_zero_iff _).2
      have ht : Tendsto (fun t : AsymptoticTime =>
          φ t (z • a) - z • φ t a) atTop (nhds (0 : B)) := by
        simpa only [_root_.AsymptoticMorphism.toFun_eq_coe] using
          _root_.AsymptoticMorphism.smul_defect_tendsto φ z a
      exact ht.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
        simp only [BoundedContinuousFunction.sub_apply,
          BoundedContinuousFunction.smul_apply, orbitBCF_apply])
    rw [map_sub, map_smul, sub_eq_zero] at h
    exact h
  map_mul' := by
    intro a b
    have h :
        _root_.AsymptoticAlgebra.quotientMap B
          (orbitBCF φ (a * b) - orbitBCF φ a * orbitBCF φ b) = 0 := by
      apply (_root_.AsymptoticAlgebra.quotientMap_eq_zero_iff _).2
      have ht : Tendsto (fun t : AsymptoticTime =>
          φ t (a * b) - φ t a * φ t b) atTop (nhds (0 : B)) := by
        simpa only [_root_.AsymptoticMorphism.toFun_eq_coe] using
          _root_.AsymptoticMorphism.mul_defect_tendsto φ a b
      exact ht.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
        simp only [BoundedContinuousFunction.sub_apply,
          BoundedContinuousFunction.mul_apply, orbitBCF_apply])
    rw [map_sub, map_mul, sub_eq_zero] at h
    exact h
  map_star' := by
    intro a
    have h :
        _root_.AsymptoticAlgebra.quotientMap B
          (orbitBCF φ (star a) - star (orbitBCF φ a)) = 0 := by
      apply (_root_.AsymptoticAlgebra.quotientMap_eq_zero_iff _).2
      have ht : Tendsto (fun t : AsymptoticTime =>
          φ t (star a) - star (φ t a)) atTop (nhds (0 : B)) := by
        simpa only [_root_.AsymptoticMorphism.toFun_eq_coe] using
          _root_.AsymptoticMorphism.star_defect_tendsto φ a
      exact ht.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
        simp only [BoundedContinuousFunction.sub_apply,
          BoundedContinuousFunction.star_apply, orbitBCF_apply])
    rw [map_sub, map_star, sub_eq_zero] at h
    exact h

/-- **Quotient class of an asymptotic coefficient orbit.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. For an asymptotic star morphism φ:A→B, write
F_a(t)=φ_t(a) for its bounded continuous coefficient orbit, and Φφ(a)=q_B(F_a). For a∈A, toHom
φ a=q_B(orbitBCF φ a)=[t↦φ_t(a)].
-/
@[simp]
theorem toHom_apply (φ : AsymptoticMorphism A B) (a : A) :
    toHom φ a = _root_.AsymptoticAlgebra.quotientMap B (orbitBCF φ a) := by
  rfl

/-- **Equal quotient homomorphisms exactly for strictly equivalent families.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. Two families φ,ψ are strictly equivalent when
φ_t(a)-ψ_t(a)→0 in norm as t→∞ for every a∈A. For asymptotic star morphisms φ,ψ:A→B, toHom
φ=toHom ψ if and only if they are strictly equivalent; toHom sends a to the quotient class
[t↦φ_t(a)].
-/
theorem toHom_eq_iff (φ ψ : AsymptoticMorphism A B) :
    toHom φ = toHom ψ ↔ StrictlyEquivalent φ ψ := by
  constructor
  · intro h a
    have hq := DFunLike.congr_fun h a
    rw [toHom_apply, toHom_apply] at hq
    have ht := (_root_.AsymptoticAlgebra.quotientMap_eq_iff
      (orbitBCF φ a) (orbitBCF ψ a)).1 hq
    simpa only [orbitBCF_apply] using ht
  · intro h
    apply NonUnitalStarAlgHom.ext
    intro a
    apply (_root_.AsymptoticAlgebra.quotientMap_eq_iff _ _).2
    simpa only [orbitBCF_apply] using h a

/-- **A lifted quotient homomorphism maps back to itself.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. For a nonunital complex star homomorphism
ρ:A→B∞, choose bounded continuous representatives F_a with q_B(F_a)=ρ(a). The resulting
asymptotic family AsymptoticAlgebra.ofHom ρ has toHom(AsymptoticAlgebra.ofHom ρ)=ρ.
-/
theorem toHom_ofHom (ρ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B) :
    toHom (_root_.AsymptoticAlgebra.ofHom ρ) = ρ := by
  apply NonUnitalStarAlgHom.ext
  intro a
  change _root_.AsymptoticAlgebra.quotientMap B
      (orbitBCF (_root_.AsymptoticAlgebra.ofHom ρ) a) = ρ a
  have horbit : orbitBCF (_root_.AsymptoticAlgebra.ofHom ρ) a =
      Classical.choose (_root_.AsymptoticAlgebra.quotientMap_surjective B (ρ a)) := by
    apply BoundedContinuousFunction.ext
    intro t
    rw [orbitBCF_apply, _root_.AsymptoticAlgebra.ofHom_apply]
  rw [horbit]
  exact Classical.choose_spec (_root_.AsymptoticAlgebra.quotientMap_surjective B (ρ a))

/-- **Map from strict asymptotic classes to quotient homomorphisms.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. Two families φ,ψ are strictly equivalent when
φ_t(a)-ψ_t(a)→0 in norm as t→∞ for every a∈A. The map strictClassToHom sends the
strict-equivalence class [φ] to the nonunital complex star homomorphism a↦[t↦φ_t(a)] in A→B∞.
-/
def strictClassToHom :
    Quotient (strictSetoid A B) → (A →⋆ₙₐ[ℂ] AsymptoticAlgebra B) :=
  Quotient.lift toHom (fun φ ψ h => (toHom_eq_iff φ ψ).2 h)

/-- **Value of the strict-class homomorphism map.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. For an asymptotic star morphism φ:A→B, write
F_a(t)=φ_t(a) for its bounded continuous coefficient orbit, and Φφ(a)=q_B(F_a). Two families
φ,ψ are strictly equivalent when φ_t(a)-ψ_t(a)→0 in norm as t→∞ for every a∈A. For the
strict-equivalence class [φ], strictClassToHom([φ])=toHom φ.
-/
@[simp]
theorem strictClassToHom_mk (φ : AsymptoticMorphism A B) :
    strictClassToHom (Quotient.mk (strictSetoid A B) φ) = toHom φ := by
  rfl

/-- **Bijection of strict classes with quotient homomorphisms.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. Two families φ,ψ are strictly equivalent when
φ_t(a)-ψ_t(a)→0 in norm as t→∞ for every a∈A. The equivalence strictClassEquiv identifies the
quotient of asymptotic star morphisms A→B by this relation with the nonunital complex star
homomorphisms A→B∞, via [φ]↦(a↦[t↦φ_t(a)]).
-/
def strictClassEquiv :
    Quotient (strictSetoid A B) ≃ (A →⋆ₙₐ[ℂ] AsymptoticAlgebra B) :=
  Equiv.ofBijective strictClassToHom ⟨
    by
      intro q r
      refine Quotient.inductionOn₂ q r ?_
      intro φ ψ h
      rw [strictClassToHom_mk, strictClassToHom_mk] at h
      exact Quotient.sound ((toHom_eq_iff φ ψ).1 h),
    by
      intro ρ
      exact ⟨Quotient.mk (strictSetoid A B) (_root_.AsymptoticAlgebra.ofHom ρ),
        toHom_ofHom ρ⟩⟩

/-- **Value of the strict correspondence on a representative.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. For an asymptotic star morphism φ:A→B, write
F_a(t)=φ_t(a) for its bounded continuous coefficient orbit, and Φφ(a)=q_B(F_a). Two families
φ,ψ are strictly equivalent when φ_t(a)-ψ_t(a)→0 in norm as t→∞ for every a∈A. The bijection
strictClassEquiv sends the strict class of φ to toHom φ, the homomorphism a↦q_B(t↦φ_t(a)).
-/
@[simp]
theorem strictClassEquiv_mk (φ : AsymptoticMorphism A B) :
    strictClassEquiv (Quotient.mk (strictSetoid A B) φ) = toHom φ := by
  rfl


end AsymptoticMorphism

end

end
