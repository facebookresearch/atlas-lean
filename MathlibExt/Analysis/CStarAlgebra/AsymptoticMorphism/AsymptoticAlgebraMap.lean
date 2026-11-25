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
public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.BoundedHom

/-!
# Functoriality of asymptotic quotient algebras

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. A nonunital complex star homomorphism φ:A→B
induces φ∞:A∞→B∞ with φ∞(q_A(F))=q_B(φ∘F). These maps respect composition. The constant
classes c_A(a)=q_A(t↦a) form natural injective coefficient maps: φ∞∘c_A=c_B∘φ.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped BoundedContinuousFunction CStarAlgebra
  NonUnitalStarSubalgebra.Quotient

noncomputable section

namespace AsymptoticAlgebra

universe uA uB uC

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [NonUnitalCStarAlgebra C]

attribute [local instance] cStarAlgebra

/-- **Map induced on asymptotic quotient algebras.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. For a nonunital complex star homomorphism
φ:A→B, map φ:A∞→B∞ sends q_A(F) to q_B(t↦φ(F(t))).
-/
@[no_expose]
def map (φ : A →⋆ₙₐ[ℂ] B) :
    AsymptoticAlgebra A →⋆ₙₐ[ℂ] AsymptoticAlgebra B := by
  let I := BoundedContinuousFunction.vanishingIdeal AsymptoticTime A
  let J := BoundedContinuousFunction.vanishingIdeal AsymptoticTime B
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  let _ : J.carrier.IsTwoSided := J.isTwoSided
  exact NonUnitalStarSubalgebra.Quotient.map I.carrier J.carrier
    (BoundedContinuousFunction.compNonUnitalStarAlgHom
      (X := AsymptoticTime) φ)
    (BoundedContinuousFunction.compNonUnitalStarAlgHom_mapsTo_vanishingIdeal
      (X := AsymptoticTime) φ)

/-- **Induced map on a bounded-function representative.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. For a nonunital complex star homomorphism
φ:A→B and F∈C_b(T,A), map φ (q_A(F))=q_B(φ∘F).
-/
@[simp]
theorem map_quotientMap (φ : A →⋆ₙₐ[ℂ] B)
    (f : AsymptoticTime →ᵇ A) :
    map φ (quotientMap A f) =
      quotientMap B
        (BoundedContinuousFunction.compNonUnitalStarAlgHom φ f) := by
  let I := BoundedContinuousFunction.vanishingIdeal AsymptoticTime A
  let J := BoundedContinuousFunction.vanishingIdeal AsymptoticTime B
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  let _ : J.carrier.IsTwoSided := J.isTwoSided
  exact NonUnitalStarSubalgebra.Quotient.map_mk I.carrier J.carrier
    (BoundedContinuousFunction.compNonUnitalStarAlgHom
      (X := AsymptoticTime) φ)
    (BoundedContinuousFunction.compNonUnitalStarAlgHom_mapsTo_vanishingIdeal
      (X := AsymptoticTime) φ) f

/-- **Induced maps intertwine the quotient projections.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. For a nonunital complex star homomorphism
φ:A→B, (map φ)∘q_A=q_B∘(F↦φ∘F), as nonunital complex star homomorphisms on C_b(T,A).
-/
theorem map_comp_quotientMap (φ : A →⋆ₙₐ[ℂ] B) :
    (map φ).comp (quotientMap A) =
      (quotientMap B).comp
        (BoundedContinuousFunction.compNonUnitalStarAlgHom
          (X := AsymptoticTime) φ) := by
  let I := BoundedContinuousFunction.vanishingIdeal AsymptoticTime A
  let J := BoundedContinuousFunction.vanishingIdeal AsymptoticTime B
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  let _ : J.carrier.IsTwoSided := J.isTwoSided
  exact NonUnitalStarSubalgebra.Quotient.map_comp_mk I.carrier J.carrier
    (BoundedContinuousFunction.compNonUnitalStarAlgHom
      (X := AsymptoticTime) φ)
    (BoundedContinuousFunction.compNonUnitalStarAlgHom_mapsTo_vanishingIdeal
      (X := AsymptoticTime) φ)

@[simp]
theorem map_id (A : Type uA) [NonUnitalCStarAlgebra A] :
    map (NonUnitalStarAlgHom.id ℂ A) =
      NonUnitalStarAlgHom.id ℂ (AsymptoticAlgebra A) := by
  let I := BoundedContinuousFunction.vanishingIdeal AsymptoticTime A
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  apply NonUnitalStarSubalgebra.Quotient.hom_ext I.carrier
  change (map (NonUnitalStarAlgHom.id ℂ A)).comp (quotientMap A) =
    (NonUnitalStarAlgHom.id ℂ (AsymptoticAlgebra A)).comp (quotientMap A)
  rw [map_comp_quotientMap,
    BoundedContinuousFunction.compNonUnitalStarAlgHom_id]
  rfl

@[simp]
theorem map_zero (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    map (0 : A →⋆ₙₐ[ℂ] B) = 0 := by
  let I := BoundedContinuousFunction.vanishingIdeal AsymptoticTime A
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  apply NonUnitalStarSubalgebra.Quotient.hom_ext I.carrier
  change (map (0 : A →⋆ₙₐ[ℂ] B)).comp (quotientMap A) =
    (0 : AsymptoticAlgebra A →⋆ₙₐ[ℂ] AsymptoticAlgebra B).comp (quotientMap A)
  rw [map_comp_quotientMap,
    BoundedContinuousFunction.compNonUnitalStarAlgHom_zero]
  rfl

/-- **Composition of asymptotic quotient maps.**

Let A,B,C be nonunital complex C-star algebras and φ:A→B, ψ:B→C nonunital complex star
homomorphisms. On X∞=C_b([1,∞),X)/C₀([1,∞),X), the induced maps satisfy map(ψ∘φ)=(map ψ)∘(map
φ).
-/
theorem map_comp (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] C) :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  let I := BoundedContinuousFunction.vanishingIdeal AsymptoticTime A
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  apply NonUnitalStarSubalgebra.Quotient.hom_ext I.carrier
  apply NonUnitalStarAlgHom.ext
  intro f
  change map (ψ.comp φ) (quotientMap A f) =
    map ψ (map φ (quotientMap A f))
  simp only [NonUnitalStarAlgHom.comp_apply, map_quotientMap,
    BoundedContinuousFunction.compNonUnitalStarAlgHom_comp]

private def boundedConstantHom
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    A →⋆ₙₐ[ℂ] (AsymptoticTime →ᵇ A) where
  toFun := BoundedContinuousFunction.const AsymptoticTime
  map_zero' := by ext t; rfl
  map_add' _ _ := by ext t; rfl
  map_mul' _ _ := by ext t; rfl
  map_smul' _ _ := by ext t; rfl
  map_star' _ := by ext t; rfl

/-- **Coefficient inclusion by constant asymptotic classes.**

Let A be a nonunital complex C-star algebra, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and q_A its quotient
map. The nonunital complex star homomorphism constantHom A sends a to q_A(t↦a).
-/
@[no_expose]
def constantHom (A : Type uA) [NonUnitalCStarAlgebra A] :
    A →⋆ₙₐ[ℂ] AsymptoticAlgebra A :=
  (quotientMap A).comp (boundedConstantHom A)

@[simp]
theorem constantHom_apply
    (A : Type uA) [NonUnitalCStarAlgebra A] (a : A) :
    constantHom A a =
      quotientMap A
        (BoundedContinuousFunction.const AsymptoticTime a) := by
  rfl

private theorem comp_constant
    (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    BoundedContinuousFunction.compNonUnitalStarAlgHom φ
        (BoundedContinuousFunction.const AsymptoticTime a) =
      BoundedContinuousFunction.const AsymptoticTime (φ a) := by
  ext t
  rw [BoundedContinuousFunction.compNonUnitalStarAlgHom_apply]
  rfl

/-- **Naturality of constant coefficient classes.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. For a nonunital complex star homomorphism
φ:A→B and c_X(x)=q_X(t↦x), (map φ)∘c_A=c_B∘φ.
-/
theorem map_comp_constantHom (φ : A →⋆ₙₐ[ℂ] B) :
    (map φ).comp (constantHom A) = (constantHom B).comp φ := by
  ext a
  simp only [NonUnitalStarAlgHom.comp_apply, constantHom_apply,
    map_quotientMap, comp_constant]

/-- **A constant asymptotic class is zero exactly for the zero coefficient.**

Let A be a nonunital complex C-star algebra, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and q_A its quotient
map. For a∈A, constantHom A a=q_A(t↦a)=0 if and only if a=0.
-/
theorem constantHom_eq_zero_iff
    (A : Type uA) [NonUnitalCStarAlgebra A] (a : A) :
    constantHom A a = 0 ↔ a = 0 := by
  let _ : Nonempty AsymptoticTime := ⟨⟨1, le_rfl⟩⟩
  let _ : NeBot (atTop : Filter AsymptoticTime) := Filter.atTop_neBot
  constructor
  · intro h
    rw [constantHom_apply] at h
    have ht := (quotientMap_eq_zero_iff
      (BoundedContinuousFunction.const AsymptoticTime a)).1 h
    exact tendsto_nhds_unique
      (tendsto_const_nhds :
        Tendsto (fun _ : AsymptoticTime => a) atTop (nhds a)) ht
  · rintro rfl
    exact _root_.map_zero (constantHom A)

/-- **Injectivity of the constant-class coefficient map.**

Let A be a nonunital complex C-star algebra. The map constantHom A:A→C_b([1,∞),A)/C₀([1,∞),A),
a↦[t↦a], is injective, including when A is zero.
-/
theorem constantHom_injective
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    Function.Injective (constantHom A) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply (constantHom_eq_zero_iff A (a - b)).1
  rw [map_sub, hab, sub_self]


end AsymptoticAlgebra
