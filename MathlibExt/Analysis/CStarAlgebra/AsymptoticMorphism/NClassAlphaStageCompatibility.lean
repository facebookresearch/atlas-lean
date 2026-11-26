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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.NClassFunctoriality

/-!
# Naturality of the asymptotic next-stage class map

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For a representative φ:A→αⁿB, let a_n(φ)=αφ:αA→α(αⁿB)=αⁿ⁺¹B. It induces
a_n:Q_n(A,B)→Q_(n+1)(αA,B), called alphaNextClass. For nonunital complex star homomorphisms
u:A′→A and g:B→C between nonunital complex C-star algebras, this map commutes with source
precomposition by αu and coefficient postcomposition by αⁿ⁺¹g. Restricting its source along
c_A:A→αA, a↦[t↦a], recovers the constant-class successor transition Q_n(A,B)→Q_(n+1)(A,B).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

attribute [local instance] AsymptoticAlgebra.cStarAlgebra

namespace IteratedAsymptoticAlgebra

universe uA uA' uB uC

/-!
## Naturality in the source algebra

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For a representative φ:A→αⁿB, let a_n(φ)=αφ:αA→α(αⁿB)=αⁿ⁺¹B. It induces
a_n:Q_n(A,B)→Q_(n+1)(αA,B), called alphaNextClass. For u:A′→A, the next-stage map sends [φ∘u]
to [αφ∘αu].
-/

/-- **Source precomposition and the next-stage representative.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For a representative φ:A→αⁿB, let a_n(φ)=αφ:αA→α(αⁿB)=αⁿ⁺¹B. It induces
a_n:Q_n(A,B)→Q_(n+1)(αA,B), called alphaNextClass. For a star homomorphism u:A′→A from a
nonunital complex C-star algebra, a_n(φ∘u)=a_n(φ)∘αu.
-/
theorem alphaNextRepresentative_precomp (n : ℕ)
    {A : Type uA} {A' : Type uA'} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
    [NonUnitalCStarAlgebra B]
    (u : A' →⋆ₙₐ[ℂ] A) (phi : HomN n A B) :
    alphaNextRepresentative n (precompRepresentative n u phi) =
      precompRepresentative (n + 1) (AsymptoticAlgebra.map u)
        (alphaNextRepresentative n phi) := by
  have hpre :
      precompRepresentative n u phi = phi.comp u := by
    apply NonUnitalStarAlgHom.ext
    intro a
    rw [precompRepresentative_apply,
      NonUnitalStarAlgHom.comp_apply]
  apply NonUnitalStarAlgHom.ext
  intro x
  rw [hpre, precompRepresentative_apply,
    alphaNextRepresentative_eq, alphaRepresentative_eq,
    alphaNextRepresentative_eq, alphaRepresentative_eq]
  exact DFunLike.congr_fun (AsymptoticAlgebra.map_comp u phi) x

/-- **Source naturality of the next-stage class map.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For a representative φ:A→αⁿB, let a_n(φ)=αφ:αA→α(αⁿB)=αⁿ⁺¹B. It induces
a_n:Q_n(A,B)→Q_(n+1)(αA,B), called alphaNextClass. For a star homomorphism u:A′→A from a
nonunital complex C-star algebra and q∈Q_n(A,B), alphaNextClass(precompClass n u
q)=precompClass(n+1)(αu)(alphaNextClass q), with target Q_(n+1)(αA′,B).
-/
theorem alphaNextClass_precomp (n : ℕ)
    {A : Type uA} {A' : Type uA'} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
    [NonUnitalCStarAlgebra B]
    (u : A' →⋆ₙₐ[ℂ] A) (q : NClasses n A B) :
    alphaNextClass n A' B (precompClass n u q) =
      precompClass (n + 1) (B := B) (AsymptoticAlgebra.map u)
        (alphaNextClass n A B q) := by
  refine Quotient.inductionOn q ?_
  intro phi
  change alphaNextClass n A' B (precompClass n u (classOf n phi)) =
    precompClass (n + 1) (B := B) (AsymptoticAlgebra.map u)
      (alphaNextClass n A B (classOf n phi))
  rw [precompClass_classOf, alphaNextClass_classOf,
    alphaNextClass_classOf, precompClass_classOf,
    alphaNextRepresentative_precomp]

/-!
## Naturality in the coefficient algebra

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For a representative φ:A→αⁿB, let a_n(φ)=αφ:αA→α(αⁿB)=αⁿ⁺¹B. It induces
a_n:Q_n(A,B)→Q_(n+1)(αA,B), called alphaNextClass. For a star homomorphism g:B→C, applying α
to αⁿg∘φ gives αⁿ⁺¹g∘αφ.
-/

/-- **Coefficient postcomposition and the next-stage representative.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For a representative φ:A→αⁿB, let a_n(φ)=αφ:αA→α(αⁿB)=αⁿ⁺¹B. It induces
a_n:Q_n(A,B)→Q_(n+1)(αA,B), called alphaNextClass. For a star homomorphism g:B→C into a
nonunital complex C-star algebra, a_n(αⁿg∘φ)=αⁿ⁺¹g∘a_n(φ).
-/
theorem alphaNextRepresentative_postcomp (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (g : B →⋆ₙₐ[ℂ] C) (phi : HomN n A B) :
    alphaNextRepresentative n (postcompRepresentative n g phi) =
      postcompRepresentative (n + 1) g
        (alphaNextRepresentative n phi) := by
  have hpost :
      postcompRepresentative n g phi = (map n g).comp phi := by
    apply NonUnitalStarAlgHom.ext
    intro a
    rw [postcompRepresentative_apply,
      NonUnitalStarAlgHom.comp_apply]
  apply NonUnitalStarAlgHom.ext
  intro x
  rw [hpost, postcompRepresentative_apply,
    alphaNextRepresentative_eq, alphaRepresentative_eq,
    alphaNextRepresentative_eq, alphaRepresentative_eq,
    map_succ]
  exact DFunLike.congr_fun
    (AsymptoticAlgebra.map_comp phi (map n g)) x

/-- **Coefficient naturality of the next-stage class map.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For a representative φ:A→αⁿB, let a_n(φ)=αφ:αA→α(αⁿB)=αⁿ⁺¹B. It induces
a_n:Q_n(A,B)→Q_(n+1)(αA,B), called alphaNextClass. For a star homomorphism g:B→C into a
nonunital complex C-star algebra and q∈Q_n(A,B), alphaNextClass(postcompClass n g
q)=postcompClass(n+1) g (alphaNextClass q), with target Q_(n+1)(αA,C).
-/
theorem alphaNextClass_postcomp (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (g : B →⋆ₙₐ[ℂ] C) (q : NClasses n A B) :
    alphaNextClass n A C (postcompClass n g q) =
      postcompClass (n + 1) (A := AsymptoticAlgebra A) g
        (alphaNextClass n A B q) := by
  refine Quotient.inductionOn q ?_
  intro phi
  change alphaNextClass n A C (postcompClass n g (classOf n phi)) =
    postcompClass (n + 1) (A := AsymptoticAlgebra A) g
      (alphaNextClass n A B (classOf n phi))
  rw [postcompClass_classOf, alphaNextClass_classOf,
    alphaNextClass_classOf, postcompClass_classOf,
    alphaNextRepresentative_postcomp]

/-!
## Restriction along constant source classes

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For a representative φ:A→αⁿB, let a_n(φ)=αφ:αA→α(αⁿB)=αⁿ⁺¹B. It induces
a_n:Q_n(A,B)→Q_(n+1)(αA,B), called alphaNextClass. For c_A(a)=[t↦a], the restriction αφ∘c_A is
c_(αⁿB)∘φ, the successor-stage representative.
-/

/-- **Next-stage representative restricted to constant source classes.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For a representative φ:A→αⁿB, let a_n(φ)=αφ:αA→α(αⁿB)=αⁿ⁺¹B. It induces
a_n:Q_n(A,B)→Q_(n+1)(αA,B), called alphaNextClass. With c_X(x)=[t↦x]∈αX,
a_n(φ)∘c_A=stageTransitionRepresentative n φ=c_(αⁿB)∘φ.
-/
theorem alphaNextRepresentative_precomp_constantHom (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : HomN n A B) :
    precompRepresentative (n + 1) (AsymptoticAlgebra.constantHom A)
        (alphaNextRepresentative n phi) =
      stageTransitionRepresentative n phi := by
  apply NonUnitalStarAlgHom.ext
  intro a
  rw [precompRepresentative_apply,
    alphaNextRepresentative_eq, alphaRepresentative_eq,
    stageTransitionRepresentative_apply,
    stageHom_eq_constantHom]
  exact DFunLike.congr_fun
    (AsymptoticAlgebra.map_comp_constantHom phi) a

/-- **Next-stage classes recover the successor transition on constants.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For a representative φ:A→αⁿB, let a_n(φ)=αφ:αA→α(αⁿB)=αⁿ⁺¹B. It induces
a_n:Q_n(A,B)→Q_(n+1)(αA,B), called alphaNextClass. For c_A:A→αA, precompClass(n+1)
c_A∘alphaNextClass n A B=stageTransition n A B, as maps Q_n(A,B)→Q_(n+1)(A,B).
-/
theorem precompClass_comp_alphaNextClass (n : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    Function.comp
        (precompClass (n + 1) (B := B)
          (AsymptoticAlgebra.constantHom A))
        (alphaNextClass n A B) =
      stageTransition n A B := by
  funext q
  change
    precompClass (n + 1) (B := B)
        (AsymptoticAlgebra.constantHom A)
        (alphaNextClass n A B q) =
      stageTransition n A B q
  refine Quotient.inductionOn q ?_
  intro phi
  change precompClass (n + 1) (B := B) (AsymptoticAlgebra.constantHom A)
    (alphaNextClass n A B (classOf n phi)) =
    stageTransition n A B (classOf n phi)
  rw [alphaNextClass_classOf, precompClass_classOf,
    stageTransition_classOf,
    alphaNextRepresentative_precomp_constantHom]


end IteratedAsymptoticAlgebra
