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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.NHomotopy
public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.Hom

/-!
# Functoriality of literal finite-stage homotopy classes

Literal `n`-homotopy classes are contravariant in the source and covariant in
the coefficient algebra. Applying alpha to a representative also gives a
canonical class at the next stage with source `alpha A` and the same
coefficient algebra `B`.

This module does not define the disputed printed map to
`[[alpha A, alpha B]]_(n+1)`, products, direct limits, or flattening.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

attribute [local instance] AsymptoticAlgebra.cStarAlgebra

namespace IteratedAsymptoticAlgebra

universe uA uA' uA'' uB uC uD

/-! ## Source precomposition -/

/-- Precompose a finite-stage representative in its source algebra. -/
def precompRepresentative (n : ℕ)
    {A : Type uA} {A' : Type uA'} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
    [NonUnitalCStarAlgebra B]
    (u : A' →⋆ₙₐ[ℂ] A) (φ : HomN n A B) : HomN n A' B :=
  φ.comp u

@[simp]
theorem precompRepresentative_apply (n : ℕ)
    {A : Type uA} {A' : Type uA'} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
    [NonUnitalCStarAlgebra B]
    (u : A' →⋆ₙₐ[ℂ] A) (φ : HomN n A B) (a : A') :
    precompRepresentative n u φ a = φ (u a) :=
  rfl

theorem precompRepresentative_id (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : HomN n A B) :
    precompRepresentative n (NonUnitalStarAlgHom.id ℂ A) φ = φ := by
  apply NonUnitalStarAlgHom.ext
  intro a
  rfl

theorem precompRepresentative_comp (n : ℕ)
    {A : Type uA} {A' : Type uA'} {A'' : Type uA''} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
    [NonUnitalCStarAlgebra A''] [NonUnitalCStarAlgebra B]
    (u : A' →⋆ₙₐ[ℂ] A) (v : A'' →⋆ₙₐ[ℂ] A')
    (φ : HomN n A B) :
    precompRepresentative n v (precompRepresentative n u φ) =
      precompRepresentative n (u.comp v) φ :=
  NonUnitalStarAlgHom.comp_assoc φ u v

/-- Source precomposition preserves literal finite-stage homotopy. -/
theorem precompRepresentative_respects (n : ℕ)
    {A : Type uA} {A' : Type uA'} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
    [NonUnitalCStarAlgebra B]
    (u : A' →⋆ₙₐ[ℂ] A) {φ ψ : HomN n A B}
    (h : HomotopicN n φ ψ) :
    HomotopicN n (precompRepresentative n u φ)
      (precompRepresentative n u ψ) := by
  obtain ⟨H, h0, h1⟩ := h
  refine ⟨precompRepresentative n u H, ?_, ?_⟩
  · unfold precompRepresentative
    rw [← NonUnitalStarAlgHom.comp_assoc, h0]
  · unfold precompRepresentative
    rw [← NonUnitalStarAlgHom.comp_assoc, h1]

/-- Source precomposition on literal finite-stage homotopy classes. -/
def precompClass (n : ℕ)
    {A : Type uA} {A' : Type uA'} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
    [NonUnitalCStarAlgebra B]
    (u : A' →⋆ₙₐ[ℂ] A) : NClasses n A B → NClasses n A' B :=
  Quotient.map (precompRepresentative n u)
    (fun _ _ h => precompRepresentative_respects n u h)

@[simp]
theorem precompClass_classOf (n : ℕ)
    {A : Type uA} {A' : Type uA'} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
    [NonUnitalCStarAlgebra B]
    (u : A' →⋆ₙₐ[ℂ] A) (φ : HomN n A B) :
    precompClass n u (classOf n φ) =
      classOf n (precompRepresentative n u φ) :=
  rfl

theorem precompClass_id (n : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    precompClass n (B := B) (NonUnitalStarAlgHom.id ℂ A) =
      id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro φ
  change precompClass n (B := B) (NonUnitalStarAlgHom.id ℂ A)
    (classOf n φ) = classOf n φ
  rw [precompClass_classOf, precompRepresentative_id]

theorem precompClass_comp (n : ℕ)
    {A : Type uA} {A' : Type uA'} {A'' : Type uA''} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
    [NonUnitalCStarAlgebra A''] [NonUnitalCStarAlgebra B]
    (u : A' →⋆ₙₐ[ℂ] A) (v : A'' →⋆ₙₐ[ℂ] A')
    (q : NClasses n A B) :
    precompClass n v (precompClass n u q) =
      precompClass n (u.comp v) q := by
  refine Quotient.inductionOn q ?_
  intro φ
  change precompClass n v (precompClass n u (classOf n φ)) =
    precompClass n (u.comp v) (classOf n φ)
  rw [precompClass_classOf, precompClass_classOf,
    precompClass_classOf, precompRepresentative_comp]

/-! ## Coefficient postcomposition -/

/-- Iterated endpoint evaluation is natural under pointwise coefficient
postcomposition. -/
theorem endpointHom_comp_postcompPathMap (n : ℕ) (t : unitInterval)
    {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    (g : B →⋆ₙₐ[ℂ] C) :
    (AsymptoticAlgebra.endpointHom n t C).comp
        (map n (ContinuousMap.compNonUnitalStarAlgHom unitInterval g)) =
      (map n g).comp (AsymptoticAlgebra.endpointHom n t B) := by
  have hbase :
      (ContinuousMap.IntervalGluing.evalAt C t).comp
          (ContinuousMap.compNonUnitalStarAlgHom unitInterval g) =
        g.comp (ContinuousMap.IntervalGluing.evalAt B t) := by
    apply NonUnitalStarAlgHom.ext
    intro f
    rfl
  rw [AsymptoticAlgebra.endpointHom_eq,
    AsymptoticAlgebra.endpointHom_eq,
    ← map_comp, hbase, map_comp]

/-- Postcompose a finite-stage representative in its coefficient algebra. -/
def postcompRepresentative (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (g : B →⋆ₙₐ[ℂ] C) (φ : HomN n A B) : HomN n A C :=
  (map n g).comp φ

@[simp]
theorem postcompRepresentative_apply (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (g : B →⋆ₙₐ[ℂ] C) (φ : HomN n A B) (a : A) :
    postcompRepresentative n g φ a = map n g (φ a) :=
  rfl

theorem postcompRepresentative_id (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : HomN n A B) :
    postcompRepresentative n (NonUnitalStarAlgHom.id ℂ B) φ = φ := by
  unfold postcompRepresentative
  rw [map_id]
  apply NonUnitalStarAlgHom.ext
  intro a
  rfl

theorem postcompRepresentative_comp (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    (g : B →⋆ₙₐ[ℂ] C) (h : C →⋆ₙₐ[ℂ] D)
    (φ : HomN n A B) :
    postcompRepresentative n h (postcompRepresentative n g φ) =
      postcompRepresentative n (h.comp g) φ := by
  unfold postcompRepresentative
  calc
    (map n h).comp ((map n g).comp φ) =
        ((map n h).comp (map n g)).comp φ :=
      (NonUnitalStarAlgHom.comp_assoc _ _ _).symm
    _ = (map n (h.comp g)).comp φ :=
      congrArg (fun k => k.comp φ) (map_comp n g h).symm

/-- Coefficient postcomposition preserves literal finite-stage homotopy. -/
theorem postcompRepresentative_respects (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (g : B →⋆ₙₐ[ℂ] C) {φ ψ : HomN n A B}
    (h : HomotopicN n φ ψ) :
    HomotopicN n (postcompRepresentative n g φ)
      (postcompRepresentative n g ψ) := by
  obtain ⟨H, h0, h1⟩ := h
  let gI : C(unitInterval, B) →⋆ₙₐ[ℂ] C(unitInterval, C) :=
    ContinuousMap.compNonUnitalStarAlgHom unitInterval g
  refine ⟨(map n gI).comp H, ?_, ?_⟩
  · calc
      (AsymptoticAlgebra.endpointHom n 0 C).comp ((map n gI).comp H) =
          ((AsymptoticAlgebra.endpointHom n 0 C).comp (map n gI)).comp H :=
        (NonUnitalStarAlgHom.comp_assoc _ _ _).symm
      _ = ((map n g).comp (AsymptoticAlgebra.endpointHom n 0 B)).comp H :=
        congrArg (fun k => k.comp H)
          (endpointHom_comp_postcompPathMap n 0 g)
      _ = (map n g).comp
          ((AsymptoticAlgebra.endpointHom n 0 B).comp H) :=
        NonUnitalStarAlgHom.comp_assoc _ _ _
      _ = (map n g).comp φ := congrArg (fun k => (map n g).comp k) h0
      _ = postcompRepresentative n g φ := rfl
  · calc
      (AsymptoticAlgebra.endpointHom n 1 C).comp ((map n gI).comp H) =
          ((AsymptoticAlgebra.endpointHom n 1 C).comp (map n gI)).comp H :=
        (NonUnitalStarAlgHom.comp_assoc _ _ _).symm
      _ = ((map n g).comp (AsymptoticAlgebra.endpointHom n 1 B)).comp H :=
        congrArg (fun k => k.comp H)
          (endpointHom_comp_postcompPathMap n 1 g)
      _ = (map n g).comp
          ((AsymptoticAlgebra.endpointHom n 1 B).comp H) :=
        NonUnitalStarAlgHom.comp_assoc _ _ _
      _ = (map n g).comp ψ := congrArg (fun k => (map n g).comp k) h1
      _ = postcompRepresentative n g ψ := rfl

/-- Coefficient postcomposition on literal finite-stage homotopy classes. -/
def postcompClass (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (g : B →⋆ₙₐ[ℂ] C) : NClasses n A B → NClasses n A C :=
  Quotient.map (postcompRepresentative n g)
    (fun _ _ h => postcompRepresentative_respects n g h)

@[simp]
theorem postcompClass_classOf (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (g : B →⋆ₙₐ[ℂ] C) (φ : HomN n A B) :
    postcompClass n g (classOf n φ) =
      classOf n (postcompRepresentative n g φ) :=
  rfl

theorem postcompClass_id (n : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    postcompClass n (A := A) (NonUnitalStarAlgHom.id ℂ B) =
      id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro φ
  change postcompClass n (A := A) (NonUnitalStarAlgHom.id ℂ B)
    (classOf n φ) = classOf n φ
  rw [postcompClass_classOf, postcompRepresentative_id]

theorem postcompClass_comp (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    (g : B →⋆ₙₐ[ℂ] C) (h : C →⋆ₙₐ[ℂ] D)
    (q : NClasses n A B) :
    postcompClass n h (postcompClass n g q) =
      postcompClass n (h.comp g) q := by
  refine Quotient.inductionOn q ?_
  intro φ
  change postcompClass n h (postcompClass n g (classOf n φ)) =
    postcompClass n (h.comp g) (classOf n φ)
  rw [postcompClass_classOf, postcompClass_classOf,
    postcompClass_classOf, postcompRepresentative_comp]

/-! ## Literal alpha at the next stage -/

/-- Applying alpha to a representative, with its unambiguous next-stage
target and unchanged coefficient algebra. -/
def alphaNextRepresentative (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : HomN n A B) :
    HomN (n + 1) (AsymptoticAlgebra A) B :=
  alphaRepresentative n φ

theorem alphaNextRepresentative_eq (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : HomN n A B) :
    alphaNextRepresentative n φ = alphaRepresentative n φ :=
  rfl

/-- Iterated endpoint evaluation commutes with literal alpha on a
representative. -/
theorem endpointHom_comp_alphaNextRepresentative (n : ℕ)
    (t : unitInterval)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (H : HomN n A C(unitInterval, B)) :
    (AsymptoticAlgebra.endpointHom (n + 1) t B).comp
        (alphaNextRepresentative n H) =
      alphaNextRepresentative n
        ((AsymptoticAlgebra.endpointHom n t B).comp H) := by
  rw [alphaNextRepresentative_eq, alphaNextRepresentative_eq,
    alphaRepresentative_eq, alphaRepresentative_eq,
    AsymptoticAlgebra.endpointHom_eq,
    AsymptoticAlgebra.endpointHom_eq,
    IteratedAsymptoticAlgebra.map_succ]
  exact (AsymptoticAlgebra.map_comp H
    (IteratedAsymptoticAlgebra.map n
      (ContinuousMap.IntervalGluing.evalAt B t))).symm

/-- Literal alpha preserves finite-stage homotopy at its unambiguous target. -/
theorem alphaNextRepresentative_respects (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {φ ψ : HomN n A B} (h : HomotopicN n φ ψ) :
    HomotopicN (n + 1) (alphaNextRepresentative n φ)
      (alphaNextRepresentative n ψ) := by
  obtain ⟨H, h0, h1⟩ := h
  refine ⟨alphaNextRepresentative n H, ?_, ?_⟩
  · rw [endpointHom_comp_alphaNextRepresentative, h0]
  · rw [endpointHom_comp_alphaNextRepresentative, h1]

/-- Literal alpha on finite-stage homotopy classes, targeting the next stage
with source `alpha A` and unchanged coefficient algebra `B`. -/
def alphaNextClass (n : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    NClasses n A B → NClasses (n + 1) (AsymptoticAlgebra A) B :=
  Quotient.map (alphaNextRepresentative n)
    (fun _ _ h => alphaNextRepresentative_respects n h)

@[simp]
theorem alphaNextClass_classOf (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : HomN n A B) :
    alphaNextClass n A B (classOf n φ) =
      classOf (n + 1) (alphaNextRepresentative n φ) :=
  rfl

#print axioms precompClass
#print axioms postcompClass
#print axioms endpointHom_comp_postcompPathMap
#print axioms alphaNextRepresentative
#print axioms alphaNextRepresentative_respects
#print axioms alphaNextClass

end IteratedAsymptoticAlgebra
