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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.IteratedAlgebra
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.IteratedMatchingPaths

/-!
# Homotopy classes at finite asymptotic stages

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star norm, and
define α⁰X=X, αⁿ⁺¹X=α(αⁿX). Write HomN n A B for nonunital complex star homomorphisms φ:A→αⁿB.
For φ,ψ∈HomN n A B, n-homotopy means that there is a star homomorphism F:A→αⁿ(C([0,1],B)) with
αⁿ(ev_0)∘F=φ and αⁿ(ev_1)∘F=ψ, where ev_s evaluates a continuous interval path at s. Constant
interval paths, reversal and matching-path concatenation make n-homotopy an equivalence
relation. The quotient is NClasses n A B, with a successor transition induced by constant
classes in the next quotient.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

attribute [local instance] AsymptoticAlgebra.cStarAlgebra

namespace IteratedAsymptoticAlgebra

universe uA uB

/-!
## Finite-stage constant paths and reversal

For a nonunital complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient
C-star norm, and define α⁰X=X, αⁿ⁺¹X=α(αⁿX). For a nonunital complex C-star algebra B, the
maps αⁿ(B→C([0,1],B)) and αⁿ(h(s)↦h(1-s)) give constant paths and reversal at stage n.
-/

/-- **Constant path homomorphism at finite stage.**

For a nonunital complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient
C-star norm, and define α⁰X=X, αⁿ⁺¹X=α(αⁿX). For B a nonunital complex C-star algebra and n∈ℕ,
constantPathHomN n B:αⁿB→αⁿ(C([0,1],B)) is αⁿ of the map b↦(s↦b).
-/
@[no_expose]
def constantPathHomN (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    IteratedAsymptoticAlgebra n B →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra n C(unitInterval, B) :=
  map n (ContinuousMap.IntervalGluing.constantHom B)

/-- **Interval reversal at finite stage.**

For a nonunital complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient
C-star norm, and define α⁰X=X, αⁿ⁺¹X=α(αⁿX). For B a nonunital complex C-star algebra and n∈ℕ,
reversePathHomN n B:αⁿ(C([0,1],B))→αⁿ(C([0,1],B)) is αⁿ of the path map h(s)↦h(1-s).
-/
@[no_expose]
def reversePathHomN (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    IteratedAsymptoticAlgebra n C(unitInterval, B) →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra n C(unitInterval, B) :=
  map n (ContinuousMap.IntervalGluing.reverseHom B)

private theorem evalAt_comp_constantHom (t : unitInterval)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (ContinuousMap.IntervalGluing.evalAt B t).comp
        (ContinuousMap.IntervalGluing.constantHom B) =
      NonUnitalStarAlgHom.id ℂ B := by
  apply NonUnitalStarAlgHom.ext
  intro b
  rfl

private theorem evalAt_zero_comp_reverseHom
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (ContinuousMap.IntervalGluing.evalAt B 0).comp
        (ContinuousMap.IntervalGluing.reverseHom B) =
      ContinuousMap.IntervalGluing.evalAt B 1 := by
  apply NonUnitalStarAlgHom.ext
  intro f
  exact ContinuousMap.IntervalGluing.reverseHom_zero (B := B) f

private theorem evalAt_one_comp_reverseHom
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (ContinuousMap.IntervalGluing.evalAt B 1).comp
        (ContinuousMap.IntervalGluing.reverseHom B) =
      ContinuousMap.IntervalGluing.evalAt B 0 := by
  apply NonUnitalStarAlgHom.ext
  intro f
  exact ContinuousMap.IntervalGluing.reverseHom_one (B := B) f

@[simp]
theorem endpointHom_comp_constantPathHomN (n : ℕ) (t : unitInterval)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (AsymptoticAlgebra.endpointHom n t B).comp (constantPathHomN n B) =
      NonUnitalStarAlgHom.id ℂ (IteratedAsymptoticAlgebra n B) := by
  unfold constantPathHomN
  rw [AsymptoticAlgebra.endpointHom_eq, ← map_comp,
    evalAt_comp_constantHom, map_id]

@[simp]
theorem endpointHom_zero_comp_reversePathHomN (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (AsymptoticAlgebra.endpointHom n 0 B).comp (reversePathHomN n B) =
      AsymptoticAlgebra.endpointHom n 1 B := by
  unfold reversePathHomN
  rw [AsymptoticAlgebra.endpointHom_eq, ← map_comp,
    evalAt_zero_comp_reverseHom, ← AsymptoticAlgebra.endpointHom_eq]

@[simp]
theorem endpointHom_one_comp_reversePathHomN (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (AsymptoticAlgebra.endpointHom n 1 B).comp (reversePathHomN n B) =
      AsymptoticAlgebra.endpointHom n 0 B := by
  unfold reversePathHomN
  rw [AsymptoticAlgebra.endpointHom_eq, ← map_comp,
    evalAt_one_comp_reverseHom, ← AsymptoticAlgebra.endpointHom_eq]

/-!
## Finite-stage homotopy relation

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star norm, and
define α⁰X=X, αⁿ⁺¹X=α(αⁿX). Write HomN n A B for nonunital complex star homomorphisms φ:A→αⁿB.
For φ,ψ∈HomN n A B, n-homotopy means that there is a star homomorphism F:A→αⁿ(C([0,1],B)) with
αⁿ(ev_0)∘F=φ and αⁿ(ev_1)∘F=ψ, where ev_s evaluates a continuous interval path at s.
-/

/-- **Homotopy through the iterated interval algebra.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star norm, and
define α⁰X=X, αⁿ⁺¹X=α(αⁿX). Write HomN n A B for nonunital complex star homomorphisms φ:A→αⁿB.
For φ,ψ∈HomN n A B, n-homotopy means that there is a star homomorphism F:A→αⁿ(C([0,1],B)) with
αⁿ(ev_0)∘F=φ and αⁿ(ev_1)∘F=ψ, where ev_s evaluates a continuous interval path at s. This is
the proposition HomotopicN n φ ψ.
-/
def HomotopicN (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ ψ : HomN n A B) : Prop :=
  ∃ H : HomN n A C(unitInterval, B),
    (AsymptoticAlgebra.endpointHom n 0 B).comp H = φ ∧
      (AsymptoticAlgebra.endpointHom n 1 B).comp H = ψ

namespace HomotopicN

variable {n : ℕ} {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Reflexivity of finite-stage homotopy.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star norm, and
define α⁰X=X, αⁿ⁺¹X=α(αⁿX). Write HomN n A B for nonunital complex star homomorphisms φ:A→αⁿB.
For φ,ψ∈HomN n A B, n-homotopy means that there is a star homomorphism F:A→αⁿ(C([0,1],B)) with
αⁿ(ev_0)∘F=φ and αⁿ(ev_1)∘F=ψ, where ev_s evaluates a continuous interval path at s. Every
representative φ∈HomN n A B is n-homotopic to itself through the constant path map.
-/
theorem refl (φ : HomN n A B) : HomotopicN n φ φ := by
  refine ⟨(constantPathHomN n B).comp φ, ?_, ?_⟩
  · rw [← NonUnitalStarAlgHom.comp_assoc,
      endpointHom_comp_constantPathHomN]
    rfl
  · rw [← NonUnitalStarAlgHom.comp_assoc,
      endpointHom_comp_constantPathHomN]
    rfl

/-- **Symmetry of finite-stage homotopy.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star norm, and
define α⁰X=X, αⁿ⁺¹X=α(αⁿX). Write HomN n A B for nonunital complex star homomorphisms φ:A→αⁿB.
For φ,ψ∈HomN n A B, n-homotopy means that there is a star homomorphism F:A→αⁿ(C([0,1],B)) with
αⁿ(ev_0)∘F=φ and αⁿ(ev_1)∘F=ψ, where ev_s evaluates a continuous interval path at s. If φ and
ψ are n-homotopic, then ψ and φ are n-homotopic by interval reversal.
-/
theorem symm {φ ψ : HomN n A B} (h : HomotopicN n φ ψ) :
    HomotopicN n ψ φ := by
  obtain ⟨H, h0, h1⟩ := h
  refine ⟨(reversePathHomN n B).comp H, ?_, ?_⟩
  · rw [← NonUnitalStarAlgHom.comp_assoc,
      endpointHom_zero_comp_reversePathHomN]
    exact h1
  · rw [← NonUnitalStarAlgHom.comp_assoc,
      endpointHom_one_comp_reversePathHomN]
    exact h0

/-- **Transitivity of finite-stage homotopy.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star norm, and
define α⁰X=X, αⁿ⁺¹X=α(αⁿX). Write HomN n A B for nonunital complex star homomorphisms φ:A→αⁿB.
For φ,ψ∈HomN n A B, n-homotopy means that there is a star homomorphism F:A→αⁿ(C([0,1],B)) with
αⁿ(ev_0)∘F=φ and αⁿ(ev_1)∘F=ψ, where ev_s evaluates a continuous interval path at s. If φ is
n-homotopic to ψ and ψ to χ, then φ is n-homotopic to χ by matching-path gluing at stage n.
-/
theorem trans {φ ψ χ : HomN n A B}
    (hφψ : HomotopicN n φ ψ) (hψχ : HomotopicN n ψ χ) :
    HomotopicN n φ χ := by
  obtain ⟨H₀₁, h₀, h₁⟩ := hφψ
  obtain ⟨H₁₂, h₁', h₂⟩ := hψχ
  have hmatch :
      (AsymptoticAlgebra.endpointHom n 1 B).comp H₀₁ =
        (AsymptoticAlgebra.endpointHom n 0 B).comp H₁₂ :=
    h₁.trans h₁'.symm
  let P : A →⋆ₙₐ[ℂ] AsymptoticAlgebra.IteratedMatchingPaths n B :=
    NonUnitalCStarPullback.lift
      (AsymptoticAlgebra.endpointHom n 1 B)
      (AsymptoticAlgebra.endpointHom n 0 B) H₀₁ H₁₂ hmatch
  refine ⟨(AsymptoticAlgebra.glueHomN n B).comp P, ?_, ?_⟩
  · dsimp only [P]
    rw [← NonUnitalStarAlgHom.comp_assoc,
      AsymptoticAlgebra.endpointHom_zero_comp_glueHomN,
      NonUnitalStarAlgHom.comp_assoc,
      NonUnitalCStarPullback.fstHom_comp_lift, h₀]
  · dsimp only [P]
    rw [← NonUnitalStarAlgHom.comp_assoc,
      AsymptoticAlgebra.endpointHom_one_comp_glueHomN,
      NonUnitalStarAlgHom.comp_assoc,
      NonUnitalCStarPullback.sndHom_comp_lift, h₂]

end HomotopicN

/-!
## Quotient by finite-stage homotopy

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star norm, and
define α⁰X=X, αⁿ⁺¹X=α(αⁿX). Write HomN n A B for nonunital complex star homomorphisms φ:A→αⁿB.
For φ,ψ∈HomN n A B, n-homotopy means that there is a star homomorphism F:A→αⁿ(C([0,1],B)) with
αⁿ(ev_0)∘F=φ and αⁿ(ev_1)∘F=ψ, where ev_s evaluates a continuous interval path at s. The
equivalence relation defines the quotient NClasses n A B.
-/

/-- **Setoid of finite-stage homotopy.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star norm, and
define α⁰X=X, αⁿ⁺¹X=α(αⁿX). Write HomN n A B for nonunital complex star homomorphisms φ:A→αⁿB.
For φ,ψ∈HomN n A B, n-homotopy means that there is a star homomorphism F:A→αⁿ(C([0,1],B)) with
αⁿ(ev_0)∘F=φ and αⁿ(ev_1)∘F=ψ, where ev_s evaluates a continuous interval path at s. The
setoid homotopicNSetoid n A B has relation HomotopicN n.
-/
def homotopicNSetoid (n : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    Setoid (HomN n A B) where
  r := HomotopicN n
  iseqv :=
    { refl := HomotopicN.refl
      symm := HomotopicN.symm
      trans := HomotopicN.trans }

/-- **Finite-stage homotopy class space.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star norm, and
define α⁰X=X, αⁿ⁺¹X=α(αⁿX). Write HomN n A B for nonunital complex star homomorphisms φ:A→αⁿB.
For φ,ψ∈HomN n A B, n-homotopy means that there is a star homomorphism F:A→αⁿ(C([0,1],B)) with
αⁿ(ev_0)∘F=φ and αⁿ(ev_1)∘F=ψ, where ev_s evaluates a continuous interval path at s. NClasses
n A B is the quotient of HomN n A B by this equivalence relation.
-/
def NClasses (n : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :=
  Quotient (homotopicNSetoid n A B)

/-- **Class of a finite-stage representative.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star norm, and
define α⁰X=X, αⁿ⁺¹X=α(αⁿX). Write HomN n A B for nonunital complex star homomorphisms φ:A→αⁿB.
For φ,ψ∈HomN n A B, n-homotopy means that there is a star homomorphism F:A→αⁿ(C([0,1],B)) with
αⁿ(ev_0)∘F=φ and αⁿ(ev_1)∘F=ψ, where ev_s evaluates a continuous interval path at s. The map
classOf n sends φ to its n-homotopy class in NClasses n A B.
-/
def classOf (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : HomN n A B) : NClasses n A B :=
  Quotient.mk _ φ

/-!
## Successor transition by constant quotient classes

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star norm, and
define α⁰X=X, αⁿ⁺¹X=α(αⁿX). Write HomN n A B for nonunital complex star homomorphisms φ:A→αⁿB.
The stage inclusion i_n:αⁿB→αⁿ⁺¹B sends x to [t↦x] and acts on representatives by φ↦i_n∘φ.
-/

/-- **Representative included into the successor stage.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star norm, and
define α⁰X=X, αⁿ⁺¹X=α(αⁿX). Write HomN n A B for nonunital complex star homomorphisms φ:A→αⁿB.
For i_n=stageHom n B:x↦[t↦x], stageTransitionRepresentative n φ=i_n∘φ:A→αⁿ⁺¹B.
-/
def stageTransitionRepresentative (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : HomN n A B) : HomN (n + 1) A B :=
  (stageHom n B).comp φ

theorem stageTransitionRepresentative_apply (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : HomN n A B) (a : A) :
    stageTransitionRepresentative n φ a = stageHom n B (φ a) :=
  rfl

/-- **Successor inclusion preserves finite-stage homotopy.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star norm, and
define α⁰X=X, αⁿ⁺¹X=α(αⁿX). Write HomN n A B for nonunital complex star homomorphisms φ:A→αⁿB.
For φ,ψ∈HomN n A B, n-homotopy means that there is a star homomorphism F:A→αⁿ(C([0,1],B)) with
αⁿ(ev_0)∘F=φ and αⁿ(ev_1)∘F=ψ, where ev_s evaluates a continuous interval path at s. If φ is
n-homotopic to ψ, their successor representatives stageTransitionRepresentative n φ and
stageTransitionRepresentative n ψ are (n+1)-homotopic.
-/
theorem stageTransitionRepresentative_respects (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {φ ψ : HomN n A B} (h : HomotopicN n φ ψ) :
    HomotopicN (n + 1)
      (stageTransitionRepresentative n φ)
      (stageTransitionRepresentative n ψ) := by
  obtain ⟨H, h0, h1⟩ := h
  have hnat (t : unitInterval) :
      (AsymptoticAlgebra.endpointHom (n + 1) t B).comp
          (stageHom n C(unitInterval, B)) =
        (stageHom n B).comp (AsymptoticAlgebra.endpointHom n t B) := by
    simpa only [AsymptoticAlgebra.endpointHom_eq] using
      stageHom_naturality n (ContinuousMap.IntervalGluing.evalAt B t)
  refine ⟨(stageHom n C(unitInterval, B)).comp H, ?_, ?_⟩
  · unfold stageTransitionRepresentative
    rw [← NonUnitalStarAlgHom.comp_assoc, hnat,
      NonUnitalStarAlgHom.comp_assoc, h0]
  · unfold stageTransitionRepresentative
    rw [← NonUnitalStarAlgHom.comp_assoc, hnat,
      NonUnitalStarAlgHom.comp_assoc, h1]

/-- **Successor map on finite-stage homotopy classes.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star norm, and
define α⁰X=X, αⁿ⁺¹X=α(αⁿX). Write HomN n A B for nonunital complex star homomorphisms φ:A→αⁿB.
For φ,ψ∈HomN n A B, n-homotopy means that there is a star homomorphism F:A→αⁿ(C([0,1],B)) with
αⁿ(ev_0)∘F=φ and αⁿ(ev_1)∘F=ψ, where ev_s evaluates a continuous interval path at s. The map
stageTransition n A B:NClasses n A B→NClasses(n+1) A B sends [φ] to [stageHom n B∘φ].
-/
def stageTransition (n : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    NClasses n A B → NClasses (n + 1) A B :=
  Quotient.map (stageTransitionRepresentative n)
    (fun _ _ h ↦ stageTransitionRepresentative_respects n h)

@[simp]
theorem stageTransition_classOf (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : HomN n A B) :
    stageTransition n A B (classOf n φ) =
      classOf (n + 1) (stageTransitionRepresentative n φ) :=
  rfl

end IteratedAsymptoticAlgebra
