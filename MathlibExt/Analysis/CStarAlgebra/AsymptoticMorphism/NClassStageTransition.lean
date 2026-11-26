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

/-!
# Finite-offset transitions on homotopy classes

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
Write i_(n,k):αⁿB→αⁿ⁺ᵏB for the composite of k constant-class inclusions, and
S_(n,k):Q_n(A,B)→Q_(n+k)(A,B) for [φ]↦[i_(n,k)∘φ]. These maps preserve n-homotopy, have
S_(n,0)=id and S_(n,1)=stageTransition n A B, and compose by addition of offsets with the
canonical reassociation of stage indices.
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
## Representative and class stage inclusions

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
Write i_(n,k):αⁿB→αⁿ⁺ᵏB for the composite of k constant-class inclusions, and
S_(n,k):Q_n(A,B)→Q_(n+k)(A,B) for [φ]↦[i_(n,k)∘φ].
-/

/-- **Representative included across a finite stage offset.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
Write i_(n,k):αⁿB→αⁿ⁺ᵏB for the composite of k constant-class inclusions, and
S_(n,k):Q_n(A,B)→Q_(n+k)(A,B) for [φ]↦[i_(n,k)∘φ]. The map stageTransitionRepresentativeFrom n
k sends φ to i_(n,k)∘φ:A→αⁿ⁺ᵏB.
-/
def stageTransitionRepresentativeFrom (n k : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : HomN n A B) : HomN (n + k) A B :=
  (stageMapFrom n k B).comp phi

@[simp]
theorem stageTransitionRepresentativeFrom_apply (n k : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : HomN n A B) (a : A) :
    stageTransitionRepresentativeFrom n k phi a =
      stageMapFrom n k B (phi a) :=
  rfl

/-- **Finite-offset transitions preserve homotopy.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
Write i_(n,k):αⁿB→αⁿ⁺ᵏB for the composite of k constant-class inclusions, and
S_(n,k):Q_n(A,B)→Q_(n+k)(A,B) for [φ]↦[i_(n,k)∘φ]. If φ and ψ are n-homotopic, then i_(n,k)∘φ
and i_(n,k)∘ψ are (n+k)-homotopic.
-/
theorem stageTransitionRepresentativeFrom_respects (n k : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {phi psi : HomN n A B} (h : HomotopicN n phi psi) :
    HomotopicN (n + k)
      (stageTransitionRepresentativeFrom n k phi)
      (stageTransitionRepresentativeFrom n k psi) := by
  obtain ⟨H, h0, h1⟩ := h
  have hnat (t : unitInterval) :
      (AsymptoticAlgebra.endpointHom (n + k) t B).comp
          (stageMapFrom n k C(unitInterval, B)) =
        (stageMapFrom n k B).comp
          (AsymptoticAlgebra.endpointHom n t B) := by
    simpa only [AsymptoticAlgebra.endpointHom_eq] using
      stageMapFrom_naturality n k
        (ContinuousMap.IntervalGluing.evalAt B t)
  refine ⟨(stageMapFrom n k C(unitInterval, B)).comp H, ?_, ?_⟩
  · unfold stageTransitionRepresentativeFrom
    rw [← NonUnitalStarAlgHom.comp_assoc, hnat,
      NonUnitalStarAlgHom.comp_assoc, h0]
  · unfold stageTransitionRepresentativeFrom
    rw [← NonUnitalStarAlgHom.comp_assoc, hnat,
      NonUnitalStarAlgHom.comp_assoc, h1]

/-- **Transition across a finite offset on class spaces.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
Write i_(n,k):αⁿB→αⁿ⁺ᵏB for the composite of k constant-class inclusions, and
S_(n,k):Q_n(A,B)→Q_(n+k)(A,B) for [φ]↦[i_(n,k)∘φ]. The map stageTransitionFrom n k A B is
S_(n,k).
-/
def stageTransitionFrom (n k : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    NClasses n A B → NClasses (n + k) A B :=
  Quotient.map (stageTransitionRepresentativeFrom n k)
    (fun _ _ h => stageTransitionRepresentativeFrom_respects n k h)

@[simp]
theorem stageTransitionFrom_classOf (n k : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : HomN n A B) :
    stageTransitionFrom n k A B (classOf n phi) =
      classOf (n + k) (stageTransitionRepresentativeFrom n k phi) :=
  rfl

/-!
## Identity and successor stage offsets

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
Write i_(n,k):αⁿB→αⁿ⁺ᵏB for the composite of k constant-class inclusions, and
S_(n,k):Q_n(A,B)→Q_(n+k)(A,B) for [φ]↦[i_(n,k)∘φ]. Offset zero is the identity; offset one is
the constant-class successor inclusion.
-/

private theorem stageTransitionRepresentativeFrom_zero (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : HomN n A B) :
    stageTransitionRepresentativeFrom n 0 phi = phi := by
  unfold stageTransitionRepresentativeFrom
  rw [stageMapFrom_zero]
  apply NonUnitalStarAlgHom.ext
  intro a
  rfl

/-- **Zero-offset class transition.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
Write i_(n,k):αⁿB→αⁿ⁺ᵏB for the composite of k constant-class inclusions, and
S_(n,k):Q_n(A,B)→Q_(n+k)(A,B) for [φ]↦[i_(n,k)∘φ]. The map stageTransitionFrom n 0 A B equals
id on Q_n(A,B).
-/
theorem stageTransitionFrom_zero (n : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    stageTransitionFrom n 0 A B = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro phi
  change stageTransitionFrom n 0 A B (classOf n phi) = classOf n phi
  rw [stageTransitionFrom_classOf, stageTransitionRepresentativeFrom_zero]
  rfl

private theorem stageTransitionRepresentativeFrom_one (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : HomN n A B) :
    stageTransitionRepresentativeFrom n 1 phi =
      stageTransitionRepresentative n phi := by
  unfold stageTransitionRepresentativeFrom stageTransitionRepresentative
  rw [stageMapFrom_one]

/-- **One-offset class transition.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
Write i_(n,k):αⁿB→αⁿ⁺ᵏB for the composite of k constant-class inclusions, and
S_(n,k):Q_n(A,B)→Q_(n+k)(A,B) for [φ]↦[i_(n,k)∘φ]. The map stageTransitionFrom n 1 A B equals
stageTransition n A B.
-/
theorem stageTransitionFrom_one (n : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    stageTransitionFrom n 1 A B = stageTransition n A B := by
  funext q
  refine Quotient.inductionOn q ?_
  intro phi
  change stageTransitionFrom n 1 A B (classOf n phi) =
    stageTransition n A B (classOf n phi)
  rw [stageTransitionFrom_classOf, stageTransition_classOf,
    stageTransitionRepresentativeFrom_one]

/-!
## Reassociation in offset composition

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
Write i_(n,k):αⁿB→αⁿ⁺ᵏB for the composite of k constant-class inclusions, and
S_(n,k):Q_n(A,B)→Q_(n+k)(A,B) for [φ]↦[i_(n,k)∘φ]. The target stages n+(k+l) and (n+k)+l are
identified by associativity of addition, so direct offset k+l agrees with successive offsets k
and l.
-/

/-- **Reassociated target of an offset class map.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
Write i_(n,k):αⁿB→αⁿ⁺ᵏB for the composite of k constant-class inclusions, and
S_(n,k):Q_n(A,B)→Q_(n+k)(A,B) for [φ]↦[i_(n,k)∘φ]. The map stageTransitionFromReassoc n k l A
B is S_(n,k+l) with its target identified as Q_((n+k)+l)(A,B).
-/
def stageTransitionFromReassoc (n k l : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    NClasses n A B → NClasses ((n + k) + l) A B :=
  Quotient.map (sa := homotopicNSetoid n A B)
    (sb := homotopicNSetoid ((n + k) + l) A B)
    (fun phi => (stageMapFromReassoc n k l B).comp phi)
    (fun _ _ h => by
      change HomotopicN ((n + k) + l) _ _
      have hk := stageTransitionRepresentativeFrom_respects n k h
      have hkl := stageTransitionRepresentativeFrom_respects (n + k) l hk
      simpa only [stageTransitionRepresentativeFrom,
        stageMapFrom_add, NonUnitalStarAlgHom.comp_assoc] using hkl)

@[simp]
theorem stageTransitionFromReassoc_classOf (n k l : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : HomN n A B) :
    stageTransitionFromReassoc n k l A B (classOf n phi) =
      classOf ((n + k) + l) ((stageMapFromReassoc n k l B).comp phi) :=
  rfl

/-- **Addition of offsets gives composition of class transitions.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
Write i_(n,k):αⁿB→αⁿ⁺ᵏB for the composite of k constant-class inclusions, and
S_(n,k):Q_n(A,B)→Q_(n+k)(A,B) for [φ]↦[i_(n,k)∘φ]. With the target Q_((n+k)+l)(A,B),
stageTransitionFromReassoc n k l A B=stageTransitionFrom(n+k) l A B∘stageTransitionFrom n k A
B.
-/
theorem stageTransitionFrom_add (n k l : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    stageTransitionFromReassoc n k l A B =
      Function.comp (stageTransitionFrom (n + k) l A B)
        (stageTransitionFrom n k A B) := by
  funext q
  refine Quotient.inductionOn q ?_
  intro phi
  change
    stageTransitionFromReassoc n k l A B (classOf n phi) =
      stageTransitionFrom (n + k) l A B
        (stageTransitionFrom n k A B (classOf n phi))
  rw [stageTransitionFromReassoc_classOf,
    stageTransitionFrom_classOf, stageTransitionFrom_classOf,
    stageMapFrom_add, NonUnitalStarAlgHom.comp_assoc]
  rfl


end IteratedAsymptoticAlgebra
