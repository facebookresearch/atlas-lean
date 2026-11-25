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
# Arbitrary finite-stage maps on literal homotopy classes

The direct iterated map `stageMapFrom n k` sends an actual representative at
stage `n` to one at stage `n + k`.  Naturality with the two endpoint maps
transports a literal interval homotopy, so this map descends to the explicit
quotient `NClasses`.

The offset-addition law uses a separately named reassociated map.  Thus its
target is visibly `(n + k) + l`; no definitional identification of that stage
with `n + (k + l)` and no replacement relation are hidden in the API.

This file defines only finite-stage data.  It does not construct a direct
limit, product, flattening map, or E-theory class.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

attribute [local instance] AsymptoticAlgebra.cStarAlgebra

namespace IteratedAsymptoticAlgebra

universe uA uB

/-! ## Representative and quotient maps -/

/-- Include one representative by an arbitrary finite stage offset. -/
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

/-- Every finite stage offset preserves the literal interval-homotopy
relation. -/
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

/-- The arbitrary finite-stage map on literal homotopy classes. -/
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

/-! ## Zero and one offsets -/

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

/-- Offset zero is the identity on literal homotopy classes. -/
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

/-- Offset one is the existing one-step constant-stage transition. -/
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

/-! ## Explicitly reassociated offset composition -/

/-- The direct `(k + l)`-offset map, with its class target transported to the
left-associated stage `(n + k) + l` by the already named representative map
`stageMapFromReassoc`. -/
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

/-- Offset addition is composition after making the target reassociation
explicit. -/
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
