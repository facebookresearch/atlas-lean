/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.AlgebraicTopology.ModelCategory.ProperSpanGluing

/-!
# Tests for left-proper span gluing

These tests exercise both designated-leg orientations on arbitrary chosen
pushout squares, canonical pushouts, identity cubes, and the absence of
stronger unproved hypotheses or public helper machinery.
-/

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.ProperSpanGluing

variable {C : Type u} [Category.{v} C]

section ArbitraryChosenPushouts

variable [ModelCategory C] [IsLeftProper C]

variable {A B X P A' B' X' P' : C}
  {i : A ⟶ B} {g : A ⟶ X} {p : B ⟶ P} {q : X ⟶ P}
  {i' : A' ⟶ B'} {g' : A' ⟶ X'} {p' : B' ⟶ P'} {q' : X' ⟶ P'}
  (sq : IsPushout i g p q) (sq' : IsPushout i' g' p' q')
  {a : A ⟶ A'} {b : B ⟶ B'} {c : X ⟶ X'} {d : P ⟶ P'}
  (hi : i ≫ b = a ≫ i') (hg : g ≫ c = a ≫ g')
  (hp : p ≫ d = b ≫ p') (hq : q ≫ d = c ≫ q')

/-- The first-leg theorem consumes exactly the two first-leg cofibrations,
three vertical weak equivalences, and four cube equations. -/
example [Cofibration i] [Cofibration i']
    [WeakEquivalence a] [WeakEquivalence b] [WeakEquivalence c] :
    WeakEquivalence d :=
  IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
    sq sq' hi hg hp hq

/-- The second-leg theorem is the independent flipped client. -/
example [Cofibration g] [Cofibration g']
    [WeakEquivalence a] [WeakEquivalence b] [WeakEquivalence c] :
    WeakEquivalence d :=
  IsLeftProper.weakEquivalence_map_of_isPushouts_of_snd
    sq sq' hi hg hp hq

end ArbitraryChosenPushouts

section CanonicalPushouts

variable [ModelCategory C] [IsLeftProper C]

variable {P₀ Q₀ R₀ P₁ Q₁ R₁ : C}
  {u₀ : P₀ ⟶ Q₀} {v₀ : P₀ ⟶ R₀}
  {u₁ : P₁ ⟶ Q₁} {v₁ : P₁ ⟶ R₁}
  {wP : P₀ ⟶ P₁} {wQ : Q₀ ⟶ Q₁} {wR : R₀ ⟶ R₁}
  (hu : u₀ ≫ wQ = wP ≫ u₁) (hv : v₀ ≫ wR = wP ≫ v₁)

/-- Canonical `pushout.map`, first-leg orientation. -/
example [Cofibration u₀] [Cofibration u₁]
    [WeakEquivalence wP] [WeakEquivalence wQ] [WeakEquivalence wR] :
    WeakEquivalence
      (pushout.map u₀ v₀ u₁ v₁ wQ wR wP hu hv) :=
  IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
    (IsPushout.of_hasPushout u₀ v₀)
    (IsPushout.of_hasPushout u₁ v₁) hu hv
    (pushout.inl_desc _ _ _) (pushout.inr_desc _ _ _)

/-- Canonical `pushout.map`, second-leg orientation. -/
example [Cofibration v₀] [Cofibration v₁]
    [WeakEquivalence wP] [WeakEquivalence wQ] [WeakEquivalence wR] :
    WeakEquivalence
      (pushout.map u₀ v₀ u₁ v₁ wQ wR wP hu hv) :=
  IsLeftProper.weakEquivalence_map_of_isPushouts_of_snd
    (IsPushout.of_hasPushout u₀ v₀)
    (IsPushout.of_hasPushout u₁ v₁) hu hv
    (pushout.inl_desc _ _ _) (pushout.inr_desc _ _ _)

/-- An identity cube needs no object-cofibrancy assumption. -/
example {A B X : C} (i : A ⟶ B) (g : A ⟶ X) [Cofibration i] :
    WeakEquivalence (𝟙 (pushout i g)) := by
  apply IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
    (IsPushout.of_hasPushout i g) (IsPushout.of_hasPushout i g)
    (a := 𝟙 A) (b := 𝟙 B) (c := 𝟙 X)
  all_goals simp

/-- The flipped identity cube exercises the second designated leg. -/
example {A B X : C} (i : A ⟶ B) (g : A ⟶ X) [Cofibration g] :
    WeakEquivalence (𝟙 (pushout i g)) := by
  apply IsLeftProper.weakEquivalence_map_of_isPushouts_of_snd
    (IsPushout.of_hasPushout i g) (IsPushout.of_hasPushout i g)
    (a := 𝟙 A) (b := 𝟙 B) (c := 𝟙 X)
  all_goals simp

end CanonicalPushouts

section MissingProperness

variable [ModelCategory C]
  {A B X P A' B' X' P' : C}
  {i : A ⟶ B} {g : A ⟶ X} {p : B ⟶ P} {q : X ⟶ P}
  {i' : A' ⟶ B'} {g' : A' ⟶ X'} {p' : B' ⟶ P'} {q' : X' ⟶ P'}
  (sq : IsPushout i g p q) (sq' : IsPushout i' g' p' q')
  {a : A ⟶ A'} {b : B ⟶ B'} {c : X ⟶ X'} {d : P ⟶ P'}
  (hi : i ≫ b = a ≫ i') (hg : g ≫ c = a ≫ g')
  (hp : p ≫ d = b ≫ p') (hq : q ≫ d = c ≫ q')
  [Cofibration i] [Cofibration i']
  [WeakEquivalence a] [WeakEquivalence b] [WeakEquivalence c]

example : True := by
  fail_if_success
    have _ := IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
      sq sq' hi hg hp hq
  trivial

end MissingProperness

section MissingDesignatedCofibrations

variable [ModelCategory C] [IsLeftProper C]
  {A B X P A' B' X' P' : C}
  {i : A ⟶ B} {g : A ⟶ X} {p : B ⟶ P} {q : X ⟶ P}
  {i' : A' ⟶ B'} {g' : A' ⟶ X'} {p' : B' ⟶ P'} {q' : X' ⟶ P'}
  (sq : IsPushout i g p q) (sq' : IsPushout i' g' p' q')
  {a : A ⟶ A'} {b : B ⟶ B'} {c : X ⟶ X'} {d : P ⟶ P'}
  (hi : i ≫ b = a ≫ i') (hg : g ≫ c = a ≫ g')
  (hp : p ≫ d = b ≫ p') (hq : q ≫ d = c ≫ q')
  [WeakEquivalence a] [WeakEquivalence b] [WeakEquivalence c]

example [Cofibration i'] : True := by
  fail_if_success
    have _ := IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
      sq sq' hi hg hp hq
  trivial

example [Cofibration i] : True := by
  fail_if_success
    have _ := IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
      sq sq' hi hg hp hq
  trivial

example [Cofibration g'] : True := by
  fail_if_success
    have _ := IsLeftProper.weakEquivalence_map_of_isPushouts_of_snd
      sq sq' hi hg hp hq
  trivial

example [Cofibration g] : True := by
  fail_if_success
    have _ := IsLeftProper.weakEquivalence_map_of_isPushouts_of_snd
      sq sq' hi hg hp hq
  trivial

end MissingDesignatedCofibrations

section UniverseOneObjects

variable {C₁ : Type 1} [Category.{0} C₁]
  [ModelCategory C₁] [IsLeftProper C₁]

/-- Explicit object-universe-one, morphism-universe-zero client. -/
example {A B X : C₁} (i : A ⟶ B) (g : A ⟶ X) [Cofibration i] :
    WeakEquivalence (𝟙 (pushout i g)) := by
  apply IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
    (IsPushout.of_hasPushout i g) (IsPushout.of_hasPushout i g)
    (a := 𝟙 A) (b := 𝟙 B) (c := 𝟙 X)
  all_goals simp

end UniverseOneObjects

#check IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
#check IsLeftProper.weakEquivalence_map_of_isPushouts_of_snd

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.weakEquivalence_pushoutMap_of_fst

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.weakEquivalence_pushoutMap_of_snd

#guard_msgs (error, substring := true) in
#check IsRightProper.weakEquivalence_map_of_isPullbacks_of_fst

#print axioms IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
#print axioms IsLeftProper.weakEquivalence_map_of_isPushouts_of_snd

end MathlibExtTest.AlgebraicTopology.ModelCategory.ProperSpanGluing
