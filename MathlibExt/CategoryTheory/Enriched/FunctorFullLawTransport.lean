/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.CoendCharacteristicEquationTransport
public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# Full identity and composition equations under actual enriched-functor field identities

Existing enriched functors supply their complete identity and composition
functions. Proved whole object and Hom-map field identities transport the
actual equation types before any native object or Hom input is substituted.
No incoming identity or composition packet is assumed or constructed.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe uV vV uA uR

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Enriched
namespace EnrichedFunctorFullLawTransport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {A : Type uA} [EnrichedCategory V A] {R : Type uR}

/-- The complete original operator-object field family. -/
abbrev Objects := R → A → A

/-- The full enriched Hom-map field family on these exact original objects. -/
abbrev Maps (o : Objects (A := A) (R := R)) :=
  ∀ r : R, ∀ X Y : A, (X ⟶[V] Y) ⟶ (o r X ⟶[V] o r Y)

/-- The entire enriched identity equation on every original object. -/
def IdentityCondition (o : Objects (A := A) (R := R)) (m : Maps (V := V) o) : Prop :=
  (fun (r : R) (X : A) => eId V X ≫ m r X X) = fun r X => eId V (o r X)

/-- The complete enriched composition equation with both full source Hom factors retained. -/
def CompositionCondition (o : Objects (A := A) (R := R)) (m : Maps (V := V) o) : Prop :=
  (fun (r : R) (X Y Z : A) => eComp V X Y Z ≫ m r X Z) =
    fun r X Y Z => (m r X Y ⊗ₘ m r Y Z) ≫ eComp V (o r X) (o r Y) (o r Z)

/-- The actual whole object fields of an existing enriched-functor family. -/
def functorObjects (F : R → EnrichedFunctor V A A) : Objects (A := A) (R := R) :=
  fun r => (F r).obj

/-- All existing complete Hom-map fields before any source object is chosen. -/
def functorMaps (F : R → EnrichedFunctor V A A) : Maps (V := V) (functorObjects F) :=
  fun r => (F r).map

/-- Existing enriched functors prove the complete identity function equation. -/
theorem identity_condition_of_functors (F : R → EnrichedFunctor V A A) :
    IdentityCondition (functorObjects F) (functorMaps F) := by
  funext r X
  exact (F r).map_id X

/-- Existing enriched functors prove the entire full-Hom composition function equation. -/
theorem composition_condition_of_functors (F : R → EnrichedFunctor V A A) :
    CompositionCondition (functorObjects F) (functorMaps F) := by
  funext r X Y Z
  exact (F r).map_comp X Y Z

/-- Actual whole object identity identifies the entire enriched Hom-map type. -/
theorem maps_type_eq {o o' : Objects (A := A) (R := R)} (ho : o = o') :
    Maps (V := V) o = Maps (V := V) o' := by
  cases ho
  rfl

/-- The actual complete object and map fields identify the whole identity-equation type. -/
theorem identity_condition_type_eq {o o' : Objects (A := A) (R := R)}
    (m : Maps (V := V) o) (m' : Maps (V := V) o') (ho : o = o') (hm : HEq m m') :
    IdentityCondition o m = IdentityCondition o' m' := by
  cases ho
  cases eq_of_heq hm
  rfl

/-- The actual whole field identities preserve the entire composition-equation type. -/
theorem composition_condition_type_eq {o o' : Objects (A := A) (R := R)}
    (m : Maps (V := V) o) (m' : Maps (V := V) o') (ho : o = o') (hm : HEq m m') :
    CompositionCondition o m = CompositionCondition o' m' := by
  cases ho
  cases eq_of_heq hm
  rfl

end EnrichedFunctorFullLawTransport
end CategoryTheory.Enriched
