/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.FunctorFullLawTransport

/-!
# Complete composition equations under actual Hom-object and field identities

Reindex a proved complete enriched composition function before any source
object is substituted. Transport its equation type only along actual whole
Hom-object, Hom-map and composition-field identities. The source and target
composition fields are functions; no coherence packet is constructed.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uV vV uA uJ uR

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Enriched

namespace EnrichedFunctorFullLawTransport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {A : Type uA} [EnrichedCategory V A] {R : Type uR}

/-- Apply an already proved full identity function to its original input. -/
theorem identity_condition_apply (o : Objects (A := A) (R := R)) (m : Maps (V := V) o)
    (h : IdentityCondition o m) (r : R) (X : A) :
    eId V X ≫ m r X X = eId V (o r X) :=
  congrArg (fun Φ => Φ r X) h

/-- Apply the complete two-Hom composition function after its proof. -/
theorem composition_condition_apply (o : Objects (A := A) (R := R)) (m : Maps (V := V) o)
    (h : CompositionCondition o m) (r : R) (X Y Z : A) :
    eComp V X Y Z ≫ m r X Z =
      (m r X Y ⊗ₘ m r Y Z) ≫ eComp V (o r X) (o r Y) (o r Z) :=
  congrArg (fun Φ => Φ r X Y Z) h

end EnrichedFunctorFullLawTransport

namespace EnrichedFunctorProofFieldTransport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {A : Type uA} [EnrichedCategory V A] {R : Type uR}

/-- The complete TYPE of existing enriched identity proof fields. -/
def IdentityFields (o : EnrichedFunctorFullLawTransport.Objects (A := A) (R := R))
    (m : EnrichedFunctorFullLawTransport.Maps (V := V) o) : Prop :=
  ∀ r X, eId V X ≫ m r X X = eId V (o r X)

/-- The entire TYPE of existing composition proof fields, with both Hom factors. -/
def CompositionFields (o : EnrichedFunctorFullLawTransport.Objects (A := A) (R := R))
    (m : EnrichedFunctorFullLawTransport.Maps (V := V) o) : Prop :=
  ∀ r X Y Z, eComp V X Y Z ≫ m r X Z =
    (m r X Y ⊗ₘ m r Y Z) ≫ eComp V (o r X) (o r Y) (o r Z)

/-- The actual complete identity proof fields of an existing enriched functor family. -/
theorem identity_fields_of_functors (F : R → EnrichedFunctor V A A) :
    IdentityFields (EnrichedFunctorFullLawTransport.functorObjects F)
      (EnrichedFunctorFullLawTransport.functorMaps F) :=
  fun r X => (F r).map_id X

/-- All actual composition proof fields of the same existing complete functor family. -/
theorem composition_fields_of_functors (F : R → EnrichedFunctor V A A) :
    CompositionFields (EnrichedFunctorFullLawTransport.functorObjects F)
      (EnrichedFunctorFullLawTransport.functorMaps F) :=
  fun r X Y Z => (F r).map_comp X Y Z

/-- Actual whole object/map identities identify the full identity proof-field TYPE. -/
theorem identity_fields_type_eq {o o' : EnrichedFunctorFullLawTransport.Objects
    (A := A) (R := R)}
    (m : EnrichedFunctorFullLawTransport.Maps (V := V) o)
    (m' : EnrichedFunctorFullLawTransport.Maps (V := V) o') (ho : o = o') (hm : HEq m m') :
    IdentityFields o m = IdentityFields o' m' := by
  cases ho
  cases eq_of_heq hm
  rfl

/-- Entire actual fields identify the full composition proof-function TYPE. -/
theorem composition_fields_type_eq {o o' : EnrichedFunctorFullLawTransport.Objects
    (A := A) (R := R)}
    (m : EnrichedFunctorFullLawTransport.Maps (V := V) o)
    (m' : EnrichedFunctorFullLawTransport.Maps (V := V) o') (ho : o = o') (hm : HEq m m') :
    CompositionFields o m = CompositionFields o' m' := by
  cases ho
  cases eq_of_heq hm
  rfl

end EnrichedFunctorProofFieldTransport

namespace FullShiftCompositionEquationTransport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {J : Type uJ} {R : Type uR}

/-- The entire source Hom-object function. -/
abbrev HomObjects := J → J → V

/-- Every shifted target Hom object, before any source input is supplied. -/
abbrev TargetHomObjects := R → J → J → V

/-- Complete Hom-map fields between those actual object functions. -/
abbrev Maps (H : HomObjects (V := V) (J := J))
    (K : TargetHomObjects (V := V) (J := J) (R := R)) :=
  ∀ r n k, H n k ⟶ K r n k

/-- The entire source composition field with both complete Hom factors. -/
abbrev Composition (H : HomObjects (V := V) (J := J)) :=
  ∀ n k l, H n k ⊗ H k l ⟶ H n l

/-- The complete target composition field on the actual shifted Hom objects. -/
abbrev TargetComposition (K : TargetHomObjects (V := V) (J := J) (R := R)) :=
  ∀ r n k l, K r n k ⊗ K r k l ⟶ K r n l

/-- Compose the whole source composition and Hom-map fields. -/
def sourceComposite {H : HomObjects (V := V) (J := J)}
    {K : TargetHomObjects (V := V) (J := J) (R := R)}
    (m : Maps H K) (c : Composition H) :=
  fun r n k l => c n k l ≫ m r n l

/-- Compose both whole Hom-map fields with the entire target composition. -/
def targetComposite {H : HomObjects (V := V) (J := J)}
    {K : TargetHomObjects (V := V) (J := J) (R := R)}
    (m : Maps H K) (c : TargetComposition K) :=
  fun r n k l => (m r n k ⊗ₘ m r k l) ≫ c r n k l

/-- Equality of these exact complete function composites. -/
def Condition {H : HomObjects (V := V) (J := J)}
    {K : TargetHomObjects (V := V) (J := J) (R := R)}
    (m : Maps H K) (c : Composition H) (d : TargetComposition K) : Prop :=
  sourceComposite m c = targetComposite m d

/-- Actual whole Hom-object and field identities identify the full equation type. -/
theorem condition_type_eq {H H' : HomObjects (V := V) (J := J)}
    {K K' : TargetHomObjects (V := V) (J := J) (R := R)}
    (m : Maps H K) (m' : Maps H' K') (c : Composition H) (c' : Composition H')
    (d : TargetComposition K) (d' : TargetComposition K')
    (hH : H = H') (hK : K = K') (hm : HEq m m') (hc : HEq c c') (hd : HEq d d') :
    Condition m c d = Condition m' c' d' := by
  cases hH
  cases hK
  cases eq_of_heq hm
  cases eq_of_heq hc
  cases eq_of_heq hd
  rfl

/-- Apply the already proved complete equation after its native field type is fixed. -/
theorem condition_apply {H : HomObjects (V := V) (J := J)}
    {K : TargetHomObjects (V := V) (J := J) (R := R)}
    (m : Maps H K) (c : Composition H) (d : TargetComposition K)
    (h : Condition m c d) (r : R) (n k l : J) :
    c n k l ≫ m r n l = (m r n k ⊗ₘ m r k l) ≫ d r n k l :=
  congrArg (fun Φ => Φ r n k l) h

/-- The entire dependent proof-function TYPE on the actual complete native fields. -/
def ProofFields {H : HomObjects (V := V) (J := J)}
    {K : TargetHomObjects (V := V) (J := J) (R := R)}
    (m : Maps H K) (c : Composition H) (d : TargetComposition K) : Prop :=
  ∀ r n k l, c n k l ≫ m r n l = (m r n k ⊗ₘ m r k l) ≫ d r n k l

/-- The complete function equation supplies all its dependent proof fields before inputs. -/
theorem proof_fields_of_condition {H : HomObjects (V := V) (J := J)}
    {K : TargetHomObjects (V := V) (J := J) (R := R)}
    (m : Maps H K) (c : Composition H) (d : TargetComposition K)
    (h : Condition m c d) : ProofFields m c d :=
  fun r n k l => congrFun (congrFun (congrFun (congrFun h r) n) k) l

variable {A : Type uA} [EnrichedCategory V A]

/-- The full actual source Hom-object fields on a chosen object function. -/
def sourceHomObjects (σ : J → A) : HomObjects (V := V) (J := J) :=
  fun n k => σ n ⟶[V] σ k

/-- The entire target Hom-object fields under the original shifted-object algorithm. -/
def targetHomObjects (σ : J → A) (o : EnrichedFunctorFullLawTransport.Objects
    (A := A) (R := R)) : TargetHomObjects (V := V) (J := J) (R := R) :=
  fun r n k => o r (σ n) ⟶[V] o r (σ k)

/-- Restrict all complete Hom-map fields at once. -/
def maps (σ : J → A) (o : EnrichedFunctorFullLawTransport.Objects (A := A) (R := R))
    (m : EnrichedFunctorFullLawTransport.Maps (V := V) o) :
    Maps (sourceHomObjects (V := V) σ) (targetHomObjects (V := V) σ o) :=
  fun r n k => m r (σ n) (σ k)

/-- The actual full enriched source composition field on that object function. -/
def sourceComposition (σ : J → A) : Composition (sourceHomObjects (V := V) σ) :=
  fun n k l => eComp V (σ n) (σ k) (σ l)

/-- All target composition fields under those same original object functions. -/
def targetComposition (σ : J → A) (o : EnrichedFunctorFullLawTransport.Objects
    (A := A) (R := R)) : TargetComposition (targetHomObjects (V := V) σ o) :=
  fun r n k l => eComp V (o r (σ n)) (o r (σ k)) (o r (σ l))

/-- Restrict the already proved complete composition equation before supplying any input. -/
theorem restricted_condition_proof (σ : J → A)
    (o : EnrichedFunctorFullLawTransport.Objects (A := A) (R := R))
    (m : EnrichedFunctorFullLawTransport.Maps (V := V) o)
    (h : EnrichedFunctorFullLawTransport.CompositionCondition o m) :
    Condition (maps σ o m) (sourceComposition σ) (targetComposition σ o) :=
  congrArg
    (fun (Φ : ∀ (r : R) (X Y Z : A),
        (X ⟶[V] Y) ⊗ (Y ⟶[V] Z) ⟶ (o r X ⟶[V] o r Z)) =>
      fun (r : R) (n k l : J) => Φ r (σ n) (σ k) (σ l)) h

end FullShiftCompositionEquationTransport
end CategoryTheory.Enriched
