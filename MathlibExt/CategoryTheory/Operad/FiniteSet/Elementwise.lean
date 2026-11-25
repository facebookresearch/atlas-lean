/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Operad.FiniteSet.Basic

/-!
# Elementwise accessors for `SetOperad`

Derived accessors for the canonical `SetOperad` specialization.
These expose the empty tensor element, unary unit, substitution
data, total arity, full elementwise substitution, and associativity
routes by unfolding the `Type`-valued finite tensor as dependent
products. No new axioms are added beyond the existing `OperadObj`
structure.
-/

@[expose] public section

namespace CategoryTheory.Operad

universe u

namespace SetOperad

/-- The unique element of the empty tensor source for `Type`.

This is the dependent function over the empty finite family, given by
`fun e => e.elim` after unfolding. -/
def emptyTensorElement : operadUnitSource (V := Type u) :=
  fun e => e.elim

/-- The operadic unit element in `O(1)`, obtained by applying the
enriched unit morphism to the empty tensor element. -/
def unitElement (O : SetOperad.{u}) : O.toCollection.eval arityOne :=
  O.unit emptyTensorElement

/-- Substitution data for elementwise composition: outer arity `I`
and inner arities `J i`. -/
def substitutionData (I : FintypeCat) (J : I → FintypeCat) : SubstitutionData where
  index := I
  obj i := ⟨J i⟩

/-- Total arity of a substitution datum: the dependent sum `Σ i : I, J i`. -/
def totalArity (I : FintypeCat) (J : I → FintypeCat) : FintypeCat :=
  substitutionTotalObj (substitutionData I J)

/-- Full elementwise substitution: apply `O.subst` at `substitutionData I J`
to the `Option`-indexed family `none ↦ outer`, `some i ↦ inner i`.
Supports empty `I` and empty `J i` with no `Nonempty` assumptions. -/
def fullSubstitution (O : SetOperad.{u}) {I : FintypeCat} {J : I → FintypeCat}
    (outer : O.toCollection.eval I) (inner : (i : I) → O.toCollection.eval (J i)) :
    O.toCollection.eval (totalArity I J) :=
  (O.subst.app (substitutionData I J)) (fun o => match o with
    | none => outer
    | some i => inner i)

/-- Evaluation of the substitution-source map at an arbitrary factor. -/
theorem substitutionSource_map_apply (O : SymmetricCollection (Type u))
    {X Y : SubstitutionData} (f : X ⟶ Y)
    (fam : (substitutionSource O).obj X)
    (i : Option X.index) :
    ((substitutionSource O).map f fam)
        (((substitutionFactors O).map f).equiv i) =
      ((substitutionFactors O).map f).hom i (fam i) := by
  change
      FiniteFamily.typeTensorMap ((substitutionFactors O).map f) fam
          (((substitutionFactors O).map f).equiv i) =
        ((substitutionFactors O).map f).hom i (fam i)
  exact FiniteFamily.typeTensorMap_apply
    ((substitutionFactors O).map f) fam i

/-- Evaluation of the substitution-source map at the outer factor. -/
theorem substitutionSource_map_apply_none (O : SymmetricCollection (Type u))
    {X Y : SubstitutionData} (f : X ⟶ Y)
    (fam : (substitutionSource O).obj X) :
    ((substitutionSource O).map f fam) none =
      ((substitutionFactors O).map f).hom none (fam none) := by
  have h1 := substitutionSource_map_apply O f fam none
  have h2 :
      ((substitutionSource O).map f fam)
          (((substitutionFactors O).map f).equiv none) =
        ((substitutionSource O).map f fam) none :=
    rfl
  exact h2 ▸ h1

/-- Evaluation of the substitution-source map at an inner factor. -/
theorem substitutionSource_map_apply_some (O : SymmetricCollection (Type u))
    {X Y : SubstitutionData} (f : X ⟶ Y)
    (fam : (substitutionSource O).obj X) (i : X.index) :
    ((substitutionSource O).map f fam) (some (f.equiv i)) =
      ((substitutionFactors O).map f).hom (some i) (fam (some i)) := by
  have h1 := substitutionSource_map_apply O f fam (some i)
  have h2 :
      ((substitutionSource O).map f fam)
          (((substitutionFactors O).map f).equiv (some i)) =
        ((substitutionSource O).map f fam) (some (f.equiv i)) :=
    rfl
  exact h2 ▸ h1

/-- Elementwise form of naturality for operadic substitution. -/
theorem subst_naturality_apply (O : SetOperad.{u})
    {X Y : SubstitutionData} (f : X ⟶ Y)
    (fam : (substitutionSource O.toCollection).obj X) :
    O.subst.app Y ((substitutionSource O.toCollection).map f fam) =
      (substitutionTarget O.toCollection).map f (O.subst.app X fam) := by
  have h := O.subst.naturality f
  have h1 :
      ((substitutionSource O.toCollection).map f ≫ O.subst.app Y) fam =
        (O.subst.app X ≫ (substitutionTarget O.toCollection).map f) fam := by
    rw [h]
  exact h1

/-- The core enriched associativity equation exposed at the
elementwise layer: the two routes from the common source agree,
proved directly by `O.assoc`. -/
theorem associativity_routes (O : SetOperad.{u}) (d : AssocData) :
    associativityRouteA O.toCollection O.subst d =
      associativityRouteB O.toCollection O.subst d :=
  O.assoc d

end SetOperad

end CategoryTheory.Operad
