/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.WholeRepresentationGenuine
public import MathlibExt.CategoryTheory.Enriched.WholeRepresentationFreeObject

/-!
# The original enriched free/evaluation adjunction on whole representations

Extension uses the whole Hom action, and evaluation uses the enriched identity.
They are inverse by the action laws and whole naturality, over any monoidal base.
For a braided closed base, these maps agree with those of the unit-graded category.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV uC

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.WholeRepresentation.FreeEvaluation

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [EnrichedCategory V C]

/-- Extend a full coefficient map using the original entire action. -/
def extend (n : C) (K : V) (X : WholeRepresentation V C) (h : K ⟶ X.obj n) :
    freeObject n K ⟶ X where
  app k := h ▷ (n ⟶[V] k) ≫ X.action n k
  comm k l := by
    let P := n ⟶[V] k
    let Q := k ⟶[V] l
    let H := n ⟶[V] l
    change (((h ▷ P) ≫ X.action n k) ▷ Q) ≫ X.action k l =
      ((α_ K P Q).hom ≫ K ◁ eComp V n k l) ≫ (h ▷ H) ≫ X.action n l
    have hassoc : (X.action n k ▷ Q) ≫ X.action k l =
        (α_ (X.obj n) P Q).hom ≫ (X.obj n ◁ eComp V n k l) ≫ X.action n l := by
      rw [← X.assoc n k l, Iso.hom_inv_id_assoc]
    rw [Category.assoc, comp_whiskerRight, Category.assoc, hassoc,
      associator_naturality_left_assoc, whisker_exchange_assoc]

/-- Every extension component is the actual original coefficient action. -/
theorem extend_app (n k : C) (K : V) (X : WholeRepresentation V C) (h : K ⟶ X.obj n) :
    (extend n K X h).app k = h ▷ (n ⟶[V] k) ≫ X.action n k := rfl

/-- Evaluate the original whole map on the complete enriched identity coefficient. -/
def evaluate (n : C) (K : V) (X : WholeRepresentation V C) (f : freeObject n K ⟶ X) : K ⟶ X.obj n :=
  (ρ_ K).inv ≫ (K ◁ eId V n) ≫ f.app n

/-- The action unit law recovers the supplied coefficient map. -/
theorem evaluate_extend (n : C) (K : V) (X : WholeRepresentation V C) (h : K ⟶ X.obj n) :
    evaluate n K X (extend n K X h) = h := by
  change (ρ_ K).inv ≫ (K ◁ eId V n) ≫ (h ▷ (n ⟶[V] n)) ≫ X.action n n = h
  rw [whisker_exchange_assoc, X.unit n]
  exact (whiskerRight_id_symm h).symm

/-- Whole naturality at the enriched identity recovers the entire supplied morphism. -/
theorem extend_evaluate (n : C) (K : V) (X : WholeRepresentation V C) (f : freeObject n K ⟶ X) :
    extend n K X (evaluate n K X f) = f := by
  apply hom_ext
  intro k
  let H := n ⟶[V] k
  let E := n ⟶[V] n
  let pad : K ⊗ H ⟶ (K ⊗ E) ⊗ H := ((ρ_ K).inv ▷ H) ≫ ((K ◁ eId V n) ▷ H)
  have hPad : pad ≫ EnrichedFunctorCat.Free.action n K n k = 𝟙 (K ⊗ H) := by
    have hCanonical : pad ≫ (α_ K E H).hom =
        (K ◁ (λ_ H).inv) ≫ K ◁ (eId V n ▷ H) := by
      dsimp only [pad, E, H]
      monoidal
    rw [EnrichedFunctorCat.Free.action, ← Category.assoc, hCanonical]
    rw [← whiskerLeft_comp, ← whiskerLeft_comp]
    have hUnit := congrArg (fun q => K ◁ q) (e_id_comp V n k)
    simpa only [H, Category.assoc, whiskerLeft_id] using hUnit
  let fn : K ⊗ E ⟶ X.obj n := f.app n
  let fk : K ⊗ H ⟶ X.obj k := f.app k
  have hcomm : (fn ▷ H) ≫ X.action n k =
      EnrichedFunctorCat.Free.action n K n k ≫ fk := f.comm n k
  have h : pad ≫ (fn ▷ H) ≫ X.action n k = fk := by
    rw [hcomm, ← Category.assoc, hPad, Category.id_comp]
  change (((ρ_ K).inv ≫ (K ◁ eId V n) ≫ fn) ▷ H) ≫ X.action n k = fk
  simpa only [pad, comp_whiskerRight, Category.assoc] using h

/-- The full coefficient Hom correspondence uses original extension and identity evaluation. -/
def homEquiv (n : C) (K : V) (X : WholeRepresentation V C) :
    (freeObject n K ⟶ X) ≃ (K ⟶ X.obj n) where
  toFun := evaluate n K X
  invFun := extend n K X
  left_inv := extend_evaluate n K X
  right_inv := evaluate_extend n K X

/-- Whole extension retains every original coefficient precomposition square. -/
theorem extend_precomp (n : C) {K L : V} (X : WholeRepresentation V C)
    (f : K ⟶ L) (h : L ⟶ X.obj n) :
    extend n K X (f ≫ h) = (freeAt n).map f ≫ extend n L X h := by
  apply hom_ext
  intro k
  change ((f ≫ h) ▷ (n ⟶[V] k)) ≫ X.action n k =
    (f ▷ (n ⟶[V] k)) ≫ (h ▷ (n ⟶[V] k)) ≫ X.action n k
  rw [comp_whiskerRight, Category.assoc]

/-- Whole identity evaluation retains every original target transformation square. -/
theorem evaluate_postcomp (n : C) (K : V) {X Y : WholeRepresentation V C}
    (f : freeObject n K ⟶ X) (g : X ⟶ Y) :
    evaluate n K Y (f ≫ g) = evaluate n K X f ≫ (evaluation n).map g := by
  let p : K ⟶ K ⊗ (𝟙_ V) := (ρ_ K).inv
  let q : K ⊗ (𝟙_ V) ⟶ K ⊗ (n ⟶[V] n) := K ◁ eId V n
  let r : K ⊗ (n ⟶[V] n) ⟶ X.obj n := f.app n
  let t : X.obj n ⟶ Y.obj n := g.app n
  change p ≫ q ≫ (r ≫ t) = (p ≫ q ≫ r) ≫ t
  exact (Category.assoc p q (r ≫ t)).symm.trans
    ((Category.assoc (p ≫ q) r t).symm.trans (congrArg (fun z => z ≫ t) (Category.assoc p q r)))

/-- Reconstruct the whole free/evaluation adjunction from the original Hom functions. -/
def adjunction (n : C) : freeAt (V := V) n ⊣ evaluation (V := V) n :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv n
      homEquiv_naturality_left_symm := fun f h => extend_precomp n _ f h
      homEquiv_naturality_right := fun f g => evaluate_postcomp n _ f g }

/-- The selected adjunction retains the entire original Hom correspondence. -/
theorem adjunction_homEquiv (n : C) : (adjunction (V := V) n).homEquiv = homEquiv n :=
  Adjunction.mkOfHomEquiv_homEquiv _

section Genuine

variable [MonoidalClosed V]

/-- The whole free representation gives the actual original enriched free object. -/
theorem freeObject_genuine (n : C) (K : V) :
    genuineObject (freeObject n K) = EnrichedFunctorCat.Free.object n K := rfl

variable [BraidedCategory V]

/-- Every whole coefficient map gives the actual original enriched free coefficient map. -/
theorem freeMap_genuine (n : C) {K L : V} (h : K ⟶ L) :
    genuineMap (freeMap n h) = EnrichedFunctorCat.Free.coefficientMap n h := by
  apply EnrichedFunctorCat.hom_ext
  intro k
  exact (genuineMap_component (freeMap n h) k).trans
    (EnrichedFunctorCat.Free.coefficientMap_component n h k).symm

/-- The whole extension map becomes the actual original genuine unit-graded extension. -/
theorem extend_genuine (n : C) (K : V) (X : WholeRepresentation V C) (h : K ⟶ X.obj n) :
    genuineMap (extend n K X h) = EnrichedFunctorCat.Free.extend n K (genuineObject X) h := by
  apply EnrichedFunctorCat.hom_ext
  intro k
  have hr :
      EnrichedFunctorCat.component (EnrichedFunctorCat.Free.extend n K (genuineObject X) h) k =
        h ▷ (n ⟶[V] k) ≫ X.action n k := by
    have hc := EnrichedFunctorCat.Free.extend_component n K (genuineObject X) h k
    have hh : EnrichedFunctorCat.Free.extensionComponent n K (genuineObject X) h k =
        h ▷ (n ⟶[V] k) ≫ X.action n k := by
      have hs : EnrichedFunctorCat.Free.extensionComponent n K (genuineObject X) h k =
          (h ⊗ₘ 𝟙 (n ⟶[V] k)) ≫ MonoidalClosed.uncurry (MonoidalClosed.curry (X.action n k)) := rfl
      have hu := MonoidalClosed.uncurry_curry (X.action n k)
      exact hs.trans ((congrArg
        (fun t => t ≫ MonoidalClosed.uncurry (MonoidalClosed.curry (X.action n k)))
        (tensorHom_id h (n ⟶[V] k))).trans (congrArg (fun t => h ▷ (n ⟶[V] k) ≫ t) hu))
    exact hc.trans hh
  exact (genuineMap_component _ k).trans hr.symm

/-- Whole identity evaluation is the actual original enriched free identity evaluation. -/
theorem evaluate_genuine (n : C) (K : V) (X : WholeRepresentation V C) (f : freeObject n K ⟶ X) :
    EnrichedFunctorCat.Free.evaluate n K (genuineObject X) (genuineMap f) = evaluate n K X f := by
  change (ρ_ K).inv ≫ (K ◁ eId V n) ≫ EnrichedFunctorCat.component (genuineMap f) n =
    (ρ_ K).inv ≫ (K ◁ eId V n) ≫ f.app n
  exact congrArg (fun t => (ρ_ K).inv ≫ (K ◁ eId V n) ≫ t) (genuineMap_component f n)

end Genuine

end CategoryTheory.WholeRepresentation.FreeEvaluation
