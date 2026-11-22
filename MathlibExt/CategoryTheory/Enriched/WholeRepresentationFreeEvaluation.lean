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

Both whole Hom functions use the actual original enriched free universal
property. Extension and identity evaluation retain their original maps.
The original genuine category and selected adjunction are compared through
the complete whole-Hom equivalence.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV uC

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.WholeRepresentation.FreeEvaluation

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  [BraidedCategory V] {C : Type uC} [EnrichedCategory V C]

omit [BraidedCategory V] in
/-- The whole free representation gives the actual original enriched free object. -/
theorem freeObject_genuine (n : C) (K : V) :
    genuineObject (freeObject n K) = EnrichedFunctorCat.Free.object n K := rfl

/-- Every whole coefficient map gives the actual original enriched free coefficient map. -/
theorem freeMap_genuine (n : C) {K L : V} (h : K ⟶ L) :
    genuineMap (freeMap n h) = EnrichedFunctorCat.Free.coefficientMap n h := by
  apply EnrichedFunctorCat.hom_ext
  intro k
  exact (genuineMap_component (freeMap n h) k).trans
    (EnrichedFunctorCat.Free.coefficientMap_component n h k).symm

/-- Extend a full coefficient map using the original entire action. -/
def extend (n : C) (K : V) (X : WholeRepresentation V C) (h : K ⟶ X.obj n) : freeObject n K ⟶ X where
  app k := h ▷ (n ⟶[V] k) ≫ X.action n k
  comm k l := by
    have hn := EnrichedFunctorCat.Free.extensionComponent_natural n K (genuineObject X) h k l
    rw [tensorHom_id] at hn
    change MonoidalClosed.uncurry (MonoidalClosed.curry (EnrichedFunctorCat.Free.action n K k l)) ≫
        ((h ⊗ₘ 𝟙 (n ⟶[V] l)) ≫ MonoidalClosed.uncurry (MonoidalClosed.curry (X.action n l))) =
      (((h ⊗ₘ 𝟙 (n ⟶[V] k)) ≫ MonoidalClosed.uncurry (MonoidalClosed.curry (X.action n k))) ▷
          (k ⟶[V] l)) ≫ MonoidalClosed.uncurry (MonoidalClosed.curry (X.action k l)) at hn
    change ((h ▷ (n ⟶[V] k) ≫ X.action n k) ▷ (k ⟶[V] l)) ≫ X.action k l =
      EnrichedFunctorCat.Free.action n K k l ≫ h ▷ (n ⟶[V] l) ≫ X.action n l
    simpa only [MonoidalClosed.uncurry_curry, tensorHom_id] using hn.symm

omit [BraidedCategory V] in
/-- Every extension component is the actual original coefficient action. -/
theorem extend_app (n k : C) (K : V) (X : WholeRepresentation V C) (h : K ⟶ X.obj n) :
    (extend n K X h).app k = h ▷ (n ⟶[V] k) ≫ X.action n k := rfl

/-- The whole extension map becomes the actual original genuine unit-graded extension. -/
theorem extend_genuine (n : C) (K : V) (X : WholeRepresentation V C) (h : K ⟶ X.obj n) :
    genuineMap (extend n K X h) = EnrichedFunctorCat.Free.extend n K (genuineObject X) h := by
  apply EnrichedFunctorCat.hom_ext
  intro k
  have hr : EnrichedFunctorCat.component (EnrichedFunctorCat.Free.extend n K (genuineObject X) h) k =
      h ▷ (n ⟶[V] k) ≫ X.action n k := by
    have hc := EnrichedFunctorCat.Free.extend_component n K (genuineObject X) h k
    have hh : EnrichedFunctorCat.Free.extensionComponent n K (genuineObject X) h k =
        h ▷ (n ⟶[V] k) ≫ X.action n k := by
      have hs : EnrichedFunctorCat.Free.extensionComponent n K (genuineObject X) h k =
          (h ⊗ₘ 𝟙 (n ⟶[V] k)) ≫ MonoidalClosed.uncurry (MonoidalClosed.curry (X.action n k)) := rfl
      have hu := MonoidalClosed.uncurry_curry (X.action n k)
      exact hs.trans ((congrArg (fun t => t ≫ MonoidalClosed.uncurry (MonoidalClosed.curry (X.action n k)))
          (tensorHom_id h (n ⟶[V] k))).trans (congrArg (fun t => h ▷ (n ⟶[V] k) ≫ t) hu))
    exact hc.trans hh
  exact (genuineMap_component _ k).trans hr.symm

/-- Evaluate the original whole map on the complete enriched identity coefficient. -/
def evaluate (n : C) (K : V) (X : WholeRepresentation V C) (f : freeObject n K ⟶ X) : K ⟶ X.obj n :=
  (ρ_ K).inv ≫ (K ◁ eId V n) ≫ f.app n

/-- Whole identity evaluation is the actual original enriched free identity evaluation. -/
theorem evaluate_genuine (n : C) (K : V) (X : WholeRepresentation V C) (f : freeObject n K ⟶ X) :
    EnrichedFunctorCat.Free.evaluate n K (genuineObject X) (genuineMap f) = evaluate n K X f := by
  change (ρ_ K).inv ≫ (K ◁ eId V n) ≫ EnrichedFunctorCat.component (genuineMap f) n =
    (ρ_ K).inv ≫ (K ◁ eId V n) ≫ f.app n
  exact congrArg (fun t => (ρ_ K).inv ≫ (K ◁ eId V n) ≫ t) (genuineMap_component f n)

/-- The original enriched free universal property recovers every supplied coefficient map. -/
theorem evaluate_extend (n : C) (K : V) (X : WholeRepresentation V C) (h : K ⟶ X.obj n) :
    evaluate n K X (extend n K X h) = h :=
  (evaluate_genuine n K X (extend n K X h)).symm.trans
    ((congrArg (EnrichedFunctorCat.Free.evaluate n K (genuineObject X)) (extend_genuine n K X h)).trans
      (EnrichedFunctorCat.Free.evaluate_extend n K (genuineObject X) h))

/-- The original enriched free universal property recovers the entire supplied whole morphism. -/
theorem extend_evaluate (n : C) (K : V) (X : WholeRepresentation V C) (f : freeObject n K ⟶ X) :
    extend n K X (evaluate n K X f) = f := by
  have hm := (extend_genuine n K X (evaluate n K X f)).trans
    ((congrArg (EnrichedFunctorCat.Free.extend n K (genuineObject X)) (evaluate_genuine n K X f)).symm.trans
      (EnrichedFunctorCat.Free.extend_evaluate n K (genuineObject X) (genuineMap f)))
  apply hom_ext
  intro k
  simpa only [genuineMap_component] using! congrArg (fun q => EnrichedFunctorCat.component q k) hm

/-- The full coefficient Hom correspondence uses original extension and identity evaluation. -/
def homEquiv (n : C) (K : V) (X : WholeRepresentation V C) :
    (freeObject n K ⟶ X) ≃ (K ⟶ X.obj n) where
  toFun := evaluate n K X
  invFun := extend n K X
  left_inv := extend_evaluate n K X
  right_inv := evaluate_extend n K X

omit [BraidedCategory V] in
/-- Whole extension retains every original coefficient precomposition square. -/
theorem extend_precomp (n : C) {K L : V} (X : WholeRepresentation V C)
    (f : K ⟶ L) (h : L ⟶ X.obj n) :
    extend n K X (f ≫ h) = (freeAt n).map f ≫ extend n L X h := by
  apply hom_ext
  intro k
  change ((f ≫ h) ▷ (n ⟶[V] k)) ≫ X.action n k =
    (f ▷ (n ⟶[V] k)) ≫ (h ▷ (n ⟶[V] k)) ≫ X.action n k
  rw [comp_whiskerRight, Category.assoc]

omit [MonoidalClosed V] [BraidedCategory V] in
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

/-- The actual whole free/evaluation adjunction is reconstructed from both original Hom functions. -/
def adjunction (n : C) : freeAt (V := V) n ⊣ evaluation (V := V) n :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv n
      homEquiv_naturality_left_symm := fun f h => extend_precomp n _ f h
      homEquiv_naturality_right := fun f g => evaluate_postcomp n _ f g }

/-- The selected adjunction retains the entire original Hom correspondence. -/
theorem adjunction_homEquiv (n : C) : (adjunction (V := V) n).homEquiv = homEquiv n :=
  Adjunction.mkOfHomEquiv_homEquiv _

end CategoryTheory.WholeRepresentation.FreeEvaluation
