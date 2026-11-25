/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.WholeRepresentationFreeEvaluation

/-!
# Comparison with the actual original enriched free/evaluation adjunction

The free and evaluation functors retain all original functions and maps.
Their comparison maps are genuine original identities. Both selected Hom
functions, unit and whole counit are preserved, and the actual adjunction
satisfies both full triangle equations.
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

/-- The whole free functor is the actual original genuine enriched free functor. -/
def genuineFreeIso (n : C) :
    freeAt (V := V) n ⋙ toGenuineFunctors ≅ EnrichedFunctorCat.Free.functor n :=
  NatIso.ofComponents (fun K => Iso.refl (EnrichedFunctorCat.Free.object n K)) (fun h => by
    change genuineMap (freeMap n h) ≫ 𝟙 _ = 𝟙 _ ≫ EnrichedFunctorCat.Free.coefficientMap n h
    exact (congrArg (fun f => f ≫ 𝟙 _) (freeMap_genuine n h)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- Whole evaluation is the actual original evaluation after the genuine category equivalence. -/
def genuineEvaluationIso (n : C) :
    toGenuineFunctors ⋙ EnrichedFunctorCat.evaluation n ≅ evaluation (V := V) n :=
  NatIso.ofComponents (fun X => Iso.refl (X.obj n)) (fun f => by
    change EnrichedFunctorCat.component (genuineMap f) n ≫ 𝟙 _ = 𝟙 _ ≫ f.app n
    exact (congrArg (fun h => h ≫ 𝟙 _) (genuineMap_component f n)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- The free comparison retains all original value-category identity components. -/
theorem genuineFreeIso_hom_component (n k : C) (K : V) :
    EnrichedFunctorCat.component ((genuineFreeIso n).hom.app K) k = 𝟙 (K ⊗ (n ⟶[V] k)) :=
  EnrichedFunctorCat.component_id _ _

/-- The inverse free comparison retains all original value-category identity components. -/
theorem genuineFreeIso_inv_component (n k : C) (K : V) :
    EnrichedFunctorCat.component ((genuineFreeIso n).inv.app K) k = 𝟙 (K ⊗ (n ⟶[V] k)) :=
  EnrichedFunctorCat.component_id _ _

/-- The evaluation comparison retains the original identity map on every evaluated object. -/
theorem genuineEvaluationIso_hom_app (n : C) (X : WholeRepresentation V C) :
    (genuineEvaluationIso n).hom.app X = 𝟙 (X.obj n) := rfl

/-- The inverse evaluation comparison retains the same original identity map. -/
theorem genuineEvaluationIso_inv_app (n : C) (X : WholeRepresentation V C) :
    (genuineEvaluationIso n).inv.app X = 𝟙 (X.obj n) := rfl

omit [MonoidalClosed V] [BraidedCategory V] in
/-- The actual selected unit is identity evaluation at the complete enriched identity
coefficient. -/
theorem adjunction_unit (n : C) (K : V) :
    (adjunction (V := V) n).unit.app K = (ρ_ K).inv ≫ (K ◁ eId V n) := by
  let p : K ⟶ K ⊗ (𝟙_ V) := (ρ_ K).inv
  let q : K ⊗ (𝟙_ V) ⟶ K ⊗ (n ⟶[V] n) := K ◁ eId V n
  change p ≫ q ≫ 𝟙 _ = p ≫ q
  exact congrArg (fun t => p ≫ t) (Category.comp_id q)

omit [MonoidalClosed V] [BraidedCategory V] in
/-- Every actual selected counit component is the complete original enriched Hom action. -/
theorem adjunction_counit_app (n k : C) (X : WholeRepresentation V C) :
    ((adjunction (V := V) n).counit.app X).app k = X.action n k := by
  change (𝟙 (X.obj n) ▷ (n ⟶[V] k)) ≫ X.action n k = X.action n k
  exact (congrArg (fun t => t ≫ X.action n k) (id_whiskerRight _ _)).trans (Category.id_comp _)

/-- The actual selected original enriched unit is the unchanged whole representation unit. -/
theorem genuine_unit (n : C) (K : V) :
    (EnrichedFunctorCat.Free.adjunction (V := V) n).unit.app K =
      (adjunction (V := V) n).unit.app K := by
  change EnrichedFunctorCat.Free.evaluate n K (EnrichedFunctorCat.Free.object n K)
      (𝟙 (EnrichedFunctorCat.Free.object n K)) = (adjunction (V := V) n).unit.app K
  have hi : EnrichedFunctorCat.component (𝟙 (EnrichedFunctorCat.Free.object n K)) n =
      𝟙 (K ⊗ (n ⟶[V] n)) := EnrichedFunctorCat.component_id _ _
  have hu := (congrArg (fun t => (ρ_ K).inv ≫ (K ◁ eId V n) ≫ t) hi).trans
    (congrArg (fun t => (ρ_ K).inv ≫ t) (Category.comp_id (K ◁ eId V n)))
  exact hu.trans (adjunction_unit n K).symm

/-- The whole selected counit becomes the actual original genuine unit-graded enriched counit. -/
theorem genuine_counit (n : C) (X : WholeRepresentation V C) :
    toGenuineFunctors.map ((adjunction (V := V) n).counit.app X) =
      (EnrichedFunctorCat.Free.adjunction (V := V) n).counit.app (genuineObject X) := by
  change genuineMap (extend n (X.obj n) X (𝟙 (X.obj n))) =
    EnrichedFunctorCat.Free.extend n (X.obj n) (genuineObject X) (𝟙 (X.obj n))
  exact extend_genuine n (X.obj n) X (𝟙 (X.obj n))

omit [MonoidalClosed V] [BraidedCategory V] in
/-- The first triangle is the actual selected whole free-functor triangle. -/
theorem free_triangle (n : C) (K : V) :
    (freeAt n).map ((adjunction (V := V) n).unit.app K) ≫
        (adjunction (V := V) n).counit.app ((freeAt n).obj K) = 𝟙 ((freeAt n).obj K) :=
  (adjunction n).left_triangle_components K

omit [MonoidalClosed V] [BraidedCategory V] in
/-- The second triangle is the actual selected whole evaluation triangle. -/
theorem evaluation_triangle (n : C) (X : WholeRepresentation V C) :
    (adjunction (V := V) n).unit.app ((evaluation n).obj X) ≫
        (evaluation n).map ((adjunction (V := V) n).counit.app X) = 𝟙 ((evaluation n).obj X) :=
  (adjunction n).right_triangle_components X

/-- Both actual selected adjunctions have the same complete forward Hom function. -/
theorem adjunction_hom_genuine (n : C) (K : V) (X : WholeRepresentation V C)
    (f : freeObject n K ⟶ X) :
    (adjunction (V := V) n).homEquiv K X f =
      (EnrichedFunctorCat.Free.adjunction (V := V) n).homEquiv K (genuineObject X)
        (genuineMap f) := by
  have hl := congrArg (fun q => q K X f) (adjunction_homEquiv (V := V) n)
  have hr := congrArg (fun q => q K (genuineObject X) (genuineMap f))
    (EnrichedFunctorCat.Free.adjunction_homEquiv (V := V) n)
  exact hl.trans ((evaluate_genuine n K X f).symm.trans hr.symm)

/-- Both actual selected adjunctions have the same complete inverse Hom function. -/
theorem adjunction_hom_inverse_genuine (n : C) (K : V) (X : WholeRepresentation V C)
    (h : K ⟶ X.obj n) :
    genuineMap (((adjunction (V := V) n).homEquiv K X).symm h) =
      ((EnrichedFunctorCat.Free.adjunction (V := V) n).homEquiv K (genuineObject X)).symm h := by
  have hl := congrArg (fun q => (q K X).symm h) (adjunction_homEquiv (V := V) n)
  have hr := congrArg (fun q => (q K (genuineObject X)).symm h)
    (EnrichedFunctorCat.Free.adjunction_homEquiv (V := V) n)
  exact (congrArg genuineMap hl).trans ((extend_genuine n K X h).trans hr.symm)

end CategoryTheory.WholeRepresentation.FreeEvaluation
