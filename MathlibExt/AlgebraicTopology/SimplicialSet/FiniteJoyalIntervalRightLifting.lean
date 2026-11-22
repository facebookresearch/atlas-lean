/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalNaiveFibrations
public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryFactorization
public import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

/-!
# Right lifting tests for the finite-interval auxiliary class

For arbitrary simplicial maps, auxiliary naive fibrancy is equivalent to
inner fibrancy and boundary RLP for both actual endpoint function maps.
The endpoint function target is the pullback of endpoint evaluation and
the supplied base map. The same criterion uses all monomorphisms.

The actual corner pushout and endpoint pullback are supplied to the native
parametrized-adjunction square and lift equivalences. These retain every
prescribed square and both diagonal equations.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
  MonoidalCategory CartesianMonoidalCategory

universe u

namespace SSet.joyalInterval

variable {A B X Y : SSet.{u}}

/-- Evaluation at the specified interval endpoint, using the native unit
isomorphism for the internal Hom. -/
def endpointEvaluation (X : SSet.{u}) (ε : Fin 2) :
    (ihom joyalInterval).obj X ⟶ X :=
  (MonoidalClosed.pre (unitPoint ε)).app X ≫
    (MonoidalClosed.unitNatIso (C := SSet.{u})).inv.app X

@[reassoc]
lemma endpointEvaluation_naturality (p : X ⟶ Y) (ε : Fin 2) :
    endpointEvaluation X ε ≫ p = (ihom joyalInterval).map p ≫ endpointEvaluation Y ε := by
  dsimp [endpointEvaluation]
  have hunit := (MonoidalClosed.unitNatIso (C := SSet.{u})).inv.naturality p
  dsimp only [Functor.id_map] at hunit
  rw [Category.assoc, ← hunit,
    ← Category.assoc, ← (MonoidalClosed.pre (unitPoint ε)).naturality p, Category.assoc]

/-- The endpoint Leibniz function map into the actual pullback of
endpoint evaluation on the target and the given base map. -/
def endpointFunctionMap (p : X ⟶ Y) (ε : Fin 2) :
    (ihom joyalInterval).obj X ⟶ pullback (endpointEvaluation Y ε) p :=
  pullback.lift ((ihom joyalInterval).map p) (endpointEvaluation X ε)
    (endpointEvaluation_naturality p ε).symm

@[reassoc (attr := simp)]
lemma endpointFunctionMap_fst (p : X ⟶ Y) (ε : Fin 2) :
    endpointFunctionMap p ε ≫ pullback.fst (endpointEvaluation Y ε) p =
      (ihom joyalInterval).map p := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma endpointFunctionMap_snd (p : X ⟶ Y) (ε : Fin 2) :
    endpointFunctionMap p ε ≫ pullback.snd (endpointEvaluation Y ε) p =
      endpointEvaluation X ε := by
  exact pullback.lift_snd _ _ _

/-- The existing specified endpoint-corner pushout as native Leibniz data.
Its corner arrow is unchanged; the unit factor is transported by its unitor. -/
def endpointCornerPushoutObjObj (i : A ⟶ B) (ε : Fin 2) :
    (curriedTensor SSet).PushoutObjObj (unitPoint ε) i where
  pt := pushout i ((productPrecylinder.app A).endpoint ε)
  inl := pushout.inr i ((productPrecylinder.app A).endpoint ε)
  inr := (λ_ B).hom ≫ pushout.inl i ((productPrecylinder.app A).endpoint ε)
  isPushout := by
    refine (IsPushout.of_hasPushout i ((productPrecylinder.app A).endpoint ε)).flip.of_iso
      (λ_ A).symm (Iso.refl _) (λ_ B).symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simpa using productPrecylinder_endpoint_unitor A ε
    · simp
    · simp
    · simp
  ι := productPrecylinder.endpointCorner i ε
  inl_ι := by
    simp
  inr_ι := by
    rw [Category.assoc, Precylinder.inl_endpointCorner,
      productPrecylinder_endpoint_unitor B ε]
    simp

/-- The actual endpoint-function pullback as native Leibniz data.
The first projection uses the native internal-Hom unit isomorphism. -/
def endpointFunctionPullbackObjObj (p : X ⟶ Y) (ε : Fin 2) :
    MonoidalClosed.internalHom.PullbackObjObj (unitPoint ε) p where
  pt := pullback (endpointEvaluation Y ε) p
  fst := pullback.snd (endpointEvaluation Y ε) p ≫
    (MonoidalClosed.unitNatIso (C := SSet.{u})).hom.app X
  snd := pullback.fst (endpointEvaluation Y ε) p
  isPullback := by
    refine (IsPullback.of_hasPullback (endpointEvaluation Y ε) p).flip.of_iso
      (Iso.refl _) ((MonoidalClosed.unitNatIso (C := SSet.{u})).app X)
      (Iso.refl _) ((MonoidalClosed.unitNatIso (C := SSet.{u})).app Y) ?_ ?_ ?_ ?_
    · simp
    · simp
    · change p ≫ (MonoidalClosed.unitNatIso (C := SSet.{u})).hom.app Y =
        (MonoidalClosed.unitNatIso (C := SSet.{u})).hom.app X ≫ (ihom (𝟙_ SSet)).map p
      exact (MonoidalClosed.unitNatIso (C := SSet.{u})).hom.naturality p
    · simp [endpointEvaluation]
  π := endpointFunctionMap p ε
  π_fst := by
    rw [← Category.assoc, endpointFunctionMap_snd]
    simp [endpointEvaluation]
  π_snd := by
    exact endpointFunctionMap_fst p ε

/-- Endpoint-corner lifting and endpoint-function lifting are equivalent
for every left map, with the actual chosen pushout and pullback. -/
lemma endpointCorner_hasLiftingProperty_iff (i : A ⟶ B) (p : X ⟶ Y) (ε : Fin 2) :
    HasLiftingProperty (productPrecylinder.endpointCorner i ε) p ↔
      HasLiftingProperty i (endpointFunctionMap p ε) :=
  ParametrizedAdjunction.hasLiftingProperty_iff MonoidalClosed.internalHomAdjunction₂
    (endpointCornerPushoutObjObj i ε) (endpointFunctionPullbackObjObj p ε)

/-- The complete auxiliary naive-fibration criterion: raw inner lifting
and boundary lifting for both endpoint function maps, in all dimensions. -/
lemma auxiliaryNaiveFibrations_iff (p : X ⟶ Y) :
    auxiliaryNaiveFibrations p ↔ InnerFibration p ∧
      ∀ ε : Fin 2, modelCategoryQuillen.I.rlp (endpointFunctionMap p ε) := by
  rw [auxiliaryNaiveFibrations_eq_generatorRlp]
  constructor
  · intro hp
    constructor
    · rw [innerFibration_iff]
      exact fun _ _ i hi ↦ hp i (Or.inl hi)
    · intro ε A B i hi
      cases hi with
      | mk n =>
        exact (endpointCorner_hasLiftingProperty_iff _ p ε).mp
          (hp _ (auxiliaryGenerators.endpointCorner_mem n ε))
  · rintro ⟨hp, hε⟩ A B i hi
    change innerHornInclusions i ∨ MorphismProperty.ofHoms _ i at hi
    rcases hi with hi | hi
    · exact hp.mem i hi
    · cases hi with
      | mk k =>
        exact (endpointCorner_hasLiftingProperty_iff _ p k.2).mpr
          (hε k.2 _ (modelCategoryQuillen.boundary_ι_mem_I k.1))

/-- Equivalently, each actual endpoint function map lifts against every
monomorphism. No fibrancy assumption on source or base is required. -/
lemma auxiliaryNaiveFibrations_iff_monomorphisms (p : X ⟶ Y) :
    auxiliaryNaiveFibrations p ↔ InnerFibration p ∧
      ∀ ε : Fin 2,
        (MorphismProperty.monomorphisms SSet).rlp (endpointFunctionMap p ε) := by
  rw [auxiliaryNaiveFibrations_iff]
  simp only [rlp_monomorphisms]

end SSet.joyalInterval
