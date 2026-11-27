/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.ProductRelationMapping
public import MathlibExt.CategoryTheory.Enriched.RightActionMapping
public import MathlibExt.CategoryTheory.Enriched.NaturalTransformation

@[expose] public section
set_option autoImplicit false
set_option linter.hashCommand false
noncomputable section
universe uV vV uI uA

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.EnrichedRightActionMapping

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I] {A : Type uA}

/-- Actual genuine enriched diagrams and complete right coefficient actions.
The source has no selected ordinary category; all original Hom parameters are retained. -/
structure Data where
  /-- The source enriched diagram. -/
  X : EnrichedFunctor V I V
  /-- The target enriched diagram. -/
  Y : EnrichedFunctor V I V
  /-- The coefficient object for each action index. -/
  coefficient : A → V
  /-- The diagram index reached by a right coefficient action. -/
  rightIndex : I → A → I
  /-- The right coefficient action on the source diagram. -/
  rightX : ∀ n a, X.obj n ⊗ coefficient a ⟶ X.obj (rightIndex n a)
  /-- The right coefficient action on the target diagram. -/
  rightY : ∀ n a, Y.obj n ⊗ coefficient a ⟶ Y.obj (rightIndex n a)

/-- Indices for the enriched naturality and right action relations. -/
abbrev Relation : Type (max uI uA) := Sum (I × I) (I × A)

/-- Every complete original component internal Hom. -/
abbrev objects (d : Data (V := V) (I := I) (A := A)) (n : I) : V :=
  (ihom (d.X.obj n)).obj (d.Y.obj n)

/-- The first relation contains the FULL original H(n,k), and the second the full coefficient. -/
def relations (d : Data (V := V) (I := I) (A := A)) : Relation (I := I) (A := A) → V
  | .inl (n, k) => (ihom (d.X.obj n ⊗ (n ⟶[V] k))).obj (d.Y.obj k)
  | .inr (n, a) => (ihom (d.X.obj n ⊗ d.coefficient a)).obj (d.Y.obj (d.rightIndex n a))

/-- Both full original naturality relation families are the actual component maps. -/
def system (d : Data (V := V) (I := I) (A := A)) :
    ProductRelationMapping.Data (V := V) (I := I) (R := Relation (I := I) (A := A)) where
  objects := objects d
  relations := relations d
  leftIndex
    | .inl (n, _) => n
    | .inr (n, a) => d.rightIndex n a
  rightIndex
    | .inl (_, k) => k
    | .inr (n, _) => n
  leftComponent
    | .inl (n, k) =>
      (SphereOperator.fixedRightTensor
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (n ⟶[V] k)).map
        (d.X.obj n) (d.Y.obj n) ≫
        eHomWhiskerLeft V (d.X.obj n ⊗ (n ⟶[V] k)) (MonoidalClosed.uncurry (d.Y.map n k))
    | .inr (n, a) => eHomWhiskerRight V (d.rightX n a) (d.Y.obj (d.rightIndex n a))
  rightComponent
    | .inl (n, k) => eHomWhiskerRight V (MonoidalClosed.uncurry (d.X.map n k)) (d.Y.obj k)
    | .inr (n, a) =>
      (SphereOperator.fixedRightTensor
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (d.coefficient a)).map
        (d.X.obj n) (d.Y.obj n) ≫
        eHomWhiskerLeft V (d.X.obj n ⊗ d.coefficient a) (d.rightY n a)

/-- Every complete parameter family has full enriched Hom and right action naturality. -/
abbrev Family (d : Data (V := V) (I := I) (A := A)) (P : V) :=
  ProductRelationMapping.Family (system d) P

/-- The original actual unit-graded component. -/
abbrev component (d : Data (V := V) (I := I) (A := A))
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) d.X d.Y) (n : I) :
    d.X.obj n ⟶ d.Y.obj n :=
  (eHomEquiv V (X := d.X.obj n) (Y := d.Y.obj n)).symm (t.app n)

/-- Genuine unit-graded transformations preserving every complete original right action. -/
abbrev CompatibleHom (d : Data (V := V) (I := I) (A := A)) :=
  { t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) d.X d.Y //
    ∀ n a, d.rightX n a ≫ component d t (d.rightIndex n a) =
      (component d t n ▷ d.coefficient a) ≫ d.rightY n a }

/-- Actual full unit-graded morphisms give every original complete unit family. -/
def compatibleToFamily (d : Data (V := V) (I := I) (A := A)) (f : CompatibleHom d) :
    Family d (𝟙_ V) where
  app n := eHomEquiv V (component d f.val n)
  condition r := by
    cases r with
    | inl r =>
      let H : V := r.1 ⟶[V] r.2
      let q := component d f.val r.1
      let q' := component d f.val r.2
      let x := MonoidalClosed.uncurry (d.X.map r.1 r.2)
      let y := MonoidalClosed.uncurry (d.Y.map r.1 r.2)
      have h : x ≫ q' = (q ▷ H) ≫ y := by
        simpa only [tensorHom_id] using f.val.uncurriedNaturality r.1 r.2
      have hTensor := congrArg
        (fun z => z ≫ eHomWhiskerLeft V (d.X.obj r.1 ⊗ H) y)
        (SphereOperator.fixedRightTensor_point (MonoidalClosed.enrichedMonoidalCategoryDataSelf V)
          H q)
      change eHomEquiv V q ≫
          (SphereOperator.fixedRightTensor
            (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) H).map
            (d.X.obj r.1) (d.Y.obj r.1) ≫
          eHomWhiskerLeft V (d.X.obj r.1 ⊗ H) y =
        eHomEquiv V q' ≫ eHomWhiskerRight V x (d.Y.obj r.2)
      exact (Category.assoc _ _ _).symm.trans
        (hTensor.trans
          ((eHomEquiv_comp_eHomWhiskerLeft V V (q ▷ H) y).trans
            ((congrArg (eHomEquiv V) h.symm).trans
              (eHomEquiv_comp_eHomWhiskerRight V V x q').symm)))
    | inr r =>
      let q := component d f.val r.1
      let q' := component d f.val (d.rightIndex r.1 r.2)
      have hTensor := congrArg
        (fun z => z ≫ eHomWhiskerLeft V (d.X.obj r.1 ⊗ d.coefficient r.2) (d.rightY r.1 r.2))
        (SphereOperator.fixedRightTensor_point (MonoidalClosed.enrichedMonoidalCategoryDataSelf V)
          (d.coefficient r.2) q)
      change eHomEquiv V q' ≫ eHomWhiskerRight V (d.rightX r.1 r.2)
          (d.Y.obj (d.rightIndex r.1 r.2)) =
        eHomEquiv V q ≫
          (SphereOperator.fixedRightTensor
            (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (d.coefficient r.2)).map
            (d.X.obj r.1) (d.Y.obj r.1) ≫
          eHomWhiskerLeft V (d.X.obj r.1 ⊗ d.coefficient r.2) (d.rightY r.1 r.2)
      exact (eHomEquiv_comp_eHomWhiskerRight V V (d.rightX r.1 r.2) q').trans
        ((congrArg (eHomEquiv V) (f.property r.1 r.2)).trans
          ((eHomEquiv_comp_eHomWhiskerLeft V V
            (q ▷ d.coefficient r.2) (d.rightY r.1 r.2)).symm.trans
            (hTensor.symm.trans (Category.assoc _ _ _))))

/-- Every original unit-family point determines the unchanged ordinary component map. -/
abbrev familyComponent (d : Data (V := V) (I := I) (A := A))
    (q : Family d (𝟙_ V)) (n : I) : d.X.obj n ⟶ d.Y.obj n :=
  (eHomEquiv V (X := d.X.obj n) (Y := d.Y.obj n)).symm (q.app n)

/-- Full component points retain the actual family morphisms. -/
theorem familyComponent_point (d : Data (V := V) (I := I) (A := A))
    (q : Family d (𝟙_ V)) (n : I) :
    eHomEquiv V (familyComponent d q n) = q.app n :=
  (eHomEquiv V (X := d.X.obj n) (Y := d.Y.obj n)).apply_symm_apply (q.app n)

private theorem familyFullNaturality (d : Data (V := V) (I := I) (A := A))
    (q : Family d (𝟙_ V)) (n k : I) :
    MonoidalClosed.uncurry (d.X.map n k) ≫ familyComponent d q k =
      (familyComponent d q n ⊗ₘ 𝟙 (n ⟶[V] k)) ≫
        MonoidalClosed.uncurry (d.Y.map n k) := by
  apply (eHomEquiv V).injective
  rw [tensorHom_id, ← eHomEquiv_comp_eHomWhiskerRight V V, ← eHomEquiv_comp_eHomWhiskerLeft V V,
    ← SphereOperator.fixedRightTensor_point (MonoidalClosed.enrichedMonoidalCategoryDataSelf V)]
  rw [familyComponent_point, familyComponent_point]
  have h := q.condition (.inl (n, k))
  change q.app n ≫ (SphereOperator.fixedRightTensor
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (n ⟶[V] k)).map
    (d.X.obj n) (d.Y.obj n) ≫
      eHomWhiskerLeft V (d.X.obj n ⊗ (n ⟶[V] k)) (MonoidalClosed.uncurry (d.Y.map n k)) =
    q.app k ≫ eHomWhiskerRight V (MonoidalClosed.uncurry (d.X.map n k)) (d.Y.obj k) at h
  exact h.symm.trans (Category.assoc _ _ _).symm

/-- Full original H(n,k) naturality reconstructs a genuine entire unit-graded transformation. -/
@[no_expose]
def familyTransformation (d : Data (V := V) (I := I) (A := A))
    (q : Family d (𝟙_ V)) : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) d.X d.Y :=
  GradedNatTrans.unitOfComponents (familyComponent d q) (familyFullNaturality d q)

/-- Each complete component of the reconstructed genuine transformation is unchanged. -/
theorem familyTransformation_component (d : Data (V := V) (I := I) (A := A))
    (q : Family d (𝟙_ V)) (n : I) : component d (familyTransformation d q) n =
      familyComponent d q n :=
  GradedNatTrans.unitOfComponents_component (familyComponent d q) (familyFullNaturality d q) n

/-- Every whole original right coefficient relation holds on the genuine transformation. -/
def familyToCompatible (d : Data (V := V) (I := I) (A := A))
    (q : Family d (𝟙_ V)) : CompatibleHom d := by
  refine ⟨familyTransformation d q, ?_⟩
  intro n a
  rw [familyTransformation_component, familyTransformation_component]
  apply (eHomEquiv V).injective
  rw [← eHomEquiv_comp_eHomWhiskerRight V V, ← eHomEquiv_comp_eHomWhiskerLeft V V,
    ← SphereOperator.fixedRightTensor_point (MonoidalClosed.enrichedMonoidalCategoryDataSelf V)]
  rw [familyComponent_point, familyComponent_point]
  have h := q.condition (.inr (n, a))
  change q.app (d.rightIndex n a) ≫ eHomWhiskerRight V (d.rightX n a)
      (d.Y.obj (d.rightIndex n a)) = q.app n ≫
    (SphereOperator.fixedRightTensor
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (d.coefficient a)).map
      (d.X.obj n) (d.Y.obj n) ≫
      eHomWhiskerLeft V (d.X.obj n ⊗ d.coefficient a) (d.rightY n a) at h
  exact h.trans (Category.assoc _ _ _).symm

/-- Every original component survives the full coefficient-compatible reconstruction. -/
theorem familyToCompatible_component (d : Data (V := V) (I := I) (A := A))
    (q : Family d (𝟙_ V)) (n : I) : component d (familyToCompatible d q).val n =
      familyComponent d q n := familyTransformation_component d q n

/-- Every entire original genuine transformation is recovered. -/
theorem family_compatible_inverse (d : Data (V := V) (I := I) (A := A)) (f : CompatibleHom d) :
    familyToCompatible d (compatibleToFamily d f) = f := by
  apply Subtype.ext
  apply GradedNatTrans.ext
  funext n
  apply (eHomEquiv V).symm.injective
  change component d (familyToCompatible d (compatibleToFamily d f)).val n = component d f.val n
  exact (familyToCompatible_component d (compatibleToFamily d f) n).trans
    ((eHomEquiv V).symm_apply_apply (component d f.val n))

/-- Every full original enriched unit-family component is recovered. -/
theorem compatible_family_inverse (d : Data (V := V) (I := I) (A := A))
    (q : Family d (𝟙_ V)) : compatibleToFamily d (familyToCompatible d q) = q := by
  apply ProductRelationMapping.Family.ext
  funext n
  change eHomEquiv V (component d (familyToCompatible d q).val n) = q.app n
  exact (congrArg (eHomEquiv V) (familyToCompatible_component d q n)).trans
    (familyComponent_point d q n)

/-- The genuine whole unit-graded morphism/family correspondence has both complete inverses. -/
def compatibleFamilyEquiv (d : Data (V := V) (I := I) (A := A)) :
    CompatibleHom d ≃ Family d (𝟙_ V) where
  toFun := compatibleToFamily d
  invFun := familyToCompatible d
  left_inv := family_compatible_inverse d
  right_inv := compatible_family_inverse d

variable (d : Data (V := V) (I := I) (A := A))
  [HasProduct (system d).objects] [HasProduct (system d).relations]
  [HasEqualizer (ProductRelationMapping.leftMap (system d))
    (ProductRelationMapping.rightMap (system d))]

/-- Actual enriched-source right mapping object with all complete original relation parameters. -/
@[no_expose]
def Hom : V := ProductRelationMapping.Hom (system d)

/-- Every full original parameter family is represented without an ordinary source category. -/
@[no_expose]
def parameterEquiv (P : V) : (P ⟶ Hom d) ≃ Family d P :=
  ProductRelationMapping.representationEquiv (system d) P

/-- Actual compatible genuine unit-graded morphisms are exactly maps from the pointed unit. -/
@[no_expose]
def unitHomEquiv : CompatibleHom d ≃ (𝟙_ V ⟶ Hom d) :=
  (compatibleFamilyEquiv d).trans
    (ProductRelationMapping.representationEquiv (system d) (𝟙_ V)).symm

/-- All complete native/generic mapping-space projections retain their original component. -/
@[no_expose]
def π (n : I) : Hom d ⟶ objects d n := ProductRelationMapping.π (system d) n

/-- Every entire parameter family component is unchanged. -/
theorem parameterEquiv_app (P : V) (f : P ⟶ Hom d) (n : I) :
    (parameterEquiv d P f).app n = f ≫ π d n := by rfl

/-- Every full component of a represented genuine transformation is unchanged. -/
theorem unitHomEquiv_π (f : CompatibleHom d) (n : I) :
    unitHomEquiv d f ≫ π d n = eHomEquiv V (component d f.val n) :=
  ProductRelationMapping.lift_π (system d) (compatibleToFamily d f) n

/-- The actual full mapping object is the complete original product relation equalizer. -/
theorem Hom_eq : Hom d =
    equalizer (ProductRelationMapping.leftMap (system d))
      (ProductRelationMapping.rightMap (system d)) :=
  ProductRelationMapping.Hom_eq (system d)

end CategoryTheory.Enriched.EnrichedRightActionMapping
