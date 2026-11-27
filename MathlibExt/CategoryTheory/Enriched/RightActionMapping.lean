/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.Basic
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorHom
public import MathlibExt.CategoryTheory.Enriched.ProductRelationMapping
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

import Mathlib.Tactic.DSimpPercent

@[expose] public section
set_option autoImplicit false
set_option linter.hashCommand false
noncomputable section
universe uV vV uI vI

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.RightActionMapping

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]

/-- Raw actual diagrams and complete coefficient-right action maps.
No mapping-object value or inverse law is an input. -/
structure Data where
  /-- The source diagram. -/
  X : I ⥤ V
  /-- The target diagram. -/
  Y : I ⥤ V
  /-- The coefficient object at each index. -/
  coefficient : I → V
  /-- The right coefficient action on the source diagram. -/
  rightX : ∀ n a, X.obj n ⊗ coefficient a ⟶ X.obj (n ⊗ a)
  /-- The right coefficient action on the target diagram. -/
  rightY : ∀ n a, Y.obj n ⊗ coefficient a ⟶ Y.obj (n ⊗ a)

/-- Mapping families retain every original degree. -/
abbrev objects (d : Data (V := V) (I := I)) (n : I) : V :=
  (ihom (d.X.obj n)).obj (d.Y.obj n)

/-- Both ordinary index naturality and the entire coefficient-action squares are retained. -/
abbrev Relation : Type (max uI vI) := Sum (Arrow I) (I × I)

/-- All relation targets retain their full actual internal Hom. -/
def relations (d : Data (V := V) (I := I)) : Relation (I := I) → V
  | .inl f => (ihom (d.X.obj f.left)).obj (d.Y.obj f.right)
  | .inr (n, a) => (ihom (d.X.obj n ⊗ d.coefficient a)).obj (d.Y.obj (n ⊗ a))

/-- The original ordinary index and right-action squares as full product relation data. -/
abbrev system (d : Data (V := V) (I := I)) :
    ProductRelationMapping.Data (V := V) (I := I) (R := Relation (I := I)) where
  objects := objects d
  relations := relations d
  leftIndex
    | .inl f => f.left
    | .inr (n, a) => n ⊗ a
  rightIndex
    | .inl f => f.right
    | .inr (n, _) => n
  leftComponent
    | .inl f => eHomWhiskerLeft V (d.X.obj f.left) (d.Y.map f.hom)
    | .inr (n, a) => eHomWhiskerRight V (d.rightX n a) (d.Y.obj (n ⊗ a))
  rightComponent
    | .inl f => eHomWhiskerRight V (d.X.map f.hom) (d.Y.obj f.right)
    | .inr (n, a) =>
      (SphereOperator.fixedRightTensor
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (d.coefficient a)).map
        (d.X.obj n) (d.Y.obj n) ≫
      eHomWhiskerLeft V (d.X.obj n ⊗ d.coefficient a) (d.rightY n a)

/-- The entire first relation family uses index postcomposition and source-action precomposition. -/
def familyLeft (d : Data (V := V) (I := I)) {P : V}
    (q : ∀ n, P ⟶ objects d n) : ∀ r, P ⟶ relations d r :=
  dsimp% only [system] (fun r => q ((system d).leftIndex r) ≫ (system d).leftComponent r)

/-- The entire second relation family uses index precomposition and target right action. -/
def familyRight (d : Data (V := V) (I := I)) {P : V}
    (q : ∀ n, P ⟶ objects d n) : ∀ r, P ⟶ relations d r :=
  fun r => q ((system d).rightIndex r) ≫ (system d).rightComponent r

omit [BraidedCategory V] in
/-- Every complete first relation is the original index or source-action square. -/
theorem familyLeft_eq (d : Data (V := V) (I := I)) {P : V}
    (q : ∀ n, P ⟶ objects d n) : familyLeft d q =
    (fun r => match r with
      | .inl f => q f.left ≫ eHomWhiskerLeft V (d.X.obj f.left) (d.Y.map f.hom)
      | .inr (n, a) =>
        q (n ⊗ a) ≫ eHomWhiskerRight V (d.rightX n a) (d.Y.obj (n ⊗ a))) := by
  funext r
  cases r with
  | inl f => rfl
  | inr r =>
    rcases r with ⟨n, a⟩
    rfl

/-- Every complete second relation is the original index or target-action square. -/
theorem familyRight_eq (d : Data (V := V) (I := I)) {P : V}
    (q : ∀ n, P ⟶ objects d n) : familyRight d q =
    (fun r => match r with
      | .inl f => q f.right ≫ eHomWhiskerRight V (d.X.map f.hom) (d.Y.obj f.right)
      | .inr (n, a) => q n ≫
        (SphereOperator.fixedRightTensor
          (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (d.coefficient a)).map
          (d.X.obj n) (d.Y.obj n) ≫
        eHomWhiskerLeft V (d.X.obj n ⊗ d.coefficient a) (d.rightY n a)) := by
  funext r
  cases r with
  | inl f => rfl
  | inr r =>
    rcases r with ⟨n, a⟩
    rfl

/-- All full parameter families satisfying both original complete relation systems. -/
abbrev CompatibleFamily (d : Data (V := V) (I := I)) (P : V) :=
  ProductRelationMapping.Family (system d) P

/-- The original component projection is the generic complete family projection. -/
abbrev CompatibleFamily.app {d : Data (V := V) (I := I)} {P : V}
    (q : CompatibleFamily d P) : ∀ n, P ⟶ objects d n :=
  ProductRelationMapping.Family.app q

/-- The generic family condition retains both complete original relation systems. -/
abbrev CompatibleFamily.condition {d : Data (V := V) (I := I)} {P : V}
    (q : CompatibleFamily d P) : ∀ r, familyLeft d q.app r = familyRight d q.app r :=
  ProductRelationMapping.Family.condition q

/-- The original family constructor uses the actual generic complete relation condition. -/
abbrev CompatibleFamily.mk {d : Data (V := V) (I := I)} {P : V}
    (app : ∀ n, P ⟶ objects d n)
    (condition : ∀ r, familyLeft d app r = familyRight d app r) : CompatibleFamily d P :=
  ProductRelationMapping.Family.mk app condition

/-- Complete original families are determined by their component maps. -/
@[ext]
theorem CompatibleFamily.ext {d : Data (V := V) (I := I)} {P : V}
    {q q' : CompatibleFamily d P} (h : q.app = q'.app) : q = q' :=
  ProductRelationMapping.Family.ext h

/-- Actual ordinary transformations intertwining every full original right action. -/
abbrev CompatibleHom (d : Data (V := V) (I := I)) :=
  { f : d.X ⟶ d.Y // ∀ n a,
    d.rightX n a ≫ f.app (n ⊗ a) = (f.app n ▷ d.coefficient a) ≫ d.rightY n a }

/-- Every complete compatible ordinary transformation defines the original unit family. -/
def compatibleToFamily (d : Data (V := V) (I := I)) (f : CompatibleHom d) :
    CompatibleFamily d (𝟙_ V) where
  app n := eHomEquiv V (f.val.app n)
  condition r := by
    cases r with
    | inl r =>
      change eHomEquiv V (f.val.app r.left) ≫
          eHomWhiskerLeft V (d.X.obj r.left) (d.Y.map r.hom) =
        eHomEquiv V (f.val.app r.right) ≫
          eHomWhiskerRight V (d.X.map r.hom) (d.Y.obj r.right)
      exact (eHomEquiv_comp_eHomWhiskerLeft V V (f.val.app r.left) (d.Y.map r.hom)).trans
        ((congrArg (eHomEquiv V) (f.val.naturality r.hom).symm).trans
          (eHomEquiv_comp_eHomWhiskerRight V V (d.X.map r.hom) (f.val.app r.right)).symm)
    | inr r =>
      change eHomEquiv V (f.val.app (r.1 ⊗ r.2)) ≫
          eHomWhiskerRight V (d.rightX r.1 r.2) (d.Y.obj (r.1 ⊗ r.2)) =
        eHomEquiv V (f.val.app r.1) ≫
          (SphereOperator.fixedRightTensor
            (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (d.coefficient r.2)).map
            (d.X.obj r.1) (d.Y.obj r.1) ≫
          eHomWhiskerLeft V (d.X.obj r.1 ⊗ d.coefficient r.2) (d.rightY r.1 r.2)
      have hRight := congrArg
        (fun z => z ≫ eHomWhiskerLeft V (d.X.obj r.1 ⊗ d.coefficient r.2)
          (d.rightY r.1 r.2))
        (SphereOperator.fixedRightTensor_point
          (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (d.coefficient r.2) (f.val.app r.1))
      exact (eHomEquiv_comp_eHomWhiskerRight V V (d.rightX r.1 r.2) (f.val.app (r.1 ⊗ r.2))).trans
        ((congrArg (eHomEquiv V) (f.property r.1 r.2)).trans
          ((eHomEquiv_comp_eHomWhiskerLeft V V
            (f.val.app r.1 ▷ d.coefficient r.2) (d.rightY r.1 r.2)).symm.trans
            ((hRight.symm).trans (Category.assoc _ _ _))))

/-- Every complete original unit family reconstructs the actual compatible transformation. -/
def familyToCompatible (d : Data (V := V) (I := I))
    (q : CompatibleFamily d (𝟙_ V)) : CompatibleHom d :=
  ⟨{ app := fun n =>
        (eHomEquiv V (X := d.X.obj n) (Y := d.Y.obj n)).symm (q.app n)
     naturality := by
       intro i j f
       apply (eHomEquiv V).injective
       rw [← eHomEquiv_comp_eHomWhiskerRight V V, ← eHomEquiv_comp_eHomWhiskerLeft V V,
         Equiv.apply_symm_apply, Equiv.apply_symm_apply]
       exact (q.condition (.inl (Arrow.mk f))).symm },
    fun n a => by
      apply (eHomEquiv V).injective
      rw [← eHomEquiv_comp_eHomWhiskerRight V V, ← eHomEquiv_comp_eHomWhiskerLeft V V,
        ← SphereOperator.fixedRightTensor_point (MonoidalClosed.enrichedMonoidalCategoryDataSelf V),
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      have h := q.condition (.inr (n, a))
      change q.app (n ⊗ a) ≫ eHomWhiskerRight V (d.rightX n a) (d.Y.obj (n ⊗ a)) =
        q.app n ≫ (SphereOperator.fixedRightTensor
          (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (d.coefficient a)).map
          (d.X.obj n) (d.Y.obj n) ≫
          eHomWhiskerLeft V (d.X.obj n ⊗ d.coefficient a) (d.rightY n a) at h
      exact h.trans (Category.assoc _ _ _).symm⟩

/-- The complete original compatible transformation is recovered. -/
theorem family_compatible_inverse (d : Data (V := V) (I := I)) (f : CompatibleHom d) :
    familyToCompatible d (compatibleToFamily d f) = f := by
  apply Subtype.ext
  apply NatTrans.ext
  funext n
  change (eHomEquiv V).symm (eHomEquiv V (f.val.app n)) = f.val.app n
  exact (eHomEquiv V).symm_apply_apply (f.val.app n)

/-- Every full original unit-family component is recovered. -/
theorem compatible_family_inverse (d : Data (V := V) (I := I))
    (q : CompatibleFamily d (𝟙_ V)) : compatibleToFamily d (familyToCompatible d q) = q := by
  apply CompatibleFamily.ext
  funext n
  exact (eHomEquiv V (X := d.X.obj n) (Y := d.Y.obj n)).apply_symm_apply (q.app n)

/-- The unit-family correspondence preserves all original indices and full right actions. -/
def compatibleFamilyEquiv (d : Data (V := V) (I := I)) :
    CompatibleHom d ≃ CompatibleFamily d (𝟙_ V) where
  toFun := compatibleToFamily d
  invFun := familyToCompatible d
  left_inv := family_compatible_inverse d
  right_inv := compatible_family_inverse d

variable (d : Data (V := V) (I := I))
  [HasProduct (objects d)] [HasProduct (relations d)]

omit [BraidedCategory V] in
/-- The left product map needs only the original source relation components. -/
abbrev leftSystem :
    ProductRelationMapping.Data (V := V) (I := I) (R := Relation (I := I)) where
  objects := objects d
  relations := relations d
  leftIndex
    | .inl f => f.left
    | .inr (n, a) => n ⊗ a
  rightIndex
    | .inl f => f.left
    | .inr (n, a) => n ⊗ a
  leftComponent
    | .inl f => eHomWhiskerLeft V (d.X.obj f.left) (d.Y.map f.hom)
    | .inr (n, a) => eHomWhiskerRight V (d.rightX n a) (d.Y.obj (n ⊗ a))
  rightComponent
    | .inl f => eHomWhiskerLeft V (d.X.obj f.left) (d.Y.map f.hom)
    | .inr (n, a) => eHomWhiskerRight V (d.rightX n a) (d.Y.obj (n ⊗ a))

omit [BraidedCategory V] in
/-- Full first naturality relation map on the actual degree-indexed product. -/
abbrev leftMap : (∏ᶜ objects d) ⟶ ∏ᶜ relations d :=
  ProductRelationMapping.leftMap (leftSystem d)

/-- Full second naturality relation map on the same actual degree-indexed product. -/
abbrev rightMap : (∏ᶜ objects d) ⟶ ∏ᶜ relations d :=
  ProductRelationMapping.rightMap (system d)

omit [BraidedCategory V] in
/-- Every full first product projection retains the original relation family. -/
theorem leftMap_π (r : Relation (I := I)) :
    leftMap d ≫ Pi.π (relations d) r = familyLeft d (Pi.π (objects d)) r :=
  ProductRelationMapping.leftMap_π (leftSystem d) r

/-- Every full second product projection retains the original relation family. -/
theorem rightMap_π (r : Relation (I := I)) :
    rightMap d ≫ Pi.π (relations d) r = familyRight d (Pi.π (objects d)) r :=
  ProductRelationMapping.rightMap_π (system d) r

variable [HasEqualizer (leftMap d) (rightMap d)]

local instance system_hasEqualizer :
    HasEqualizer (ProductRelationMapping.leftMap (system d))
      (ProductRelationMapping.rightMap (system d)) := by
  change HasEqualizer (leftMap d) (rightMap d)
  infer_instance

/-- The independent complete original mapping object is the actual product equalizer. -/
abbrev Hom : V := ProductRelationMapping.Hom (system d)

/-- Every original full degree projection of the independent mapping object. -/
abbrev π (n : I) : Hom d ⟶ objects d n :=
  ProductRelationMapping.π (system d) n

omit [BraidedCategory V] [HasProduct (objects d)] [HasProduct (relations d)]
  [HasEqualizer (leftMap d) (rightMap d)] in
/-- The complete first relation family commutes with every parameter map. -/
theorem familyLeft_precomp {P Q : V} (f : P ⟶ Q) (q : ∀ n, Q ⟶ objects d n)
    (r : Relation (I := I)) :
    familyLeft d (fun n => f ≫ q n) r = f ≫ familyLeft d q r := by
  cases r with
  | inl r => exact Category.assoc _ _ _
  | inr r => exact Category.assoc _ _ _

omit [HasProduct (objects d)] [HasProduct (relations d)]
  [HasEqualizer (leftMap d) (rightMap d)] in
/-- The complete second relation family commutes with every parameter map. -/
theorem familyRight_precomp {P Q : V} (f : P ⟶ Q) (q : ∀ n, Q ⟶ objects d n)
    (r : Relation (I := I)) :
    familyRight d (fun n => f ≫ q n) r = f ≫ familyRight d q r := by
  cases r with
  | inl r => exact Category.assoc _ _ _
  | inr r => exact Category.assoc _ _ _

/-- Every full original relation holds on the actual independent mapping object. -/
theorem condition (r : Relation (I := I)) :
    familyLeft d (π d) r = familyRight d (π d) r :=
  ProductRelationMapping.condition (system d) r

/-- Any complete parameter family lifts to the actual product equalizer. -/
abbrev lift {P : V} (q : CompatibleFamily d P) : P ⟶ Hom d :=
  ProductRelationMapping.lift (system d) q

/-- The lift preserves every complete original mapping-space projection. -/
theorem lift_π {P : V} (q : CompatibleFamily d P) (n : I) :
    lift d q ≫ π d n = q.app n :=
  ProductRelationMapping.lift_π (system d) q n

/-- Maps into the actual independent mapping object are determined by every full projection. -/
theorem hom_ext {P : V} {f g : P ⟶ Hom d} (h : ∀ n, f ≫ π d n = g ≫ π d n) : f = g :=
  ProductRelationMapping.hom_ext (system d) h

/-- Every map into the actual mapping object defines its complete original parameter family. -/
abbrev toFamily {P : V} (f : P ⟶ Hom d) : CompatibleFamily d P :=
  ProductRelationMapping.toFamily (system d) f

/-- The whole original compatible family is recovered. -/
theorem toFamily_lift {P : V} (q : CompatibleFamily d P) : toFamily d (lift d q) = q :=
  ProductRelationMapping.toFamily_lift (system d) q

/-- The whole original map into the independent mapping object is recovered. -/
theorem lift_toFamily {P : V} (f : P ⟶ Hom d) : lift d (toFamily d f) = f :=
  ProductRelationMapping.lift_toFamily (system d) f

/-- Every full parameter Hom is represented by the actual original product equalizer. -/
abbrev representationEquiv (P : V) : (P ⟶ Hom d) ≃ CompatibleFamily d P :=
  ProductRelationMapping.representationEquiv (system d) P

/-- The independent mapping value is exactly the original complete product equalizer. -/
theorem Hom_eq : Hom d = equalizer (leftMap d) (rightMap d) :=
  ProductRelationMapping.Hom_eq (system d)

/-- Every complete projection is the actual original equalizer/product projection. -/
theorem π_heq (n : I) : HEq (π d n)
    (equalizer.ι (leftMap d) (rightMap d) ≫ Pi.π (objects d) n) :=
  ProductRelationMapping.π_heq (system d) n

/-- The independent mapping object represents exactly all complete compatible transformations. -/
def unitHomEquiv : CompatibleHom d ≃ (𝟙_ V ⟶ Hom d) :=
  (compatibleFamilyEquiv d).trans (representationEquiv d (𝟙_ V)).symm

/-- Every whole original degree of a represented map is unchanged. -/
theorem unitHomEquiv_π (f : CompatibleHom d) (n : I) :
    unitHomEquiv d f ≫ π d n = eHomEquiv V (f.val.app n) := by
  let q := compatibleToFamily d f
  have h := ProductRelationMapping.lift_π (system d) q n
  exact h

end CategoryTheory.Enriched.RightActionMapping

namespace CategoryTheory.Enriched.RightActionMapping

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]

/-- Actual compatible unit points prove both entire original parameter relations. -/
def familyOfPoints (d : Data (V := V) (I := I)) (P : V)
    (a : ∀ i, P ⟶ objects d i) (hsep : IsSeparator (𝟙_ V))
    (hpoint : ∀ p : 𝟙_ V ⟶ P, ∃ f : CompatibleHom d,
      ∀ i, p ≫ a i = eHomEquiv V (f.val.app i)) : CompatibleFamily d P where
  app := a
  condition r := by
    apply hsep.def
    intro p
    obtain ⟨f, hp⟩ := hpoint p
    let q := compatibleToFamily d f
    have apps : (fun i => p ≫ a i) = q.app := funext hp
    exact (familyLeft_precomp d p a r).symm.trans
      ((congrArg (fun z => familyLeft d z r) apps).trans
        ((q.condition r).trans
          ((congrArg (fun z => familyRight d z r) apps).symm.trans
            (familyRight_precomp d p a r))))

end CategoryTheory.Enriched.RightActionMapping
