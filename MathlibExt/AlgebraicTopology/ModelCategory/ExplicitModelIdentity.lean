/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.ModelCategory.Transport
public import Mathlib.CategoryTheory.InducedCategory
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction

/-!
# Identity comparisons between two explicit model records

Each actual model record has its own induced carrier.  Stock model transport
retains its three complete morphism classes, so both records coexist with
their original dictionary contexts.  The comparison functors keep every
underlying object and map.  Their full Hom functions, units, counits,
naturalities and triangles are explicit.

Equality of the actual cofibration classes and inclusion of the actual weak
classes prove that the forward identity is left Quillen.  The reverse
fibration inclusion and equality of the two trivial-fibration classes are
then derived from the actual model axioms.  No model-existence or localization
universal-property assumption is introduced by this interface.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.ExplicitModelIdentity

variable {C : Type u} [Category.{v} C]

/-- The actual record itself keys its carrier, with the original category retained. -/
abbrev Carrier (m : ModelCategory C) : Type u :=
  InducedCategory C (fun X : { _X : C // m = m } => X.1)

/-- Regard an entire original object or map in the carrier of the chosen model. -/
def ofBase (m : ModelCategory C) : C ⥤ Carrier m where
  obj X := ⟨X, rfl⟩
  map f := InducedCategory.homMk f

/-- Retain every original underlying object and the whole original map. -/
def toBase (m : ModelCategory C) : Carrier m ⥤ C where
  obj X := X.1
  map f := f.hom

/-- The entire categorical comparison retains both complete original identity functions. -/
def baseEquivalence (m : ModelCategory C) : C ≌ Carrier m where
  functor := ofBase m
  inverse := toBase m
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun X => InducedCategory.isoMk (Iso.refl X.1)) (by
      intro X Y f
      apply InducedCategory.hom_ext
      exact (Category.comp_id f.hom).trans (Category.id_comp f.hom).symm)
  functor_unitIso_comp X := by
    apply InducedCategory.hom_ext
    exact Category.comp_id (𝟙 X)

/-- Stock transport installs the supplied actual model only on its own carrier. -/
@[instance_reducible]
instance carrierModel (m : ModelCategory C) : ModelCategory (Carrier m) := by
  letI : ModelCategory C := m
  letI : CategoryWithCofibrations (Carrier m) :=
    ⟨m.categoryWithCofibrations.cofibrations.inverseImage (toBase m)⟩
  letI : CategoryWithFibrations (Carrier m) :=
    ⟨m.categoryWithFibrations.fibrations.inverseImage (toBase m)⟩
  letI : CategoryWithWeakEquivalences (Carrier m) :=
    ⟨m.categoryWithWeakEquivalences.weakEquivalences.inverseImage (toBase m)⟩
  exact ModelCategory.transport (baseEquivalence m).symm rfl rfl rfl

/-- Every cofibration test retains the whole actual source model field and underlying map. -/
theorem cofibrations_iff (m : ModelCategory C) {X Y : Carrier m} (f : X ⟶ Y) :
    cofibrations (Carrier m) f ↔ m.categoryWithCofibrations.cofibrations f.hom := Iff.rfl

/-- Every fibration test retains the whole actual source model field and underlying map. -/
theorem fibrations_iff (m : ModelCategory C) {X Y : Carrier m} (f : X ⟶ Y) :
    fibrations (Carrier m) f ↔ m.categoryWithFibrations.fibrations f.hom := Iff.rfl

/-- Every weak test retains the whole actual model weak field and underlying map. -/
theorem weakEquivalences_iff (m : ModelCategory C) {X Y : Carrier m} (f : X ⟶ Y) :
    weakEquivalences (Carrier m) f ↔
      m.categoryWithWeakEquivalences.weakEquivalences f.hom := Iff.rfl

/-- Both complete original model fields are retained in the trivial-cofibration test. -/
theorem trivialCofibrations_iff (m : ModelCategory C) {X Y : Carrier m} (f : X ⟶ Y) :
    trivialCofibrations (Carrier m) f ↔
      m.categoryWithCofibrations.cofibrations f.hom ∧
        m.categoryWithWeakEquivalences.weakEquivalences f.hom := Iff.rfl

/-- Both complete original model fields are retained in the trivial-fibration test. -/
theorem trivialFibrations_iff (m : ModelCategory C) {X Y : Carrier m} (f : X ⟶ Y) :
    trivialFibrations (Carrier m) f ↔
      m.categoryWithFibrations.fibrations f.hom ∧
        m.categoryWithWeakEquivalences.weakEquivalences f.hom := Iff.rfl

/-- The full comparison acts by the same entire identity object and map functions. -/
def comparison (m n : ModelCategory C) : Carrier m ⥤ Carrier n where
  obj X := ⟨X.1, rfl⟩
  map f := InducedCategory.homMk f.hom

/-- Every complete comparison map has exactly the given original underlying function. -/
theorem comparison_map_hom (m n : ModelCategory C) {X Y : Carrier m} (f : X ⟶ Y) :
    ((comparison m n).map f).hom = f.hom := rfl

/-- Both actual record contexts are retained by the entire categorical identity equivalence. -/
def comparisonEquivalence (m n : ModelCategory C) : Carrier m ≌ Carrier n where
  functor := comparison m n
  inverse := comparison n m
  unitIso := NatIso.ofComponents
    (fun X => InducedCategory.isoMk (Iso.refl X.1)) (by
      intro X Y f
      apply InducedCategory.hom_ext
      exact (Category.comp_id f.hom).trans (Category.id_comp f.hom).symm)
  counitIso := NatIso.ofComponents
    (fun X => InducedCategory.isoMk (Iso.refl X.1)) (by
      intro X Y f
      apply InducedCategory.hom_ext
      exact (Category.comp_id f.hom).trans (Category.id_comp f.hom).symm)
  functor_unitIso_comp X := by
    apply InducedCategory.hom_ext
    exact Category.comp_id (𝟙 X.1)

/-- The complete identity adjunction is the adjunction of those actual comparison functions. -/
def identityAdjunction (m n : ModelCategory C) : comparison m n ⊣ comparison n m :=
  (comparisonEquivalence m n).toAdjunction

/-- Every whole unit component retains the original underlying source identity. -/
theorem identityAdjunction_unit_hom (m n : ModelCategory C) (X : Carrier m) :
    ((identityAdjunction m n).unit.app X).hom = 𝟙 X.1 := rfl

/-- Every whole counit component retains the original underlying target identity. -/
theorem identityAdjunction_counit_hom (m n : ModelCategory C) (Y : Carrier n) :
    ((identityAdjunction m n).counit.app Y).hom = 𝟙 Y.1 := rfl

/-- The actual forward Hom function retains every entire original underlying map. -/
theorem identityAdjunction_homEquiv_hom (m n : ModelCategory C)
    (X : Carrier m) (Y : Carrier n) (f : (comparison m n).obj X ⟶ Y) :
    ((identityAdjunction m n).homEquiv X Y f).hom = f.hom := by
  rw [Adjunction.homEquiv_unit]
  change 𝟙 X.1 ≫ f.hom = f.hom
  exact Category.id_comp _

/-- The actual inverse Hom function retains the same entire original underlying map. -/
theorem identityAdjunction_homEquiv_symm_hom (m n : ModelCategory C)
    (X : Carrier m) (Y : Carrier n) (f : X ⟶ (comparison n m).obj Y) :
    (((identityAdjunction m n).homEquiv X Y).symm f).hom = f.hom := by
  rw [Adjunction.homEquiv_counit]
  change f.hom ≫ ((identityAdjunction m n).counit.app Y).hom = f.hom
  rw [identityAdjunction_counit_hom]
  exact Category.comp_id _

/-- Every actual source action retains the whole identity unit naturality square. -/
theorem identityAdjunction_unit_naturality (m n : ModelCategory C)
    {X Y : Carrier m} (f : X ⟶ Y) :
    f ≫ (identityAdjunction m n).unit.app Y =
      (identityAdjunction m n).unit.app X ≫
        (comparison n m).map ((comparison m n).map f) :=
  (identityAdjunction m n).unit.naturality f

/-- Every actual target action retains the whole identity counit naturality square. -/
theorem identityAdjunction_counit_naturality (m n : ModelCategory C)
    {X Y : Carrier n} (f : X ⟶ Y) :
    (comparison m n).map ((comparison n m).map f) ≫
      (identityAdjunction m n).counit.app Y =
        (identityAdjunction m n).counit.app X ≫ f :=
  (identityAdjunction m n).counit.naturality f

/-- The complete identity functors and actual unit/counit satisfy the first triangle. -/
theorem identityAdjunction_first_triangle (m n : ModelCategory C) (X : Carrier m) :
    (comparison m n).map ((identityAdjunction m n).unit.app X) ≫
      (identityAdjunction m n).counit.app ((comparison m n).obj X) = 𝟙 _ :=
  (identityAdjunction m n).left_triangle_components X

/-- The full reverse identity functor and both actual components satisfy the second triangle. -/
theorem identityAdjunction_second_triangle (m n : ModelCategory C) (Y : Carrier n) :
    (identityAdjunction m n).unit.app ((comparison n m).obj Y) ≫
      (comparison n m).map ((identityAdjunction m n).counit.app Y) = 𝟙 _ :=
  (identityAdjunction m n).right_triangle_components Y

/-- Actual class equality and weak inclusion prove the entire forward identity Quillen pair. -/
theorem identityAdjunction_isQuillen (m n : ModelCategory C)
    (hC : m.categoryWithCofibrations.cofibrations = n.categoryWithCofibrations.cofibrations)
    (hW : m.categoryWithWeakEquivalences.weakEquivalences ≤
      n.categoryWithWeakEquivalences.weakEquivalences) :
    (identityAdjunction m n).IsQuillenAdjunction where
  preservesCofibrations := by
    intro X Y f hf
    change m.categoryWithCofibrations.cofibrations f.hom at hf
    change n.categoryWithCofibrations.cofibrations f.hom
    rw [← hC]
    exact hf
  preservesTrivialCofibrations := by
    intro X Y f hf
    change m.categoryWithCofibrations.cofibrations f.hom ∧
      m.categoryWithWeakEquivalences.weakEquivalences f.hom at hf
    change n.categoryWithCofibrations.cofibrations f.hom ∧
      n.categoryWithWeakEquivalences.weakEquivalences f.hom
    exact ⟨hC ▸ hf.1, hW _ hf.2⟩

/-- The same actual classes give reverse fibration preservation through the proven adjunction. -/
theorem identityAdjunction_preservesReverseFibrations (m n : ModelCategory C)
    (hC : m.categoryWithCofibrations.cofibrations = n.categoryWithCofibrations.cofibrations)
    (hW : m.categoryWithWeakEquivalences.weakEquivalences ≤
      n.categoryWithWeakEquivalences.weakEquivalences) :
    PreservesFibrations (comparison n m) := by
  let _ := identityAdjunction_isQuillen m n hC hW
  exact CategoryTheory.Adjunction.IsQuillenAdjunction.preservesFibrations
    (adj := identityAdjunction m n)

/-- Equal actual cofibration classes force equal full trivial-fibration classes. -/
theorem actual_trivialFibrations_eq (m n : ModelCategory C)
    (hC : m.categoryWithCofibrations.cofibrations = n.categoryWithCofibrations.cofibrations) :
    m.categoryWithFibrations.fibrations ⊓ m.categoryWithWeakEquivalences.weakEquivalences =
      n.categoryWithFibrations.fibrations ⊓ n.categoryWithWeakEquivalences.weakEquivalences := by
  have hm : m.categoryWithCofibrations.cofibrations.rlp =
      m.categoryWithFibrations.fibrations ⊓ m.categoryWithWeakEquivalences.weakEquivalences := by
    let _ : ModelCategory C := m
    exact cofibrations_rlp C
  have hn : n.categoryWithCofibrations.cofibrations.rlp =
      n.categoryWithFibrations.fibrations ⊓ n.categoryWithWeakEquivalences.weakEquivalences := by
    let _ : ModelCategory C := n
    exact cofibrations_rlp C
  exact hm.symm.trans ((congrArg CategoryTheory.MorphismProperty.rlp hC).trans hn)

end HomotopicalAlgebra.ExplicitModelIdentity
