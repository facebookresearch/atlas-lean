/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.MorphismProperty.PushoutProduct
public import MathlibExt.AlgebraicTopology.ModelCategory.SmallGenerator

/-!
# Literal indexed generator families from actual adjunctions

The index and actual base-family arrow remain correlated in the label.
The strict-image description reuses the existing lifting and size APIs.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w s vC vD uC uD

open CategoryTheory

namespace CategoryTheory.MorphismProperty

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D] {S : Type s}

/-- The actual free images, indexed by the original index and base member. -/
def adjointFamilyGenerators (L : S → C ⥤ D) (P : MorphismProperty C) :
    MorphismProperty D :=
  MorphismProperty.ofHoms (fun q : S × P.toSet => (L q.1).map q.2.1.hom)

/-- Membership retains equality of the complete original indexed arrows. -/
theorem adjointFamilyGenerators_iff (L : S → C ⥤ D) (P : MorphismProperty C)
    {X Y : D} (f : X ⟶ Y) :
    adjointFamilyGenerators L P f ↔
      ∃ q : S × P.toSet, Arrow.mk f = Arrow.mk ((L q.1).map q.2.1.hom) :=
  MorphismProperty.ofHoms_iff _ f

/-- Every actual free image of a supplied base member belongs to the family. -/
theorem map_mem_adjointFamilyGenerators (L : S → C ⥤ D) (P : MorphismProperty C)
    (a : S) {A B : C} (f : A ⟶ B) (hf : P f) :
    adjointFamilyGenerators L P ((L a).map f) :=
  MorphismProperty.ofHoms.mk
    (f := fun q : S × P.toSet => (L q.1).map q.2.1.hom) (a, ⟨Arrow.mk f, hf⟩)

/-- The literal labels describe the same property as the indexed strict images. -/
theorem adjointFamilyGenerators_eq_iSup_strictMap
    (L : S → C ⥤ D) (P : MorphismProperty C) :
    adjointFamilyGenerators L P = ⨆ a : S, P.strictMap (L a) := by
  ext X Y f
  rw [MorphismProperty.iSup_iff]
  constructor
  · rintro ⟨q⟩
    exact ⟨q.1, P.map_mem_strictMap (L q.1) q.2.1.hom q.2.2⟩
  · rintro ⟨a, hf⟩
    cases hf with
    | map hf => exact map_mem_adjointFamilyGenerators L P a _ hf

/-- Indexed strict images preserve family size in an independent universe. -/
theorem adjointFamilyGenerators_isSmall
    (L : S → C ⥤ D) (P : MorphismProperty C)
    [Small.{w} S] [P.IsSmall.{w}] :
    (adjointFamilyGenerators L P).IsSmall.{w} := by
  rw [adjointFamilyGenerators_eq_iSup_strictMap]
  let _ (a : S) : (P.strictMap (L a)).IsSmall.{w} :=
    IsSmall.strictMap (inferInstance : P.IsSmall.{w}) (L a)
  infer_instance

/-- Actual right lifting is exactly base right lifting at every right adjoint. -/
theorem adjointFamilyGenerators_rlp_iff
    (L : S → C ⥤ D) (R : S → D ⥤ C) (adj : ∀ a, L a ⊣ R a)
    (P : MorphismProperty C) {X Y : D} (f : X ⟶ Y) :
    (adjointFamilyGenerators L P).rlp f ↔ ∀ a : S, P.rlp ((R a).map f) := by
  rw [adjointFamilyGenerators_eq_iSup_strictMap]
  constructor
  · intro hf a
    have hImage : (P.strictMap (L a)).rlp f := by
      intro A B g hg
      exact hf g ((MorphismProperty.iSup_iff _ g).mpr ⟨a, hg⟩)
    rw [strictMap_rlp_eq_inverseImage_rlp P (L a) (R a) (adj a)] at hImage
    exact hImage
  · intro hf A B g hg
    obtain ⟨a, ha⟩ := (MorphismProperty.iSup_iff _ g).mp hg
    have hImage : (P.strictMap (L a)).rlp f := by
      rw [strictMap_rlp_eq_inverseImage_rlp P (L a) (R a) (adj a)]
      exact hf a
    exact hImage g ha

end CategoryTheory.MorphismProperty
