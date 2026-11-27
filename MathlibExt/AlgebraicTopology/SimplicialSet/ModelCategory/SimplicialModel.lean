/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetIhomFibration
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import
  Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
import Mathlib.CategoryTheory.Adhesive.PushoutProduct

/-!
# Pushout products and pullback homs in the Kan–Quillen model

In the Kan–Quillen model structure on simplicial sets, trivial cofibrations are
anodyne extensions. The cartesian pushout product
`(B × K) ∪_(A × K) (A × L) → B × L` of two cofibrations is a cofibration and
is trivial when either factor is trivial.

Dually, the internal-hom comparison
`Map(B,X) → Map(A,X) ×_(Map(A,Y)) Map(B,Y)` is a trivial fibration when the
cofibration `A → B` is trivial or the Kan fibration `X → Y` is trivial. These
are the pushout-product and pullback-hom forms of the simplicial model axiom.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed
  HomotopicalAlgebra MorphismProperty
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace SSet

/--
In the selected Kan–Quillen model structure, the anodyne-extension property equals
the trivial-cofibration property.
-/
theorem anodyneExtensions_eq_trivialCofibrations :
    anodyneExtensions.{u} = trivialCofibrations SSet.{u} := by
  rw [anodyneExtensions_eq_llp_rlp,
    ← modelCategoryQuillen.fibrations_eq]
  exact fibrations_llp _

/--
The cartesian pushout product of two cofibrations of simplicial sets is a cofibration.
-/
theorem cofibration_pushoutProduct
    {A B K L : SSet.{u}} (i : A ⟶ B) (j : K ⟶ L)
    [Cofibration i] [Cofibration j] :
    Cofibration ((Arrow.mk i □ Arrow.mk j).hom) := by
  let _ : Mono i := modelCategoryQuillen.mono_of_cofibration i
  let _ : Mono j := modelCategoryQuillen.mono_of_cofibration j
  let _ : Mono (Arrow.mk i).hom := inferInstanceAs (Mono i)
  let _ : Mono (Arrow.mk j).hom := inferInstanceAs (Mono j)
  exact modelCategoryQuillen.cofibration_of_mono _

/--
The pushout product of a trivial cofibration with a cofibration is a trivial
cofibration.
-/
theorem pushoutProduct_mem_trivialCofibrations_of_left
    {A B K L : SSet.{u}} (i : A ⟶ B) (j : K ⟶ L)
    [Cofibration i] [WeakEquivalence i] [Cofibration j] :
    trivialCofibrations SSet.{u} ((Arrow.mk i □ Arrow.mk j).hom) := by
  rw [← anodyneExtensions_eq_trivialCofibrations]
  let sq := Functor.PushoutObjObj.ofHasPushout
    (curriedTensor SSet.{u}) i j
  change anodyneExtensions sq.ι
  apply anodyneExtensions_pushoutObjObjι' sq
  rw [anodyneExtensions_eq_trivialCofibrations]
  exact mem_trivialCofibrations i

/--
The pushout product of a cofibration with a trivial cofibration is a trivial
cofibration.
-/
theorem pushoutProduct_mem_trivialCofibrations_of_right
    {A B K L : SSet.{u}} (i : A ⟶ B) (j : K ⟶ L)
    [Cofibration i] [Cofibration j] [WeakEquivalence j] :
    trivialCofibrations SSet.{u} ((Arrow.mk i □ Arrow.mk j).hom) := by
  rw [← anodyneExtensions_eq_trivialCofibrations]
  let sq := Functor.PushoutObjObj.ofHasPushout
    (curriedTensor SSet.{u}) i j
  change anodyneExtensions sq.ι
  apply anodyneExtensions_pushoutObjObjι sq
  rw [anodyneExtensions_eq_trivialCofibrations]
  exact mem_trivialCofibrations j

private theorem ihomToPullback_mem_cofibrations_rlp
    {A B X Y : SSet.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    (h : ∀ {K L : SSet.{u}} (j : K ⟶ L),
      cofibrations SSet.{u} j →
        HasLiftingProperty ((Arrow.mk i □ Arrow.mk j).hom) p) :
    (cofibrations SSet.{u}).rlp (ihomToPullback i p) := by
  intro K L j hj
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout
    (curriedTensor SSet.{u}) i j
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback
    MonoidalClosed.internalHom i p
  have hl : HasLiftingProperty sq₁₂.ι p := by
    change HasLiftingProperty ((Arrow.mk i □ Arrow.mk j).hom) p
    exact h j hj
  have hr : HasLiftingProperty j sq₁₃.π :=
    (MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff
      sq₁₂ sq₁₃).mp hl
  change HasLiftingProperty j (ihomToPullback i p)
  exact hr

/--
For a trivial cofibration `i : A → B` and a Kan fibration `p : X → Y`, the
internal-hom pullback comparison is a trivial fibration.
-/
theorem ihomToPullback_mem_trivialFibrations_of_left
    {A B X Y : SSet.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [WeakEquivalence i] [Fibration p] :
    trivialFibrations SSet.{u} (ihomToPullback i p) := by
  have hrlp : (cofibrations SSet.{u}).rlp (ihomToPullback i p) :=
    ihomToPullback_mem_cofibrations_rlp i p (by
      intro K L j hj
      let _ : Cofibration j := (cofibration_iff j).2 hj
      have htriv := pushoutProduct_mem_trivialCofibrations_of_left i j
      have hclasses := (mem_trivialCofibrations_iff _).1 htriv
      let _ : Cofibration ((Arrow.mk i □ Arrow.mk j).hom) := hclasses.1
      let _ : WeakEquivalence ((Arrow.mk i □ Arrow.mk j).hom) := hclasses.2
      exact ModelCategory.cm4a _ _)
  have htriv : trivialFibrations SSet.{u} (ihomToPullback i p) := by
    rw [← cofibrations_rlp]
    exact hrlp
  have hclasses := (mem_trivialFibrations_iff _).1 htriv
  rw [mem_trivialFibrations_iff]
  exact ⟨SSet.fibration_ihomToPullback i p, hclasses.2⟩

/--
For a cofibration `i : A → B` and a trivial fibration `p : X → Y`, the
internal-hom pullback comparison is a trivial fibration.
-/
theorem ihomToPullback_mem_trivialFibrations_of_right
    {A B X Y : SSet.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [Fibration p] [WeakEquivalence p] :
    trivialFibrations SSet.{u} (ihomToPullback i p) := by
  have hrlp : (cofibrations SSet.{u}).rlp (ihomToPullback i p) :=
    ihomToPullback_mem_cofibrations_rlp i p (by
      intro K L j hj
      let _ : Cofibration j := (cofibration_iff j).2 hj
      let _ : Cofibration ((Arrow.mk i □ Arrow.mk j).hom) :=
        cofibration_pushoutProduct i j
      exact ModelCategory.cm4b _ _)
  have htriv : trivialFibrations SSet.{u} (ihomToPullback i p) := by
    rw [← cofibrations_rlp]
    exact hrlp
  have hclasses := (mem_trivialFibrations_iff _).1 htriv
  rw [mem_trivialFibrations_iff]
  exact ⟨SSet.fibration_ihomToPullback i p, hclasses.2⟩

end SSet
