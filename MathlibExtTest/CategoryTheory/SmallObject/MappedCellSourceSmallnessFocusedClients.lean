/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.SmallObject.MappedCellSourceSmallness
import Mathlib.CategoryTheory.Presentable.Type

/-!
# Focused clients for source smallness on mapped cell diagrams

* For an arbitrary adjoint family, the source-Hom condition on evaluated cell
  diagrams yields preservation at every free image `(L a).map g`, the canonical
  mapped cocone, and the small-object argument with functorial factorizations.
* Concretely, in `Type` with the identity adjunction and the single generator
  `Fin 1 ⟶ Fin 2`, the condition holds at `ℵ₀` because finite types are
  `ℵ₀`-presentable; the generator family is nonempty and has the small-object
  argument.
* Boundary case: for the empty base property the condition is vacuous and the
  generator family is empty.
-/

noncomputable section

universe w uS uC vC uD vD

open CategoryTheory Limits MorphismProperty Opposite HomotopicalAlgebra

namespace MathlibExtTest.CategoryTheory.SmallObject.MappedCellSourceSmallness

section General

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] {S : Type uS}
  (L : S → C ⥤ D) (R : S → D ⥤ C) (adj : ∀ s, L s ⊣ R s) (P : MorphismProperty C)
  (κ : Cardinal.{w}) [OrderBot κ.ord.ToType]
  [∀ s, PreservesColimitsOfShape κ.ord.ToType (R s)]

/-- Preservation holds at the free image of a base member, the case produced by
`map_mem_adjointFamilyGenerators`. -/
example (hSource : MappedCellSourceSmallness.Condition L R P κ) (a : S) {A B : C}
    (g : A ⟶ B) (hg : P g) {X Y : D} (f : X ⟶ Y)
    (c : RelativeCellComplex.{w}
      (fun _ : κ.ord.ToType => (adjointFamilyGenerators L P).homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (op ((L a).obj A))) :=
  MappedCellSourceSmallness.preservesColimit L R P κ adj hSource ((L a).map g)
    (map_mem_adjointFamilyGenerators L P a g hg) f c

/-- Any colimit cocone of the cell diagram is preserved by the source Hom functor. -/
example (hSource : MappedCellSourceSmallness.Condition L R P κ) {A B X Y : D}
    (i : A ⟶ B) (hi : adjointFamilyGenerators L P i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{w}
      (fun _ : κ.ord.ToType => (adjointFamilyGenerators L P).homFamily) f)
    (d : Cocone c.F) (hd : IsColimit d) :
    IsColimit ((coyoneda.obj (op A)).mapCocone d) :=
  haveI := MappedCellSourceSmallness.preservesColimit L R P κ adj hSource i hi f c
  isColimitOfPreserves _ hd

variable [Fact κ.IsRegular] [Small.{w} S] [P.IsSmall.{w}] [LocallySmall.{w} D]
  [HasPushouts D] [HasCoproducts.{w} D] [HasIterationOfShape κ.ord.ToType D]

/-- The derived small-object argument provides functorial factorizations. -/
example (hSource : MappedCellSourceSmallness.Condition L R P κ) :
    HasFunctorialFactorization (adjointFamilyGenerators L P).rlp.llp
      (adjointFamilyGenerators L P).rlp :=
  haveI := MappedCellSourceSmallness.hasSmallObjectArgument L R P κ adj hSource
  inferInstance

/-- Boundary case: the empty base property satisfies the condition vacuously. -/
example : MappedCellSourceSmallness.Condition L R ⊥ κ :=
  fun _ _ _ _ hi => absurd hi id

/-- Boundary case: the empty base property has no generators. -/
example {X Y : D} (f : X ⟶ Y) : ¬ adjointFamilyGenerators L ⊥ f := by
  rw [adjointFamilyGenerators_iff]
  rintro ⟨⟨_, ⟨_, h⟩⟩, -⟩
  exact h

end General

section Types

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

/-- The single generator `Fin 1 ⟶ Fin 2`. -/
abbrev gen : MorphismProperty (Type) :=
  MorphismProperty.ofHoms (fun _ : Unit => TypeCat.ofHom (Fin.castSucc : Fin 1 → Fin 2))

/-- The identity functor family. -/
abbrev idFam : PUnit.{1} → Type ⥤ Type := fun _ => 𝟭 Type

lemma finite_of_gen {A B : Type} {i : A ⟶ B} (hi : gen i) : Finite A := by
  obtain ⟨_, h⟩ := (MorphismProperty.ofHoms_iff _ i).1 hi
  have hA : A = Fin 1 := congrArg Comma.left h
  subst hA
  infer_instance

/-- Finite sources are `ℵ₀`-presentable, so the source-Hom condition holds. -/
lemma condition_gen :
    MappedCellSourceSmallness.Condition idFam idFam gen Cardinal.aleph0.{0} := by
  intro s A B i hi X Y f c
  have : Finite A := finite_of_gen hi
  have : IsCardinalPresentable A Cardinal.aleph0.{0} :=
    HasCardinalLT.isCardinalPresentable (hasCardinalLT_of_finite A _ le_rfl)
  have := preservesColimitsOfShape_of_isCardinalPresentable A Cardinal.aleph0.{0}
    Cardinal.aleph0.{0}.ord.ToType
  infer_instance

/-- The generator family is nonempty. -/
example : adjointFamilyGenerators idFam gen
    ((𝟭 Type).map (TypeCat.ofHom (Fin.castSucc : Fin 1 → Fin 2))) :=
  map_mem_adjointFamilyGenerators idFam gen PUnit.unit _ (MorphismProperty.ofHoms.mk ())

/-- The identity adjunction family satisfies every eligibility field at `ℵ₀`. -/
example : (adjointFamilyGenerators idFam gen).IsCardinalForSmallObjectArgument
    Cardinal.aleph0.{0} :=
  MappedCellSourceSmallness.isCardinalForSmallObjectArgument idFam idFam gen _
    (fun _ => Adjunction.id) condition_gen

/-- The concrete generator family has the small-object argument. -/
example : (adjointFamilyGenerators idFam gen).HasSmallObjectArgument.{0} :=
  MappedCellSourceSmallness.hasSmallObjectArgument idFam idFam gen _
    (fun _ => Adjunction.id) condition_gen

end Types

end MathlibExtTest.CategoryTheory.SmallObject.MappedCellSourceSmallness
