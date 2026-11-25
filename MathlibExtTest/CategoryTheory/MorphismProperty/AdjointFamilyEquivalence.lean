/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamily.Equivalence

/-! # Fixed original indexed-family and same-cardinal contracts -/

set_option autoImplicit false
noncomputable section
universe w uV vV uC vC uD vD uS uA u
open CategoryTheory Limits Opposite HomotopicalAlgebra MorphismProperty

namespace MathlibExtTest.AdjointFamilyEquivalence

variable {V : Type uV} [Category.{vV} V]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {S : Type uS} {A : Type uA}
  (e : C ≌ D) (K : S → V ⥤ C) (L : A → V ⥤ D) (j : S → A)
  (q : ∀ s, K s ≅ L (j s) ⋙ e.inverse) (P : MorphismProperty V)

example :
    adjointFamilyGenerators K P ≤
      ((adjointFamilyGenerators L P).strictMap e.inverse).isoClosure :=
  adjointFamilyGenerators_le_strictMap_isoClosure e K L j q P

example (s : S) {X Y : V} (f : X ⟶ Y) (hf : P f) :
    ((adjointFamilyGenerators L P).strictMap e.inverse)
      (e.inverse.map ((L (j s)).map f)) :=
  map_mem_strictMap _ _ _ (map_mem_adjointFamilyGenerators L P (j s) f hf)

example (s : S) {X Y : V} (f : X ⟶ Y) :
    Arrow.mk ((K s).map f) ≅ Arrow.mk (e.inverse.map ((L (j s)).map f)) :=
  Arrow.isoOfNatIso (q s) (Arrow.mk f)

example (s : S) {X Y : V} (f : X ⟶ Y) (hf : P f) :
    ∃ target : ((adjointFamilyGenerators L P).strictMap e.inverse).toSet,
      Nonempty (Arrow.mk ((K s).map f) ≅ Arrow.mk target.1.hom) := by
  refine ⟨⟨Arrow.mk (e.inverse.map ((L (j s)).map f)), ?_⟩, ?_⟩
  · exact map_mem_strictMap _ _ _ (map_mem_adjointFamilyGenerators L P (j s) f hf)
  · exact ⟨Arrow.isoOfNatIso (q s) (Arrow.mk f)⟩

example (hj : Function.Surjective j) :
    (adjointFamilyGenerators K P).isoClosure =
      ((adjointFamilyGenerators L P).strictMap e.inverse).isoClosure :=
  adjointFamilyGenerators_isoClosure_eq_strictMap e K L j hj q P

example (hj : Function.Surjective j) :
    (adjointFamilyGenerators K P).rlp =
      ((adjointFamilyGenerators L P).strictMap e.inverse).rlp :=
  adjointFamilyGenerators_rlp_eq_strictMap e K L j hj q P

example (hj : Function.Surjective j) {X Y : C} (f : X ⟶ Y) :
    (adjointFamilyGenerators K P).rlp f ↔
      ((adjointFamilyGenerators L P).strictMap e.inverse).rlp f := by
  rw [adjointFamilyGenerators_rlp_eq_strictMap e K L j hj q P]

example (hj : Function.Surjective j) :
    (adjointFamilyGenerators K P).rlp.llp =
      ((adjointFamilyGenerators L P).strictMap e.inverse).rlp.llp :=
  congrArg MorphismProperty.llp (adjointFamilyGenerators_rlp_eq_strictMap e K L j hj q P)

section SameCardinal

variable (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} S] [P.IsSmall.{w}]
  (hQ : (adjointFamilyGenerators L P).IsCardinalForSmallObjectArgument κ)

example : (adjointFamilyGenerators K P).IsCardinalForSmallObjectArgument κ :=
  adjointFamilyGenerators_isCardinalForSmallObjectArgument_of_equivalence e K L j q P κ hQ

example : (adjointFamilyGenerators K P).IsSmall.{w} :=
  (adjointFamilyGenerators_isCardinalForSmallObjectArgument_of_equivalence
    e K L j q P κ hQ).isSmall

example : LocallySmall.{w} C :=
  (adjointFamilyGenerators_isCardinalForSmallObjectArgument_of_equivalence
    e K L j q P κ hQ).locallySmall

example : HasPushouts C :=
  (adjointFamilyGenerators_isCardinalForSmallObjectArgument_of_equivalence
    e K L j q P κ hQ).hasPushouts

example : HasCoproducts.{w} C :=
  (adjointFamilyGenerators_isCardinalForSmallObjectArgument_of_equivalence
    e K L j q P κ hQ).hasCoproducts

example : HasIterationOfShape κ.ord.ToType C :=
  (adjointFamilyGenerators_isCardinalForSmallObjectArgument_of_equivalence
    e K L j q P κ hQ).hasIterationOfShape

example {X Y Z W : C} (i : X ⟶ Y) (hi : adjointFamilyGenerators K P i)
    (f : Z ⟶ W)
    (c : RelativeCellComplex.{w}
      (fun _ : κ.ord.ToType => (adjointFamilyGenerators K P).homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (op X)) :=
  (adjointFamilyGenerators_isCardinalForSmallObjectArgument_of_equivalence
    e K L j q P κ hQ).preservesColimit i hi f c

example {X Y : C} {f : X ⟶ Y}
    (labels : (adjointFamilyGenerators K P).toSet →
      ((adjointFamilyGenerators L P).strictMap e.inverse).toSet)
    (arrowIso : ∀ p, Arrow.mk p.1.hom ≅ Arrow.mk (labels p).1.hom)
    (c : RelativeCellComplex.{w}
      (fun _ : κ.ord.ToType => (adjointFamilyGenerators K P).homFamily) f) :
    (c.reindexByArrowIso (adjointFamilyGenerators K P)
      ((adjointFamilyGenerators L P).strictMap e.inverse) labels arrowIso).F = c.F ∧
      (c.reindexByArrowIso (adjointFamilyGenerators K P)
        ((adjointFamilyGenerators L P).strictMap e.inverse) labels arrowIso).incl = c.incl :=
  ⟨rfl, rfl⟩

end SameCardinal

section EmptyAndInfinite

variable (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [P.IsSmall.{w}] (hQ : (adjointFamilyGenerators L P).IsCardinalForSmallObjectArgument κ)

example (K₀ : PEmpty → V ⥤ C) (j₀ : PEmpty → A)
    (q₀ : ∀ s, K₀ s ≅ L (j₀ s) ⋙ e.inverse) :
    (adjointFamilyGenerators K₀ P).IsCardinalForSmallObjectArgument κ :=
  adjointFamilyGenerators_isCardinalForSmallObjectArgument_of_equivalence
    e K₀ L j₀ q₀ P κ hQ

example (Lₙ : ℕ → V ⥤ D)
    (hQₙ : (adjointFamilyGenerators Lₙ P).IsCardinalForSmallObjectArgument κ) :
    (adjointFamilyGenerators
      (fun _ : ℕ => Lₙ 0 ⋙ e.inverse) P).IsCardinalForSmallObjectArgument κ :=
  adjointFamilyGenerators_isCardinalForSmallObjectArgument_of_equivalence
    e (fun _ : ℕ => Lₙ 0 ⋙ e.inverse) Lₙ (fun _ => 0) (fun _ => Iso.refl _)
    P κ hQₙ

end EmptyAndInfinite

section NonthinTypeCategory

variable (F : ℕ → Type u ⥤ Type u) (Pₙ : MorphismProperty (Type u))
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType] [Pₙ.IsSmall.{w}]
  (hF : (adjointFamilyGenerators F Pₙ).IsCardinalForSmallObjectArgument κ)

example : (adjointFamilyGenerators F Pₙ).IsCardinalForSmallObjectArgument κ :=
  adjointFamilyGenerators_isCardinalForSmallObjectArgument_of_equivalence
    (CategoryTheory.Equivalence.refl (C := Type u)) F F id
      (fun n => (Functor.rightUnitor (F n)).symm)
    Pₙ κ hF

example :
    (adjointFamilyGenerators F Pₙ).rlp =
      ((adjointFamilyGenerators F Pₙ).strictMap (𝟭 (Type u))).rlp :=
  adjointFamilyGenerators_rlp_eq_strictMap (CategoryTheory.Equivalence.refl (C := Type u))
    F F id Function.surjective_id (fun n => (Functor.rightUnitor (F n)).symm) Pₙ

end NonthinTypeCategory

section RaisedUniverses

variable {V' : Type (uV + 1)} [Category.{vV + 1} V']
  {C' : Type (uC + 1)} [Category.{vC + 1} C']
  {D' : Type (uD + 1)} [Category.{vD + 1} D']
  {S' : Type (uS + 1)} {A' : Type (uA + 1)}
  (e' : C' ≌ D') (K' : S' → V' ⥤ C') (L' : A' → V' ⥤ D') (j' : S' → A')
  (q' : ∀ s, K' s ≅ L' (j' s) ⋙ e'.inverse) (P' : MorphismProperty V')
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} S'] [P'.IsSmall.{w}]
  (hQ' : (adjointFamilyGenerators L' P').IsCardinalForSmallObjectArgument κ)

example : (adjointFamilyGenerators K' P').IsCardinalForSmallObjectArgument κ :=
  adjointFamilyGenerators_isCardinalForSmallObjectArgument_of_equivalence
    e' K' L' j' q' P' κ hQ'

example (hj' : Function.Surjective j') :
    (adjointFamilyGenerators K' P').isoClosure =
      ((adjointFamilyGenerators L' P').strictMap e'.inverse).isoClosure :=
  adjointFamilyGenerators_isoClosure_eq_strictMap e' K' L' j' hj' q' P'

end RaisedUniverses

end MathlibExtTest.AdjointFamilyEquivalence
