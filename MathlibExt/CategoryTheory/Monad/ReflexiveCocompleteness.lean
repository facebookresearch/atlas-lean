/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monad.Coequalizer
public import Mathlib.CategoryTheory.Monad.Limits

/-!
# Cocompleteness from reflexive algebra coequalizers

For an arbitrary monad on a cocomplete category, the colimit of an algebra
diagram is constructed from a reflexive pair of free objects. The two source
objects are the original colimits of its underlying diagram and its monad
image. The common section is induced by the original unit. The Beck
presentations of the original algebras supply the resulting cocone and its
universal property.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe v u vJ uJ vD uD

open CategoryTheory Limits

namespace CategoryTheory.Monad.ReflexiveCocompleteness

variable {C : Type u} [Category.{v} C] (T : Monad C)
  {J : Type uJ} [Category.{vJ} J] [HasColimitsOfShape J C]
  (K : J ⥤ Algebra T)

local instance : T.free.IsLeftAdjoint := ⟨T.forget, ⟨T.adj⟩⟩

/-- The original algebra diagram followed by its actual forgetful functor. -/
abbrev underlyingDiagram : J ⥤ C := K ⋙ T.forget

/-- The original monad image of the underlying diagram. -/
abbrev relationDiagram : J ⥤ C := underlyingDiagram T K ⋙ (T : C ⥤ C)

/-- Applying the actual free adjoint keeps the given source colimit cocone. -/
def freeSourceIsColimit (H : J ⥤ C) :
    IsColimit (T.free.mapCocone (colimit.cocone H)) :=
  isColimitOfPreserves T.free (colimit.isColimit H)

/-- The first relation cocone is induced by each original algebra action. -/
def upperCocone : Cocone (relationDiagram T K ⋙ T.free) where
  pt := T.free.obj (colimit (underlyingDiagram T K))
  ι :=
    { app j := FreeCoequalizer.topMap (K.obj j) ≫
        T.free.map (colimit.ι (underlyingDiagram T K) j)
      naturality {j k} f := by
        have h : T.map (K.map f).f ≫ (K.obj k).a ≫
            colimit.ι (underlyingDiagram T K) k =
            (K.obj j).a ≫ colimit.ι (underlyingDiagram T K) j := by
          rw [← Category.assoc, (K.map f).h, Category.assoc]
          congr 1
          exact colimit.w (underlyingDiagram T K) f
        change T.free.map (T.map (K.map f).f) ≫ T.free.map (K.obj k).a ≫
            T.free.map (colimit.ι (underlyingDiagram T K) k) =
          (T.free.map (K.obj j).a ≫ T.free.map (colimit.ι (underlyingDiagram T K) j)) ≫ 𝟙 _
        rw [Category.comp_id]
        simpa only [Functor.map_comp, Category.assoc] using congrArg T.free.map h }

/-- The second relation cocone is induced by the original free counits. -/
def lowerCocone : Cocone (relationDiagram T K ⋙ T.free) where
  pt := T.free.obj (colimit (underlyingDiagram T K))
  ι :=
    { app j := FreeCoequalizer.bottomMap (K.obj j) ≫
        T.free.map (colimit.ι (underlyingDiagram T K) j)
      naturality {j k} f := by
        apply Algebra.Hom.ext
        change T.map (T.map (K.map f).f) ≫ T.μ.app (K.obj k).A ≫
          T.map (colimit.ι (underlyingDiagram T K) k) =
            (T.μ.app (K.obj j).A ≫ T.map (colimit.ι (underlyingDiagram T K) j)) ≫ 𝟙 _
        have hn : T.map (T.map (K.map f).f) ≫ T.μ.app (K.obj k).A =
            T.μ.app (K.obj j).A ≫ T.map (K.map f).f := by
          simpa only [Functor.comp_map] using T.μ.naturality (K.map f).f
        rw [Category.comp_id, ← Category.assoc, hn, Category.assoc, ← T.map_comp]
        exact congrArg (fun q => T.μ.app (K.obj j).A ≫ T.map q)
          (colimit.w (underlyingDiagram T K) f) }

/-- The action relation between the original two free source colimit objects. -/
def upperRelation : T.free.obj (colimit (relationDiagram T K)) ⟶
    T.free.obj (colimit (underlyingDiagram T K)) :=
  (freeSourceIsColimit T (relationDiagram T K)).desc (upperCocone T K)

/-- The multiplication relation between those same original free objects. -/
def lowerRelation : T.free.obj (colimit (relationDiagram T K)) ⟶
    T.free.obj (colimit (underlyingDiagram T K)) :=
  (freeSourceIsColimit T (relationDiagram T K)).desc (lowerCocone T K)

/-- The original unit is a transformation of the complete underlying diagram. -/
def unitDiagram : underlyingDiagram T K ⟶ relationDiagram T K where
  app j := T.η.app (K.obj j).A
  naturality {_ _} f := T.η.naturality (K.map f).f

/-- The common section is the actual free image of the unit-induced colimit map. -/
def relationSection : T.free.obj (colimit (underlyingDiagram T K)) ⟶
    T.free.obj (colimit (relationDiagram T K)) :=
  T.free.map (colimMap (unitDiagram T K))

/-- Every original relation leg evaluates the first chosen colimit descent. -/
theorem upperRelation_ι (j : J) :
    T.free.map (colimit.ι (relationDiagram T K) j) ≫ upperRelation T K =
      FreeCoequalizer.topMap (K.obj j) ≫
        T.free.map (colimit.ι (underlyingDiagram T K) j) :=
  (freeSourceIsColimit T (relationDiagram T K)).fac (upperCocone T K) j

/-- Every original relation leg evaluates the second chosen colimit descent. -/
theorem lowerRelation_ι (j : J) :
    T.free.map (colimit.ι (relationDiagram T K) j) ≫ lowerRelation T K =
      FreeCoequalizer.bottomMap (K.obj j) ≫
        T.free.map (colimit.ι (underlyingDiagram T K) j) :=
  (freeSourceIsColimit T (relationDiagram T K)).fac (lowerCocone T K) j

/-- The original unit is a section of the action relation. -/
theorem relationSection_upper : relationSection T K ≫ upperRelation T K = 𝟙 _ := by
  apply (freeSourceIsColimit T (underlyingDiagram T K)).hom_ext
  intro j
  change T.free.map (colimit.ι (underlyingDiagram T K) j) ≫
      relationSection T K ≫ upperRelation T K =
        T.free.map (colimit.ι (underlyingDiagram T K) j) ≫ 𝟙 _
  rw [Category.comp_id]
  rw [← Category.assoc, relationSection, ← T.free.map_comp, ι_colimMap, T.free.map_comp,
    Category.assoc, upperRelation_ι]
  change T.free.map (T.η.app (K.obj j).A) ≫
      T.free.map (K.obj j).a ≫ T.free.map (colimit.ι (underlyingDiagram T K) j) = _
  rw [← Category.assoc, ← T.free.map_comp, (K.obj j).unit]
  rw [T.free.map_id (K.obj j).A]
  exact Category.id_comp (T.free.map (colimit.ι (underlyingDiagram T K) j))

/-- The original unit is also a section of the multiplication relation. -/
theorem relationSection_lower : relationSection T K ≫ lowerRelation T K = 𝟙 _ := by
  apply (freeSourceIsColimit T (underlyingDiagram T K)).hom_ext
  intro j
  change T.free.map (colimit.ι (underlyingDiagram T K) j) ≫
      relationSection T K ≫ lowerRelation T K =
        T.free.map (colimit.ι (underlyingDiagram T K) j) ≫ 𝟙 _
  rw [Category.comp_id]
  rw [← Category.assoc, relationSection, ← T.free.map_comp, ι_colimMap, T.free.map_comp,
    Category.assoc, lowerRelation_ι]
  have hs : T.free.map (T.η.app (K.obj j).A) ≫
      FreeCoequalizer.bottomMap (K.obj j) = 𝟙 _ := by
    apply Algebra.Hom.ext
    exact T.right_unit (K.obj j).A
  change T.free.map (T.η.app (K.obj j).A) ≫
      FreeCoequalizer.bottomMap (K.obj j) ≫
        T.free.map (colimit.ι (underlyingDiagram T K) j) = _
  rw [← Category.assoc, hs]
  simp

/-- The two free relation objects have the original unit-induced common section. -/
instance relationPair_reflexive : IsReflexivePair (upperRelation T K) (lowerRelation T K) :=
  IsReflexivePair.mk' (relationSection T K) (relationSection_upper T K) (relationSection_lower T K)

variable [HasReflexiveCoequalizers (Algebra T)]

/-- The candidate colimit is the actual coequalizer of the two free relations. -/
abbrev colimitObject : Algebra T := coequalizer (upperRelation T K) (lowerRelation T K)

/-- The quotient retains the original free source colimit object. -/
abbrev quotientMap : T.free.obj (colimit (underlyingDiagram T K)) ⟶ colimitObject T K :=
  coequalizer.π (upperRelation T K) (lowerRelation T K)

/-- Every original free component equalizes its original algebra presentation. -/
theorem originalLeg_condition (j : J) :
    FreeCoequalizer.topMap (K.obj j) ≫
        T.free.map (colimit.ι (underlyingDiagram T K) j) ≫ quotientMap T K =
      FreeCoequalizer.bottomMap (K.obj j) ≫
        T.free.map (colimit.ι (underlyingDiagram T K) j) ≫ quotientMap T K := by
  calc
    _ = (T.free.map (colimit.ι (relationDiagram T K) j) ≫ upperRelation T K) ≫
        quotientMap T K := by rw [upperRelation_ι, Category.assoc]
    _ = T.free.map (colimit.ι (relationDiagram T K) j) ≫
        lowerRelation T K ≫ quotientMap T K := by
      rw [Category.assoc, quotientMap, coequalizer.condition]
    _ = _ := by rw [← Category.assoc, lowerRelation_ι, Category.assoc]

/-- Descend the original Beck presentation to obtain this component of the colimit cocone. -/
def presentationLeg (j : J) : K.obj j ⟶ colimitObject T K :=
  Cofork.IsColimit.desc (beckAlgebraCoequalizer (K.obj j))
    (T.free.map (colimit.ι (underlyingDiagram T K) j) ≫ quotientMap T K)
    (originalLeg_condition T K j)

/-- The new leg retains the exact original algebra counit and free source inclusion. -/
theorem presentationLeg_π (j : J) :
    FreeCoequalizer.π (K.obj j) ≫ presentationLeg T K j =
      T.free.map (colimit.ι (underlyingDiagram T K) j) ≫ quotientMap T K :=
  Cofork.IsColimit.π_desc' (beckAlgebraCoequalizer (K.obj j)) _ (originalLeg_condition T K j)

omit [HasColimitsOfShape J C] [HasReflexiveCoequalizers (Algebra T)] in
/-- The original Beck projection is natural for the actual algebra maps. -/
theorem presentation_naturality {X Y : Algebra T} (f : X ⟶ Y) :
    T.free.map f.f ≫ FreeCoequalizer.π Y = FreeCoequalizer.π X ≫ f := by
  apply Algebra.Hom.ext
  exact f.h

/-- The original component Beck descents form a cocone on the unchanged algebra diagram. -/
def colimitCocone : Cocone K where
  pt := colimitObject T K
  ι :=
    { app j := presentationLeg T K j
      naturality {j k} f := by
        change K.map f ≫ presentationLeg T K k = presentationLeg T K j ≫ 𝟙 _
        rw [Category.comp_id]
        apply Cofork.IsColimit.hom_ext (beckAlgebraCoequalizer (K.obj j))
        change FreeCoequalizer.π (K.obj j) ≫ (K.map f ≫ presentationLeg T K k) =
          FreeCoequalizer.π (K.obj j) ≫ presentationLeg T K j
        rw [← Category.assoc, ← presentation_naturality, Category.assoc,
          presentationLeg_π, presentationLeg_π, ← Category.assoc, ← T.free.map_comp]
        exact congrArg (fun q => T.free.map q ≫ quotientMap T K)
          (colimit.w (underlyingDiagram T K) f) }

/-- Each original algebra cocone induces the corresponding free-source cocone. -/
def freeCocone (c : Cocone K) : Cocone (underlyingDiagram T K ⋙ T.free) where
  pt := c.pt
  ι :=
    { app j := FreeCoequalizer.π (K.obj j) ≫ c.ι.app j
      naturality {j k} f := by
        change T.free.map (K.map f).f ≫ (FreeCoequalizer.π (K.obj k) ≫ c.ι.app k) =
          (FreeCoequalizer.π (K.obj j) ≫ c.ι.app j) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, presentation_naturality, Category.assoc]
        exact congrArg (fun q => FreeCoequalizer.π (K.obj j) ≫ q) (c.w f) }

/-- The original free source colimit descends to the point of any original algebra cocone. -/
def freeDesc (c : Cocone K) : T.free.obj (colimit (underlyingDiagram T K)) ⟶ c.pt :=
  (freeSourceIsColimit T (underlyingDiagram T K)).desc (freeCocone T K c)

omit [HasReflexiveCoequalizers (Algebra T)] in
/-- This free descent agrees with the original algebra counit on every original source leg. -/
theorem freeDesc_ι (c : Cocone K) (j : J) :
    T.free.map (colimit.ι (underlyingDiagram T K) j) ≫ freeDesc T K c =
      FreeCoequalizer.π (K.obj j) ≫ c.ι.app j :=
  (freeSourceIsColimit T (underlyingDiagram T K)).fac (freeCocone T K c) j

omit [HasReflexiveCoequalizers (Algebra T)] in
/-- The actual free descent equalizes both original relation maps. -/
theorem freeDesc_condition (c : Cocone K) :
    upperRelation T K ≫ freeDesc T K c = lowerRelation T K ≫ freeDesc T K c := by
  apply (freeSourceIsColimit T (relationDiagram T K)).hom_ext
  intro j
  change T.free.map (colimit.ι (relationDiagram T K) j) ≫
      (upperRelation T K ≫ freeDesc T K c) =
    T.free.map (colimit.ι (relationDiagram T K) j) ≫
      (lowerRelation T K ≫ freeDesc T K c)
  calc
    _ = FreeCoequalizer.topMap (K.obj j) ≫
        T.free.map (colimit.ι (underlyingDiagram T K) j) ≫ freeDesc T K c := by
      rw [← Category.assoc, upperRelation_ι, Category.assoc]
    _ = FreeCoequalizer.topMap (K.obj j) ≫ FreeCoequalizer.π (K.obj j) ≫ c.ι.app j := by
      rw [freeDesc_ι]
    _ = FreeCoequalizer.bottomMap (K.obj j) ≫ FreeCoequalizer.π (K.obj j) ≫ c.ι.app j := by
      rw [← Category.assoc, FreeCoequalizer.condition, Category.assoc]
    _ = _ := by
      simpa only [Category.assoc, freeDesc_ι] using
        congrArg (fun q => q ≫ freeDesc T K c) (lowerRelation_ι T K j).symm

/-- Let `T` be a monad on `C` and let `C` have colimits of shape `J`.
If `Algebra T` has reflexive coequalizers, the constructed cocone on
`K : J ⥤ Algebra T` is a colimit cocone. -/
def colimitCoconeIsColimit : IsColimit (colimitCocone T K) where
  desc c := coequalizer.desc (freeDesc T K c) (freeDesc_condition T K c)
  fac c j := by
    apply Cofork.IsColimit.hom_ext (beckAlgebraCoequalizer (K.obj j))
    change FreeCoequalizer.π (K.obj j) ≫
        (presentationLeg T K j ≫ coequalizer.desc (freeDesc T K c) (freeDesc_condition T K c)) =
      FreeCoequalizer.π (K.obj j) ≫ c.ι.app j
    rw [← Category.assoc, presentationLeg_π, Category.assoc, quotientMap, coequalizer.π_desc]
    exact freeDesc_ι T K c j
  uniq c m hm := by
    apply coequalizer.hom_ext
    change quotientMap T K ≫ m =
      quotientMap T K ≫ coequalizer.desc (freeDesc T K c) (freeDesc_condition T K c)
    rw [quotientMap, coequalizer.π_desc]
    apply (freeSourceIsColimit T (underlyingDiagram T K)).hom_ext
    intro j
    change T.free.map (colimit.ι (underlyingDiagram T K) j) ≫
        (quotientMap T K ≫ m) =
      T.free.map (colimit.ι (underlyingDiagram T K) j) ≫ freeDesc T K c
    rw [← Category.assoc, ← presentationLeg_π, Category.assoc]
    have hj : presentationLeg T K j ≫ m = c.ι.app j := hm j
    rw [hj]
    exact (freeDesc_ι T K c j).symm

/-- Let `T` be a monad on `C`. If `C` has colimits of shape `J` and
`Algebra T` has reflexive coequalizers, then `Algebra T` has colimits of shape `J`. -/
theorem hasColimitsOfShape : HasColimitsOfShape J (Algebra T) :=
  ⟨fun K => HasColimit.mk
    { cocone := colimitCocone T K
      isColimit := colimitCoconeIsColimit T K }⟩

end CategoryTheory.Monad.ReflexiveCocompleteness

namespace CategoryTheory.Monad.ReflexiveCocompleteness

variable {C : Type u} [Category.{v} C] (T : Monad C)
  [HasColimitsOfSize.{vJ, uJ} C] [HasReflexiveCoequalizers (Algebra T)]

/-- Let `T` be a monad on `C`. If `C` has colimits of size `.{vJ, uJ}` and
`Algebra T` has reflexive coequalizers, then `Algebra T` has colimits of that size. -/
theorem hasColimitsOfSize : HasColimitsOfSize.{vJ, uJ} (Algebra T) :=
  ⟨fun J _ => hasColimitsOfShape T (J := J)⟩

end CategoryTheory.Monad.ReflexiveCocompleteness

namespace CategoryTheory.Monad.ReflexiveCocompleteness

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  {J : Type uJ} [Category.{vJ} J] [HasColimitsOfShape J C]
  (U : D ⥤ C) [MonadicRightAdjoint U] [HasReflexiveCoequalizers D]

include U in
/-- Suppose `U : D ⥤ C` is a monadic right adjoint, `C` has colimits of shape `J`,
and `D` has reflexive coequalizers. Then `D` has colimits of shape `J`. -/
theorem hasColimitsOfShapeOfMonadic : HasColimitsOfShape J D := by
  let E := comparison (monadicAdjunction U)
  let : HasColimitsOfShape WalkingReflexivePair D :=
    hasReflexiveCoequalizers_iff.mpr inferInstance
  let : HasColimitsOfShape WalkingReflexivePair (Algebra (monadicAdjunction U).toMonad) :=
    Adjunction.hasColimitsOfShape_of_equivalence E.inv
  let : HasReflexiveCoequalizers (Algebra (monadicAdjunction U).toMonad) :=
    hasReflexiveCoequalizers_iff.mp inferInstance
  let : HasColimitsOfShape J (Algebra (monadicAdjunction U).toMonad) :=
    hasColimitsOfShape (monadicAdjunction U).toMonad
  exact Adjunction.hasColimitsOfShape_of_equivalence E

end CategoryTheory.Monad.ReflexiveCocompleteness

namespace CategoryTheory.Monad.ReflexiveCocompleteness

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  [HasColimitsOfSize.{vJ, uJ} C]
  (U : D ⥤ C) [MonadicRightAdjoint U] [HasReflexiveCoequalizers D]

include U in
/-- Suppose `U : D ⥤ C` is a monadic right adjoint, `C` has colimits of size
`.{vJ, uJ}`, and `D` has reflexive coequalizers. Then `D` has colimits of that size. -/
theorem hasColimitsOfSizeOfMonadic : HasColimitsOfSize.{vJ, uJ} D :=
  ⟨fun J _ => hasColimitsOfShapeOfMonadic U (J := J)⟩

end CategoryTheory.Monad.ReflexiveCocompleteness

namespace CategoryTheory.Monad.ReflexiveCocompleteness

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  {J : Type uJ} [Category.{vJ} J] [HasColimitsOfShape J C]
  (F : C ⥤ D) (U : D ⥤ C) (adj : F ⊣ U)
  [(comparison adj).IsEquivalence] [HasReflexiveCoequalizers D]

include F U adj in
/-- Let `adj : F ⊣ U` for `F : C ⥤ D` and `U : D ⥤ C`, with `comparison adj`
an equivalence. If `C` has colimits of shape `J` and `D` has reflexive
coequalizers, then `D` has colimits of shape `J`. -/
theorem hasColimitsOfShapeOfAdjunction : HasColimitsOfShape J D := by
  let : MonadicRightAdjoint U := { L := F, adj := adj, eqv := inferInstance }
  exact hasColimitsOfShapeOfMonadic U

end CategoryTheory.Monad.ReflexiveCocompleteness

namespace CategoryTheory.Monad.ReflexiveCocompleteness

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  [HasColimitsOfSize.{vJ, uJ} C]
  (F : C ⥤ D) (U : D ⥤ C) (adj : F ⊣ U)
  [(comparison adj).IsEquivalence] [HasReflexiveCoequalizers D]

include F U adj in
/-- Let `adj : F ⊣ U` for `F : C ⥤ D` and `U : D ⥤ C`, with `comparison adj`
an equivalence. If `C` has colimits of size `.{vJ, uJ}` and `D` has reflexive
coequalizers, then `D` has colimits of that size. -/
theorem hasColimitsOfSizeOfAdjunction : HasColimitsOfSize.{vJ, uJ} D :=
  ⟨fun J _ => hasColimitsOfShapeOfAdjunction F U adj (J := J)⟩

end CategoryTheory.Monad.ReflexiveCocompleteness
