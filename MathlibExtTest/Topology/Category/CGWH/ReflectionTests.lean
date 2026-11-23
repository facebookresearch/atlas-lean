/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Reflection

/-!
# Tests for weak-Hausdorff reflection

These tests exercise the public reflection and quotient interfaces, their
universe polymorphism, and the defining representative and adjunction laws.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory

namespace MathlibExtTest.Topology.Category.CGWH.ReflectionTests

section PublicSurface

variable (X : CompactlyGenerated.{u, v})
  (Y : CGWH.{u, v}) (s : Setoid ↥X.toTop)

example : Prop := CGWH.closedEquivalenceRelation X s

example : {t : Setoid ↥X.toTop |
    CGWH.closedEquivalenceRelation X t} :=
  CGWH.smallestClosedEquivalenceRelation X

example : UWeakHausdorffSpace.{u} (Quotient s) ↔
    CGWH.closedEquivalenceRelation X s :=
  CGWH.quotient_isWeakHausdorff_iff_isClosed X s

example : UWeakHausdorffSpace.{u} X ↔
    IsClosed {p : ↥((X ⊗ X).toTop) |
      CartesianMonoidalCategory.fst X X p =
        CartesianMonoidalCategory.snd X X p} :=
  CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal X

example : CompactlyGenerated.{u, v} ⥤ CGWH.{u, v} :=
  CGWH.weakHausdorffification

example : CGWH.weakHausdorffification.{u, v} ⊣
    CGWH.cgwhToCompactlyGenerated.{u, v} :=
  CGWH.weakHausdorffificationAdjunction

example : (Functor.id (CompactlyGenerated.{u, v})) ⟶
    CGWH.weakHausdorffification ⋙ CGWH.cgwhToCompactlyGenerated :=
  CGWH.reflectionUnit

example : Function.Surjective (CGWH.reflectionUnit.app X) :=
  CGWH.reflectionUnit_surjective X

example : CGWH.weakHausdorffification.obj
    (CGWH.cgwhToCompactlyGenerated.obj Y) ≅ Y :=
  CGWH.reflectionCounitIso Y

example : IsHomeomorph (CGWH.reflectionUnit.app X) ↔
    UWeakHausdorffSpace.{u} X :=
  CGWH.reflectionUnit_isHomeomorph_iff X

end PublicSurface

section UniverseMatrix

#check CGWH.closedEquivalenceRelation.{0, 0}
#check CGWH.smallestClosedEquivalenceRelation.{0, 0}
#check CGWH.quotient_isWeakHausdorff_iff_isClosed.{0, 0}
#check CGWH.weakHausdorffification.{0, 0}
#check CGWH.weakHausdorffificationAdjunction.{0, 0}
#check CGWH.reflectionUnit.{0, 0}
#check CGWH.reflectionUnit_surjective.{0, 0}
#check CGWH.reflectionCounitIso.{0, 0}
#check CGWH.quotient.{0, 0}
#check CGWH.quotientComparisonFromTop.{0, 0}
#check CGWH.quotientHomEquiv.{0, 0}
#check CGWH.quotientHomEquiv_apply.{0, 0}
#check CGWH.quotientComparisonFromTop_isHomeomorph_iff.{0, 0}
#check CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal.{0, 0}
#check CGWH.reflectionUnit_isHomeomorph_iff.{0, 0}

#check CGWH.closedEquivalenceRelation.{1, 1}
#check CGWH.smallestClosedEquivalenceRelation.{1, 1}
#check CGWH.quotient_isWeakHausdorff_iff_isClosed.{1, 1}
#check CGWH.weakHausdorffification.{1, 1}
#check CGWH.weakHausdorffificationAdjunction.{1, 1}
#check CGWH.reflectionUnit.{1, 1}
#check CGWH.reflectionUnit_surjective.{1, 1}
#check CGWH.reflectionCounitIso.{1, 1}
#check CGWH.quotient.{1, 1}
#check CGWH.quotientComparisonFromTop.{1, 1}
#check CGWH.quotientHomEquiv.{1, 1}
#check CGWH.quotientHomEquiv_apply.{1, 1}
#check CGWH.quotientComparisonFromTop_isHomeomorph_iff.{1, 1}
#check CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal.{1, 1}
#check CGWH.reflectionUnit_isHomeomorph_iff.{1, 1}

#check CGWH.closedEquivalenceRelation.{0, 1}
#check CGWH.smallestClosedEquivalenceRelation.{0, 1}
#check CGWH.quotient_isWeakHausdorff_iff_isClosed.{0, 1}
#check CGWH.weakHausdorffification.{0, 1}
#check CGWH.weakHausdorffificationAdjunction.{0, 1}
#check CGWH.reflectionUnit.{0, 1}
#check CGWH.reflectionUnit_surjective.{0, 1}
#check CGWH.reflectionCounitIso.{0, 1}
#check CGWH.quotient.{0, 1}
#check CGWH.quotientComparisonFromTop.{0, 1}
#check CGWH.quotientHomEquiv.{0, 1}
#check CGWH.quotientHomEquiv_apply.{0, 1}
#check CGWH.quotientComparisonFromTop_isHomeomorph_iff.{0, 1}
#check CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal.{0, 1}
#check CGWH.reflectionUnit_isHomeomorph_iff.{0, 1}

#check CGWH.closedEquivalenceRelation.{u, v}
#check CGWH.smallestClosedEquivalenceRelation.{u, v}
#check CGWH.quotient_isWeakHausdorff_iff_isClosed.{u, v}
#check CGWH.weakHausdorffification.{u, v}
#check CGWH.weakHausdorffificationAdjunction.{u, v}
#check CGWH.reflectionUnit.{u, v}
#check CGWH.reflectionUnit_surjective.{u, v}
#check CGWH.reflectionCounitIso.{u, v}
#check CGWH.quotient.{u, v}
#check CGWH.quotientComparisonFromTop.{u, v}
#check CGWH.quotientHomEquiv.{u, v}
#check CGWH.quotientHomEquiv_apply.{u, v}
#check CGWH.quotientComparisonFromTop_isHomeomorph_iff.{u, v}
#check CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal.{u, v}
#check CGWH.reflectionUnit_isHomeomorph_iff.{u, v}

end UniverseMatrix

section NewMixedUniverseCorner

#check CGWH.quotientHomEquiv.{1, 0}
#check CGWH.quotientHomEquiv_apply.{1, 0}

end NewMixedUniverseCorner

section SmallestRelation

variable (X : CompactlyGenerated.{u, v}) (x y z : ↥X.toTop)

example : Setoid ↥X.toTop :=
  (CGWH.smallestClosedEquivalenceRelation X).1

example : CGWH.closedEquivalenceRelation X
    (CGWH.smallestClosedEquivalenceRelation X).1 :=
  (CGWH.smallestClosedEquivalenceRelation X).2

example : (CGWH.smallestClosedEquivalenceRelation X).1 x x :=
  (CGWH.smallestClosedEquivalenceRelation X).1.refl x

example (h : (CGWH.smallestClosedEquivalenceRelation X).1 x y) :
    (CGWH.smallestClosedEquivalenceRelation X).1 y x :=
  (CGWH.smallestClosedEquivalenceRelation X).1.symm h

example (hxy : (CGWH.smallestClosedEquivalenceRelation X).1 x y)
    (hyz : (CGWH.smallestClosedEquivalenceRelation X).1 y z) :
    (CGWH.smallestClosedEquivalenceRelation X).1 x z :=
  (CGWH.smallestClosedEquivalenceRelation X).1.trans hxy hyz

end SmallestRelation

section QuotientCriterion

variable (X : CompactlyGenerated.{u, v}) (s : Setoid ↥X.toTop)

example (h : UWeakHausdorffSpace.{u} (Quotient s)) :
    CGWH.closedEquivalenceRelation X s :=
  (CGWH.quotient_isWeakHausdorff_iff_isClosed X s).mp h

example (h : CGWH.closedEquivalenceRelation X s) :
    UWeakHausdorffSpace.{u} (Quotient s) :=
  (CGWH.quotient_isWeakHausdorff_iff_isClosed X s).mpr h

end QuotientCriterion

section CharacteristicCriteria

variable (X : CompactlyGenerated.{u, v})

example (h : UWeakHausdorffSpace.{u} X) :
    IsClosed {p : ↥((X ⊗ X).toTop) |
      CartesianMonoidalCategory.fst X X p =
        CartesianMonoidalCategory.snd X X p} :=
  (CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal X).mp h

example (h : IsClosed {p : ↥((X ⊗ X).toTop) |
    CartesianMonoidalCategory.fst X X p =
      CartesianMonoidalCategory.snd X X p}) :
    UWeakHausdorffSpace.{u} X :=
  (CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal X).mpr h

example (h : UWeakHausdorffSpace.{u} X) :
    IsHomeomorph (CGWH.reflectionUnit.app X) :=
  (CGWH.reflectionUnit_isHomeomorph_iff X).mpr h

example (h : ¬ UWeakHausdorffSpace.{u} X) :
    ¬ IsHomeomorph (CGWH.reflectionUnit.app X) :=
  fun hunit => h ((CGWH.reflectionUnit_isHomeomorph_iff X).mp hunit)

end CharacteristicCriteria

section FunctorAndAdjunction

variable {X Y Z : CompactlyGenerated.{u, v}}
  (f : X ⟶ Y) (g : Y ⟶ Z)

example : CGWH.weakHausdorffification.map (𝟙 X) =
    𝟙 (CGWH.weakHausdorffification.obj X) :=
  CGWH.weakHausdorffification.map_id X

example : CGWH.weakHausdorffification.map (f ≫ g) =
    CGWH.weakHausdorffification.map f ≫
      CGWH.weakHausdorffification.map g :=
  CGWH.weakHausdorffification.map_comp f g

example : CGWH.reflectionUnit.{u, v} =
    CGWH.weakHausdorffificationAdjunction.unit := rfl

example :
    CGWH.weakHausdorffification.map
          (CGWH.reflectionUnit.app X) ≫
        CGWH.weakHausdorffificationAdjunction.counit.app
          (CGWH.weakHausdorffification.obj X) =
      𝟙 (CGWH.weakHausdorffification.obj X) :=
  CGWH.weakHausdorffificationAdjunction.left_triangle_components X

variable (T : CGWH.{u, v})

example :
    CGWH.reflectionUnit.app
          (CGWH.cgwhToCompactlyGenerated.obj T) ≫
        CGWH.cgwhToCompactlyGenerated.map
          (CGWH.weakHausdorffificationAdjunction.counit.app T) =
      𝟙 (CGWH.cgwhToCompactlyGenerated.obj T) :=
  CGWH.weakHausdorffificationAdjunction.right_triangle_components T

example : (CGWH.reflectionCounitIso T).hom ≫
    (CGWH.reflectionCounitIso T).inv =
      𝟙 (CGWH.weakHausdorffification.obj
        (CGWH.cgwhToCompactlyGenerated.obj T)) :=
  (CGWH.reflectionCounitIso T).hom_inv_id

example : (CGWH.reflectionCounitIso T).inv ≫
    (CGWH.reflectionCounitIso T).hom = 𝟙 T :=
  (CGWH.reflectionCounitIso T).inv_hom_id

end FunctorAndAdjunction

section NativeQuotient

variable (X Y Z : CGWH.{u, v}) (s : Setoid ↥X.toTop)

example : CGWH.{u, v} := CGWH.quotient X s

example : TopCat.of (Quotient s) ⟶
    CGWH.cgwhToTop.obj (CGWH.quotient X s) :=
  CGWH.quotientComparisonFromTop X s

example : (CGWH.quotient X s ⟶ Y) ≃
    (TopCat.of (Quotient s) ⟶ CGWH.cgwhToTop.obj Y) :=
  CGWH.quotientHomEquiv X s Y

example (f : CGWH.quotient X s ⟶ Y) :
    CGWH.quotientHomEquiv X s Y f =
      CGWH.quotientComparisonFromTop X s ≫
        CGWH.cgwhToTop.map f :=
  CGWH.quotientHomEquiv_apply X s Y f

example : CGWH.quotientHomEquiv X s (CGWH.quotient X s)
      (𝟙 (CGWH.quotient X s)) =
    CGWH.quotientComparisonFromTop X s := by
  rw [CGWH.quotientHomEquiv_apply, CGWH.cgwhToTop.map_id,
    Category.comp_id]

example (f : CGWH.quotient X s ⟶ Y) (g : Y ⟶ Z) :
    CGWH.quotientHomEquiv X s Z (f ≫ g) =
      CGWH.quotientComparisonFromTop X s ≫
        CGWH.cgwhToTop.map f ≫ CGWH.cgwhToTop.map g := by
  simp only [CGWH.quotientHomEquiv_apply, Functor.map_comp]

example (f : CGWH.quotient X s ⟶ Y) :
    (CGWH.quotientHomEquiv X s Y).symm
        (CGWH.quotientHomEquiv X s Y f) = f :=
  (CGWH.quotientHomEquiv X s Y).symm_apply_apply f

example (f : TopCat.of (Quotient s) ⟶ CGWH.cgwhToTop.obj Y) :
    CGWH.quotientHomEquiv X s Y
        ((CGWH.quotientHomEquiv X s Y).symm f) = f :=
  (CGWH.quotientHomEquiv X s Y).apply_symm_apply f

example (rawDesc : TopCat.of (Quotient s) ⟶
    CGWH.cgwhToTop.obj Y) :
    CGWH.quotientComparisonFromTop X s ≫
        CGWH.cgwhToTop.map
          ((CGWH.quotientHomEquiv X s Y).symm rawDesc) =
      rawDesc := by
  rw [← CGWH.quotientHomEquiv_apply]
  exact (CGWH.quotientHomEquiv X s Y).apply_symm_apply rawDesc

example {f g : CGWH.quotient X s ⟶ Y}
    (h : CGWH.quotientComparisonFromTop X s ≫
          CGWH.cgwhToTop.map f =
        CGWH.quotientComparisonFromTop X s ≫
          CGWH.cgwhToTop.map g) : f = g := by
  apply (CGWH.quotientHomEquiv X s Y).injective
  simpa only [CGWH.quotientHomEquiv_apply] using h

example (q : TopCat.of X ⟶ TopCat.of (Quotient s))
    (f : CGWH.quotient X s ⟶ Y) :
    q ≫ CGWH.quotientHomEquiv X s Y f =
      q ≫ CGWH.quotientComparisonFromTop X s ≫
        CGWH.cgwhToTop.map f := by
  simp only [CGWH.quotientHomEquiv_apply]

example (h : IsHomeomorph (CGWH.quotientComparisonFromTop X s)) :
    CGWH.closedEquivalenceRelation
      (CGWH.cgwhToCompactlyGenerated.obj X) s :=
  (CGWH.quotientComparisonFromTop_isHomeomorph_iff X s).mp h

example (h : CGWH.closedEquivalenceRelation
    (CGWH.cgwhToCompactlyGenerated.obj X) s) :
    IsHomeomorph (CGWH.quotientComparisonFromTop X s) :=
  (CGWH.quotientComparisonFromTop_isHomeomorph_iff X s).mpr h

end NativeQuotient

section InstanceBoundary

example : Reflective CGWH.cgwhToCompactlyGenerated.{u, v} := inferInstance

example : True := by
  fail_if_success let _ : Reflective CGWH.cgwhToTop.{u, v} := inferInstance
  trivial

end InstanceBoundary

#print axioms CGWH.closedEquivalenceRelation
#print axioms CGWH.smallestClosedEquivalenceRelation
#print axioms CGWH.quotient_isWeakHausdorff_iff_isClosed
#print axioms CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal
#print axioms CGWH.reflectionUnit_isHomeomorph_iff
#print axioms CGWH.reflectionUnit_surjective
#print axioms CGWH.weakHausdorffificationAdjunction
#print axioms CGWH.quotientHomEquiv
#print axioms CGWH.quotientHomEquiv_apply
#print axioms CGWH.quotientComparisonFromTop_isHomeomorph_iff

end MathlibExtTest.Topology.Category.CGWH.ReflectionTests
