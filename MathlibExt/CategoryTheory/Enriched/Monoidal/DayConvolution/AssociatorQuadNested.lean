/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorQuadFlat
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorQuadLeft
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorFunctor

/-!
# Associator Quad Nested

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed
namespace CategoryTheory.EnrichedDayKernel.AssociatorQuadNested
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed
  V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I)
attribute [local instance] Enriched.prodCategory
variable
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.objects
    d.tensorEnrichedFunctor F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.relations
    d.tensorEnrichedFunctor F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoequalizer (EnrichedDayKernel.leftMap
    d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
variable (F G H J : EnrichedFunctor V I V) (m : I)
/-- The chosen enriched Day convolution of two original input functors. -/
abbrev day (F G : EnrichedFunctor V I V) := Output.functor d.tensorEnrichedFunctor F G
/-- The value at `m` of the nested Day product `((F ⋆ G) ⋆ H) ⋆ J`. -/
abbrev valueA : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor (day d (day d F G) H) J m
/-- The value at `m` of the nested Day product `(F ⋆ G) ⋆ (H ⋆ J)`. -/
abbrev valueB : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor (day d F G) (day d H J) m
/-- The value at `m` of the nested Day product `F ⋆ (G ⋆ (H ⋆ J))`. -/
abbrev valueC : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor F (day d G (day d H J)) m
/-- The value at `m` of the nested Day product `(F ⋆ (G ⋆ H)) ⋆ J`. -/
abbrev valueD : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor (day d F (day d G H)) J m
/-- The value at `m` of the nested Day product `F ⋆ ((G ⋆ H) ⋆ J)`. -/
abbrev valueE : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor F (day d (day d G H) J) m

/-- The original primitive fully-left four-input generator, with its actual dense chosen coend
  source. -/
abbrev genA (X : ((I × I) × I) × I) : AssociatorQuadFlat.objects d F G H J m .a X ⟶ valueA d F G H J
  m :=
  AssociatorQuadLeft.nestedGenerator d F G H J m X

/-- The balanced-middle primitive generator inserts only the original first and last pair
  identities. -/
abbrev genB (X : ((I × I) × I) × I) : AssociatorQuadFlat.objects d F G H J m .b X ⟶ valueB d F G H J
  m :=
  (𝟙 ((AssociatorQuadIndex.indexB d).obj X ⟶[V] m) ⊗ₘ
    (AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G X.1.1 ⊗ₘ
      AssociatorUnit.unitGenerator d.tensorEnrichedFunctor H J (X.1.2, X.2))) ≫
    EnrichedDayKernel.gen d.tensorEnrichedFunctor (day d F G) (day d H J) m
      (X.1.1.1 ⊗ X.1.1.2, X.1.2 ⊗ X.2)

/-- The original right-nested triple identity word keeps the second and final pair insertions. -/
abbrev rightTripleUnit (F G H : EnrichedFunctor V I V) (X : (I × I) × I) :
    F.obj X.1.1 ⊗ (G.obj X.1.2 ⊗ H.obj X.2) ⟶ (day d F (day d G H)).obj (X.1.1 ⊗ (X.1.2 ⊗ X.2)) :=
  (𝟙 (F.obj X.1.1) ⊗ₘ AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G H (X.1.2, X.2)) ≫
    AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F (day d G H) (X.1.1, X.1.2 ⊗ X.2)

/-- The original primitive fully-right four-input generator on the same ordered inputs and output.
-/
abbrev genC (X : ((I × I) × I) × I) : AssociatorQuadFlat.objects d F G H J m .c X ⟶ valueC d F G H J
  m :=
  (𝟙 ((AssociatorQuadIndex.indexC d).obj X ⟶[V] m) ⊗ₘ
    (𝟙 (F.obj X.1.1.1) ⊗ₘ rightTripleUnit d G H J ((X.1.1.2, X.1.2), X.2))) ≫
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F (day d G (day d H J)) m
      (X.1.1.1, X.1.1.2 ⊗ (X.1.2 ⊗ X.2))

/-- The primitive D generator inserts the actual right first-three unit word into the last pair
  kernel. -/
abbrev genD (X : ((I × I) × I) × I) : AssociatorQuadFlat.objects d F G H J m .d X ⟶ valueD d F G H J
  m :=
  (𝟙 ((AssociatorQuadIndex.indexD d).obj X ⟶[V] m) ⊗ₘ
    (rightTripleUnit d F G H X.1 ⊗ₘ 𝟙 (J.obj X.2))) ≫
    EnrichedDayKernel.gen d.tensorEnrichedFunctor (day d F (day d G H)) J m
      (X.1.1.1 ⊗ (X.1.1.2 ⊗ X.1.2), X.2)

/-- The primitive E generator inserts the actual left final-three unit word into the first pair
  kernel. -/
abbrev genE (X : ((I × I) × I) × I) : AssociatorQuadFlat.objects d F G H J m .e X ⟶ valueE d F G H J
  m :=
  (𝟙 ((AssociatorQuadIndex.indexE d).obj X ⟶[V] m) ⊗ₘ
    (𝟙 (F.obj X.1.1.1) ⊗ₘ AssociatorQuadLeft.tripleUnitGenerator d G H J ((X.1.1.2, X.1.2), X.2))) ≫
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F (day d (day d G H) J) m
      (X.1.1.1, (X.1.1.2 ⊗ X.1.2) ⊗ X.2)

end CategoryTheory.EnrichedDayKernel.AssociatorQuadNested
