/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LogRootNativeCommutingSquares

/-!
# Actual finite-root composition across the original parameter equality

The target tests are actual objects of Over Z. Their equality is the
original scheme composite square, applied to the parameter map. The
finite composite functor uses the actual source finite functors followed
by native root reindexing along that equality, in the contravariant
direction. No independent parameter cast or comparison functor is chosen.

Source: Talpo--Vistoli, arXiv:1410.1164v2, Sections 3--6.
The finite-root line phase and infinite projection coherence remain
normalization conditions on the actual comparison cell.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LogRootFiniteCompositeCoordinates

open _root_.CategoryTheory _root_.Opposite _root_.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams KatoChartCoefficientModels
open DenominatorRootStacks FiniteRootTowers LogRootSourceModels
open LogRootCompositionModels CanonicalLogRootArrowModels
open EtaleMonoidInverseImage

variable [InverseImageTheory.{0}]
  {X Y Z : LogScheme.{0}} (f : EtaleLogSchemes.Hom X Y)
  (g : EtaleLogSchemes.Hom Y Z) (h : EtaleLogSchemes.Hom X Z)

omit [InverseImageTheory.{0}] in
/-- The source composite square on the actual parameter structure morphism. -/
theorem parameter_base_eq (S : OriginalSquare f g h) (T : Over X.scheme) :
    (T.hom ≫ f.map) ≫ g.map = T.hom ≫ h.map :=
  (Category.assoc T.hom f.map g.map).trans (congrArg (fun k => T.hom ≫ k) S.base)

omit [InverseImageTheory.{0}] in
/-- This orientation gives the arrow from the h-test to the f,g-test for reindexing. -/
theorem parameter_test_eq (S : OriginalSquare f g h) (T : Over X.scheme) :
    (Over.map h.map).obj T = (Over.map g.map).obj ((Over.map f.map).obj T) := by
  change Over.mk (T.hom ≫ h.map) = Over.mk ((T.hom ≫ f.map) ≫ g.map)
  exact congrArg (fun k : T.left ⟶ Z.scheme => Over.mk k)
    (parameter_base_eq f g h S T).symm

/-- The actual source test arrow used by native contravariant root pullback. -/
def parameterArrow (S : OriginalSquare f g h) (T : Over X.scheme) :
    (Over.map h.map).obj T ⟶ (Over.map g.map).obj ((Over.map f.map).obj T) :=
  eqToHom (parameter_test_eq f g h S T)

/-- The entire native target inverse-image functor is transported by the same base equality. -/
def targetMonoidCast (S : OriginalSquare f g h) (T : Over X.scheme) :
    monoidPullback (T.hom ≫ h.map) ≅ monoidPullback ((T.hom ≫ f.map) ≫ g.map) :=
  eqToIso (congrArg (fun k : T.left ⟶ Z.scheme => monoidPullback k)
    (parameter_base_eq f g h S T).symm)

variable (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
  (RX : RootRealization X D I) (RY : RootRealization Y D I) (RZ : RootRealization Z D I)
  (F : FiniteArrow I D f RX RY) (G : FiniteArrow I D g RY RZ)
  (H : FiniteArrow I D h RX RZ)

/-- Actual target DF structures are transported along the original equality of tests. -/
theorem target_df_heq (S : OriginalSquare f g h) (T : Over X.scheme) :
    HEq (pulledStructure I RZ.dictionary.df ((Over.map h.map).obj T))
      (pulledStructure I RZ.dictionary.df
        ((Over.map g.map).obj ((Over.map f.map).obj T))) :=
  Eq.rec (motive := fun Q _ => HEq
    (pulledStructure I RZ.dictionary.df ((Over.map h.map).obj T))
    (pulledStructure I RZ.dictionary.df Q)) HEq.rfl (parameter_test_eq f g h S T)

/-- The finite composite includes the actual native reindexing across that test equality. -/
def finiteCompositeFunctor (S : OriginalSquare f g h) (T : Over X.scheme) (n : Exponent) :
    (RX.finite n).stack.Fibre T ⥤ (RZ.finite n).stack.Fibre ((Over.map h.map).obj T) :=
  F.functor T n ⋙ G.functor ((Over.map f.map).obj T) n ⋙
    ((RZ.finite n).stack.toPseudofunctor.map
      (parameterArrow f g h S T).op.toLoc).toFunctor

/-- The comparison cell has these exact finite source and target functors. -/
abbrev FiniteComparison (S : OriginalSquare f g h) (T : Over X.scheme) (n : Exponent) :=
  H.functor T n ≅ finiteCompositeFunctor f g h I D RX RY RZ F G S T n

end MathlibExt.AlgebraicGeometry.LogRootFiniteCompositeCoordinates
