/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeSZeroFoldModels
public import MathlibExt.AlgebraicTopology.BGTVerdierQuotients
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# The full parameter action on the original S-construction

The parameter is the actual core of the full exact-functor category.
On every parameter simplex and every original multi-gap simplex its
action is native enriched composition. In particular the image of a
quotient-killing natural equivalence is a specified diagonal homotopy.
It cannot be replaced by an independently chosen nullhomotopy.

Sources: Waldhausen, *Algebraic K-theory of spaces*, Section 1.3;
Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Sections 7.1 and 9.1.
Native simplicial Hom composition is Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.StableInfinitySParametrizedAction

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityCategoryModels
open StableInfinityFiniteDiagrams StableInfinityMultiSConstruction
open StableInfinitySFunctorMaps NativeSZeroFoldModels BGTVerdierQuotients
open scoped Simplicial

universe u

/-- The actual full exact-functor core includes every higher natural equivalence. -/
abbrev ExactFunctorCore (C D : StableInfinityCategory.{u}) : SSet.{u} :=
  core (exactFunctorCategory C D)

/-- An actual exact functor determines its original full functor vertex. -/
def exactFunctorVertex {C D : StableInfinityCategory.{u}} (f : ExactFunctor C D) :
    (exactFunctorCategory C D) _⦋0⦌ :=
  ⟨mappingZero _ _ f.map,
    (SSet.mem_fullEnhancedSubcategory_obj_zero_iff _ _).mpr (by
      simpa only [IsExactVertex, Equiv.symm_apply_apply] using f.exact)⟩

/-- The vertex in the actual exact-functor core retains the original exact map. -/
def exactFunctorCoreVertex {C D : StableInfinityCategory.{u}} (f : ExactFunctor C D) :
    (ExactFunctorCore C D) _⦋0⦌ := coreVertex _ (exactFunctorVertex f)

/-- This generic source property concerns only the fixed constant zero functor. -/
structure ZeroExactFunctorSource (C D : StableInfinityCategory.{u}) : Prop where
  exact : IsExact C D (SSet.const D.zero)

/-- The source zero functor is the literal constant map at the original zero object. -/
def zeroExactFunctor {C D : StableInfinityCategory.{u}} (Z : ZeroExactFunctorSource C D) :
    ExactFunctor C D := ⟨SSet.const D.zero, Z.exact⟩

/-- The native source natural equivalence kills the actual composite quotient functor. -/
structure QuotientZeroPath (E : StableExactSequence.{u})
    (Z : ZeroExactFunctorSource E.left E.right) where
  path : (ExactFunctorCore E.left E.right) _⦋1⦌
  source : (ExactFunctorCore E.left E.right).δ 1 path =
    exactFunctorCoreVertex (E.inclusion.functor.comp E.quotientMap)
  target : (ExactFunctorCore E.left E.right).δ 0 path =
    exactFunctorCoreVertex (zeroExactFunctor Z)

/-- The reverse path has the source direction required by the actual rigid triangle. -/
structure QuotientZeroReversePath (E : StableExactSequence.{u})
    (Z : ZeroExactFunctorSource E.left E.right) where
  path : (ExactFunctorCore E.left E.right) _⦋1⦌
  source : (ExactFunctorCore E.left E.right).δ 1 path =
    exactFunctorCoreVertex (zeroExactFunctor Z)
  target : (ExactFunctorCore E.left E.right).δ 0 path =
    exactFunctorCoreVertex (E.inclusion.functor.comp E.quotientMap)

/-- The original enriched composition fixes every parameter and gap simplex. -/
structure FullSParameterAction (C D : StableInfinityCategory.{u}) where
  action : ∀ q : ℕ, multiSDiagonal C q ⊗ ExactFunctorCore C D ⟶ multiSDiagonal D q
  normalization : ∀ (q : ℕ) (r : SimplexCategoryᵒᵖ)
    (x : (multiSDiagonal C q).obj r) (f : (ExactFunctorCore C D).obj r),
    (((action q).app r (x, f)).val).val =
      (SimplicialCategory.sHomComp
        (indexNerve (MultiIntervalCategory q (fun _ => r.unop.len))) C.toSSet D.toSSet).app r
          (x.val.val, f.val.val)

/-- Native currying exposes the same complete parameter-to-diagonal Hom map. -/
def FullSParameterAction.parameterMap {C D : StableInfinityCategory.{u}}
    (A : FullSParameterAction C D) (q : ℕ) :
    ExactFunctorCore C D ⟶ mapping (multiSDiagonal C q) (multiSDiagonal D q) :=
  MonoidalClosed.curry (A.action q)

/-- The diagonal nullhomotopy is exactly the image of the original quotient-zero path. -/
def quotientDiagonalHomotopy {E : StableExactSequence.{u}}
    {Z : ZeroExactFunctorSource E.left E.right} (P : QuotientZeroPath E Z)
    (A : FullSParameterAction E.left E.right) (q : ℕ) :
    (mapping (multiSDiagonal E.left q) (multiSDiagonal E.right q)) _⦋1⦌ :=
  (A.parameterMap q).app (op ⦋1⦌) P.path

end MathlibExt.AlgebraicTopology.StableInfinitySParametrizedAction
