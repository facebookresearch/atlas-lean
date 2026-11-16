/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.BGTIndKappaModels

/-!
# Native exact-functor maps of Ind, F-kappa and Sigma-kappa

The Ind map is the filtered-colimit-preserving extension of the original
whole Yoneda functor map. The F-kappa map is its restriction to the
actual compact full categories and their small presentations. The
Sigma-kappa map is induced on the actual Verdier cofibers. All source
comparisons are full natural equivalences, retaining every parameter
arrow, and permit legitimate changes of small presentations.

Source: Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Sections 2.4
and 5.1, Definition 9.1 and Proposition 9.5.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.BGTIndSigmaFunctorMaps

open _root_.CategoryTheory
open StableInfinityCategoryModels StableInfinityFilteredColimits
open StableInfinityMappingSpaceMaps BGTIndKappaModels BGTVerdierQuotients
open scoped Cardinal

/-- The actual small compact-category comparison and native full inclusion. -/
def smallToInd {C : StableInfinityCategory.{0}}
    {k : UncountableRegularCardinal} (F : FKappaSource C k) :
    (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).obj F.small.toSSet ⟶ F.ind.toSSet :=
  F.small_comparison ≫ eqToHom F.compact_normalization ≫
    compactInclusion k.value F.ind

/-- The original Yoneda source into the actual Ind category. -/
def yonedaToInd {C : StableInfinityCategory.{0}}
    {k : UncountableRegularCardinal} (F : FKappaSource C k) :
    (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).obj C.toSSet ⟶ F.ind.toSSet :=
  (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).map F.inclusion.functor.map ≫ smallToInd F

/-- The actual filtered extension and compact restriction of the same exact functor. -/
structure FKappaFunctorMap {C D : StableInfinityCategory.{0}}
    {k : UncountableRegularCardinal} (F : FKappaSource C k) (G : FKappaSource D k)
    (f : ExactFunctor C D) where
  ind : ExactFunctor F.ind G.ind
  preserves_filtered : PreservesKappaFilteredColimits ℵ₀ ind.map
  yoneda_natural : NaturallyEquivalentMaps
    (yonedaToInd F ≫ ind.map)
    ((SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).map f.map ≫ yonedaToInd G)
  compact : ExactFunctor F.small G.small
  compact_natural : NaturallyEquivalentMaps
    ((SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).map compact.map ≫ smallToInd G)
    (smallToInd F ≫ ind.map)

/-- A map of actual exact sequences carries both native inclusion and quotient squares. -/
structure StableExactSequenceMap (E F : StableExactSequence.{0}) where
  left : ExactFunctor E.left F.left
  middle : ExactFunctor E.middle F.middle
  right : ExactFunctor E.right F.right
  inclusion_natural : NaturallyEquivalentMaps
    (E.inclusion.functor.map ≫ middle.map)
    (left.map ≫ F.inclusion.functor.map)
  quotient_natural : NaturallyEquivalentMaps
    (E.quotientMap.map ≫ right.map)
    (middle.map ≫ F.quotientMap.map)

/-- The actual induced map on the two source Verdier suspensions. -/
structure SigmaKappaFunctorMap {C D : StableInfinityCategory.{0}}
    {k : UncountableRegularCardinal} (S : SigmaKappaSource C k) (T : SigmaKappaSource D k)
    (f : ExactFunctor C D) where
  cone : FKappaFunctorMap S.cone T.cone f
  functor : ExactFunctor (sigmaCategory S) (sigmaCategory T)
  inclusion_natural : NaturallyEquivalentMaps
    (S.cone.inclusion.functor.map ≫ cone.compact.map)
    (f.map ≫ T.cone.inclusion.functor.map)
  quotient_natural : NaturallyEquivalentMaps
    (S.quotient.quotient.map ≫ functor.map)
    (cone.compact.map ≫ T.quotient.quotient.map)

/-- These are the original object and functor maps of the native suspension exact sequences. -/
def SigmaKappaFunctorMap.exactSequenceMap {C D : StableInfinityCategory.{0}}
    {k : UncountableRegularCardinal} {S : SigmaKappaSource C k} {T : SigmaKappaSource D k}
    {f : ExactFunctor C D} (M : SigmaKappaFunctorMap S T f) :
    StableExactSequenceMap S.exactSequence T.exactSequence :=
  ⟨f, M.cone.compact, M.functor, M.inclusion_natural, M.quotient_natural⟩

end MathlibExt.AlgebraicTopology.BGTIndSigmaFunctorMaps
