/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreBifunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.FunEquivalenceYoneda

/-!
# Homotopy invariance of the full functor core in both variables

Source restriction uses the entire original simplicial source. A categorical
equivalence of sources gives a categorical equivalence of full functor objects
at a quasicategory target and a realization weak equivalence of their cores.
The source and target changes retain their original commuting square.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed

namespace SSet.FunctorCore

/-- Source restriction is a categorical equivalence at every quasicategory target,
without a quasicategory hypothesis on either source. -/
theorem precomposition_categoricalEquivalence {K L : SSet.{u}} (a : K ⟶ L)
    (ha : categoricalEquivalences a) (X : SSet.{u}) [Quasicategory X] :
    categoricalEquivalences ((pre a).app X) :=
  (ha.functorEquivalence_of_mem X).categoricalEquivalences

/-- The actual full functor-core source map is structurally Kan weak. -/
theorem sourceMap_weak {K L : SSet.{u}} (a : K ⟶ L)
    (ha : categoricalEquivalences a) (X : SSet.{u}) [Quasicategory X] :
    KanComplex.W ((sourceMap a).app X) := by
  change KanComplex.W (core.map ((pre a).app X))
  exact core_map_mem_W_of_categoricalEquivalence
    (precomposition_categoricalEquivalence a ha X)

/-- Source restriction retains its literal map in the global realization weak class. -/
theorem sourceMap_realizationWeak {K L : SSet.{u}} (a : K ⟶ L)
    (ha : categoricalEquivalences a) (X : SSet.{u}) [Quasicategory X] :
    realizationWeakEquivalences ((sourceMap a).app X) := by
  let _ : KanComplex ((functor L).obj X) := isKan L X
  let _ : KanComplex ((functor K).obj X) := isKan K X
  exact (KanComplex.W_iff_realizationWeakEquivalence _).mp (sourceMap_weak a ha X)

/-- Change the source and target through their original full functor-core maps. -/
def mapBoth {K L X Y : SSet.{u}} (a : K ⟶ L) (f : X ⟶ Y) :
    (functor L).obj X ⟶ (functor K).obj Y :=
  (sourceMap a).app X ≫ (functor K).map f

/-- The same simultaneous change also retains the opposite order of the two actions. -/
theorem mapBoth_target_source {K L X Y : SSet.{u}} (a : K ⟶ L) (f : X ⟶ Y) :
    mapBoth a f = (functor L).map f ≫ (sourceMap a).app Y :=
  ((sourceMap a).naturality f).symm

/-- Both actual identity changes are the identity on the full functor core. -/
theorem mapBoth_id (K X : SSet.{u}) : mapBoth (𝟙 K) (𝟙 X) = 𝟙 ((functor K).obj X) := by
  simp only [mapBoth, sourceMap_id, NatTrans.id_app, Category.id_comp]
  exact (functor K).map_id X

/-- Simultaneous categorical equivalences act weakly on the entire original functor core. -/
theorem mapBoth_realizationWeak {K L X Y : SSet.{u}}
    (a : K ⟶ L) (f : X ⟶ Y) (ha : categoricalEquivalences a)
    (hf : categoricalEquivalences f) [Quasicategory X] [Quasicategory Y] :
    realizationWeakEquivalences (mapBoth a f) := by
  let _ : KanComplex ((functor K).obj X) := isKan K X
  let _ : KanComplex ((functor K).obj Y) := isKan K Y
  exact realizationWeakEquivalences.comp_mem _ _ (sourceMap_realizationWeak a ha X)
    ((KanComplex.W_iff_realizationWeakEquivalence _).mp (map_weak f hf K))

/-- The same simultaneous comparison is a structural Kan weak equivalence. -/
theorem mapBoth_weak {K L X Y : SSet.{u}}
    (a : K ⟶ L) (f : X ⟶ Y) (ha : categoricalEquivalences a)
    (hf : categoricalEquivalences f) [Quasicategory X] [Quasicategory Y] :
    KanComplex.W (mapBoth a f) := by
  let _ : KanComplex ((functor L).obj X) := isKan L X
  let _ : KanComplex ((functor K).obj Y) := isKan K Y
  exact (KanComplex.W_iff_realizationWeakEquivalence _).mpr
    (mapBoth_realizationWeak a f ha hf)

end SSet.FunctorCore
