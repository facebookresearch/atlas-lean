/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomotopyInvariance
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.SimplexResolutionAugmentationWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.SimplexResolutionProductFiber

/-!
# Simplicial product Theorem A*

For a pair `(f,g) : X ⟶ Y ⨯ T`, suppose that for every simplex `y` of
`Y`, the left-fiber projection followed by `g` is a realized weak homotopy
equivalence. Then `(f,g)` is itself a realized weak homotopy equivalence.

The proof compares the simplex resolutions of `f` and
`prod.fst : Y ⨯ T ⟶ Y`. The product-fiber calculation gives an objectwise
weak equivalence between their pullback diagrams, Bousfield--Kan homotopy
invariance gives the top map, and the two augmentation equivalences close the
result by two-out-of-three.

Reference: T. Fiore and M. Pieper, *Waldhausen Additivity: Classical and
Quasicategorical*, Theorem 1.14, recalling Theorem A-hat-star of Jones, Kim,
Mhoon, Santhanam, Walker, and Grayson.

This file makes no Waldhausen additivity, Q/S comparison, loop-space,
K-theory, or spectrum claim and installs no model-category instance.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MorphismProperty Opposite Simplicial

universe u

namespace SSet

/-- The map of simplex resolutions induced by `(f,g) : X ⟶ Y ⨯ T` is a
realization weak equivalence under the all-degree left-fiber hypothesis. -/
theorem simplexResolutionMap_prod_mem_realizationWeakEquivalences
    {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
    (h : ∀ (m : ℕ) (y : Y _⦋m⦌),
      TopCat.weakHomotopyEquivalences
        (SSet.toTop.map (SSet.leftFiber.π f y ≫ g))) :
    realizationWeakEquivalences
      (simplexResolutionMap
        (p := f) (q := (prod.fst : Y ⨯ T ⟶ Y))
        (prod.lift f g) (prod.lift_fst f g)) := by
  unfold simplexResolutionMap simplexResolution
  apply bkHocolimMap_mem_realizationWeakEquivalences
  intro s
  change TopCat.weakHomotopyEquivalences
    (SSet.toTop.map
      ((SSet.simplexPullbackDiagramMap
        (p := f) (q := (prod.fst : Y ⨯ T ⟶ Y))
        (prod.lift f g) (prod.lift_fst f g)).app s))
  exact simplexPullbackDiagramMap_prod_obj_mem f g h s

/-- Simplicial product Theorem A*: if every left fiber of `f`, mapped to
`T` by `g`, is a realized weak homotopy equivalence, then the ordered pair
`prod.lift f g : X ⟶ Y ⨯ T` is a realized weak homotopy equivalence. -/
theorem theoremAStar
    {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
    (h : ∀ (m : ℕ) (y : Y _⦋m⦌),
      TopCat.weakHomotopyEquivalences
        (SSet.toTop.map (SSet.leftFiber.π f y ≫ g))) :
    TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (prod.lift f g)) := by
  have hResolution : realizationWeakEquivalences
      (simplexResolutionMap
        (p := f) (q := (prod.fst : Y ⨯ T ⟶ Y))
        (prod.lift f g) (prod.lift_fst f g)) :=
    simplexResolutionMap_prod_mem_realizationWeakEquivalences f g h
  have hAugSource : realizationWeakEquivalences
      (simplexResolutionAugmentation f) :=
    simplexResolutionAugmentation_mem_realizationWeakEquivalences f
  have hAugTarget : realizationWeakEquivalences
      (simplexResolutionAugmentation
        (prod.fst : Y ⨯ T ⟶ Y)) :=
    simplexResolutionAugmentation_mem_realizationWeakEquivalences
      (prod.fst : Y ⨯ T ⟶ Y)
  have hComposite : realizationWeakEquivalences
      (simplexResolutionAugmentation f ≫ prod.lift f g) := by
    have hTopRight := realizationWeakEquivalences.comp_mem
      (simplexResolutionMap
        (p := f) (q := (prod.fst : Y ⨯ T ⟶ Y))
        (prod.lift f g) (prod.lift_fst f g))
      (simplexResolutionAugmentation
        (prod.fst : Y ⨯ T ⟶ Y))
      hResolution hAugTarget
    rw [simplexResolutionAugmentation_naturality
      (p := f) (q := (prod.fst : Y ⨯ T ⟶ Y))
      (prod.lift f g) (prod.lift_fst f g)] at hTopRight
    exact hTopRight
  have hPair : realizationWeakEquivalences (prod.lift f g) :=
    realizationWeakEquivalences.of_precomp
      (simplexResolutionAugmentation f) (prod.lift f g)
      hAugSource hComposite
  change realizationWeakEquivalences (prod.lift f g)
  exact hPair

end SSet

end
