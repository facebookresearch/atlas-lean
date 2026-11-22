/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHocolim
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceCoproducts

/-!
# Homotopy invariance of the Bousfield--Kan carrier

A componentwise realization weak equivalence of simplicial-set
diagrams induces a realization weak equivalence on their Bousfield--Kan
homotopy-colimit carriers. In each outer bar degree the map is the coproduct
of coefficient maps at the left endpoints of weighted chains; the rowwise
diagonal theorem then supplies the result.

This file makes no Quillen Theorem A, Waldhausen additivity, Q/S comparison,
or realization-equivalence claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial

universe u

namespace SSet

/-- In every outer weighted-bar degree, a componentwise realization weak
equivalence induces a realization weak equivalence. The coefficient summand
is selected by the left endpoint `p.1.left` of the weighted chain. -/
theorem bkHocolimMap_row_mem_realizationWeakEquivalences
    {J : Type u} [Category.{0} J] {D E : J ⥤ SSet.{u}}
    (alpha : D ⟶ E)
    (hAlpha : ∀ j, realizationWeakEquivalences (alpha.app j))
    (a : SimplexCategoryᵒᵖ) :
    realizationWeakEquivalences
      ((StrictOrdinaryWeightedBar.wbarSimplicialMapF
        (CategoryBar.replUnit J) alpha).app a) := by
  induction a using Opposite.rec with
  | _ a =>
      induction a using SimplexCategory.rec with
      | _ n =>
          rw [StrictOrdinaryWeightedBar.wbarSimplicialMapF_app_mk]
          change realizationWeakEquivalences
            (Limits.Sigma.map
              (fun p : StrictOrdinaryWeightedBar.WIdx J
                (CategoryBar.replUnit J) n => alpha.app p.1.left))
          exact sigma_map_mem_realizationWeakEquivalences _
            (fun p => hAlpha p.1.left)

/-- A componentwise realization weak equivalence induces a realization weak
equivalence on Bousfield--Kan homotopy-colimit carriers. -/
theorem bkHocolimMap_mem_realizationWeakEquivalences
    {J : Type u} [Category.{0} J] {D E : J ⥤ SSet.{u}}
    (alpha : D ⟶ E)
    (hAlpha : ∀ j, realizationWeakEquivalences (alpha.app j)) :
    realizationWeakEquivalences (bkHocolimMap alpha) := by
  unfold bkHocolimMap
  apply simplicialDiagonal_map_mem_realizationWeakEquivalences
  intro n
  exact bkHocolimMap_row_mem_realizationWeakEquivalences alpha hAlpha
    (Opposite.op (SimplexCategory.mk n))

end SSet

end
