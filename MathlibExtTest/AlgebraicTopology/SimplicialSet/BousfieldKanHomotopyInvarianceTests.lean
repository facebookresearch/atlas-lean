/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomotopyInvariance

/-!
# Bousfield--Kan homotopy-invariance tests

These tests pin outer bar rows in degrees zero and one, the left-endpoint
coefficient orientation, the final diagonal theorem, and the identity-map
boundary. They make no Theorem A or additivity claim.
-/

open CategoryTheory Opposite Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.BousfieldKanHomotopyInvarianceTests

universe u

variable {J : Type u} [Category.{0} J]
variable {D E : J ⥤ SSet.{u}}

/-- Outer bar degree zero is covered by componentwise weak equivalences. -/
example (alpha : D ⟶ E)
    (hAlpha : ∀ j, SSet.realizationWeakEquivalences (alpha.app j)) :
    SSet.realizationWeakEquivalences
      ((StrictOrdinaryWeightedBar.wbarSimplicialMapF
        (CategoryBar.replUnit J) alpha).app (op ⦋0⦌)) :=
  SSet.bkHocolimMap_row_mem_realizationWeakEquivalences alpha hAlpha _

/-- Outer bar degree one retains the same left-endpoint coefficient rule. -/
example (alpha : D ⟶ E)
    (hAlpha : ∀ j, SSet.realizationWeakEquivalences (alpha.app j)) :
    SSet.realizationWeakEquivalences
      ((StrictOrdinaryWeightedBar.wbarSimplicialMapF
        (CategoryBar.replUnit J) alpha).app (op ⦋1⦌)) :=
  SSet.bkHocolimMap_row_mem_realizationWeakEquivalences alpha hAlpha _

/-- The component family in degree `n` is indexed at `p.1.left`. -/
example (alpha : D ⟶ E)
    (hAlpha : ∀ j, SSet.realizationWeakEquivalences (alpha.app j))
    (n : ℕ) :
    SSet.realizationWeakEquivalences
      (Limits.Sigma.map
        (fun p : StrictOrdinaryWeightedBar.WIdx J
          (CategoryBar.replUnit J) n => alpha.app p.1.left)) :=
  SSet.sigma_map_mem_realizationWeakEquivalences _
    (fun p => hAlpha p.1.left)

/-- The Bousfield--Kan map of a componentwise weak transformation is weak. -/
example (alpha : D ⟶ E)
    (hAlpha : ∀ j, SSet.realizationWeakEquivalences (alpha.app j)) :
    SSet.realizationWeakEquivalences (SSet.bkHocolimMap alpha) :=
  SSet.bkHocolimMap_mem_realizationWeakEquivalences alpha hAlpha

/-- Identity transformations give the boundary case. -/
example (D : J ⥤ SSet.{u}) :
    SSet.realizationWeakEquivalences (SSet.bkHocolimMap (𝟙 D)) :=
  SSet.bkHocolimMap_mem_realizationWeakEquivalences (𝟙 D)
    (fun j => SSet.realizationWeakEquivalences.id_mem (D.obj j))

/-- Strict carrier composition retains source-to-target order. -/
example {F : J ⥤ SSet.{u}} (alpha : D ⟶ E) (beta : E ⟶ F) :
    SSet.bkHocolimMap (alpha ≫ beta) =
      SSet.bkHocolimMap alpha ≫ SSet.bkHocolimMap beta :=
  SSet.bkHocolimMap_comp alpha beta

example {F : J ⥤ SSet.{u}} (alpha : D ⟶ E) (beta : E ⟶ F)
    (hAlpha : ∀ j, SSet.realizationWeakEquivalences (alpha.app j))
    (hBeta : ∀ j, SSet.realizationWeakEquivalences (beta.app j)) :
    SSet.realizationWeakEquivalences
      (SSet.bkHocolimMap (alpha ≫ beta)) := by
  apply SSet.bkHocolimMap_mem_realizationWeakEquivalences
  intro j
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    (hAlpha j) (hBeta j)

section UniverseOne

variable {J₁ : Type 1} [Category.{0} J₁]
variable {D₁ E₁ : J₁ ⥤ SSet.{1}}

example (alpha : D₁ ⟶ E₁)
    (hAlpha : ∀ j, SSet.realizationWeakEquivalences (alpha.app j)) :
    SSet.realizationWeakEquivalences (SSet.bkHocolimMap alpha) :=
  SSet.bkHocolimMap_mem_realizationWeakEquivalences alpha hAlpha

end UniverseOne

section UniverseZero

variable {J₀ : Type} [Category J₀]
variable {D₀ E₀ : J₀ ⥤ SSet.{0}}

example (alpha : D₀ ⟶ E₀)
    (hAlpha : ∀ j, SSet.realizationWeakEquivalences (alpha.app j)) :
    SSet.realizationWeakEquivalences (SSet.bkHocolimMap alpha) :=
  SSet.bkHocolimMap_mem_realizationWeakEquivalences alpha hAlpha

noncomputable example :
    let J := Discrete Empty
    let D := (Functor.const J).obj (⊥_ SSet.{0})
    SSet.realizationWeakEquivalences (SSet.bkHocolimMap (𝟙 D)) :=
  SSet.bkHocolimMap_mem_realizationWeakEquivalences (𝟙 _)
    (fun _j => SSet.realizationWeakEquivalences.id_mem _)

noncomputable example :
    let J := Discrete Bool
    let D := (Functor.const J).obj (⊥_ SSet.{0})
    SSet.realizationWeakEquivalences (SSet.bkHocolimMap (𝟙 D)) :=
  SSet.bkHocolimMap_mem_realizationWeakEquivalences (𝟙 _)
    (fun _j => SSet.realizationWeakEquivalences.id_mem _)

end UniverseZero

section NoGlobalModel

example : True := by
  fail_if_success
    let _ : HomotopicalAlgebra.ModelCategory SSet.{u} := inferInstance
  fail_if_success
    let _ : HomotopicalAlgebra.ModelCategory TopCat.{u} := inferInstance
  trivial

end NoGlobalModel

#print axioms SSet.bkHocolimMap_row_mem_realizationWeakEquivalences
#print axioms SSet.bkHocolimMap_mem_realizationWeakEquivalences

end MathlibExtTest.AlgebraicTopology.SimplicialSet.BousfieldKanHomotopyInvarianceTests
