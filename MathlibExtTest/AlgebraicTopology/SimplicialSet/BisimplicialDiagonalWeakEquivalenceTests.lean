/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence

/-!
# Bisimplicial diagonal weak-equivalence tests

These tests pin the finite-product input, the sequential filtration API, and
the distinct outer-row and inner-row orientations of the diagonal theorem.
-/

noncomputable section

open CategoryTheory Limits MorphismProperty Opposite

open scoped Simplicial

namespace MathlibExtTest.BisimplicialDiagonalWeakEquivalence

universe u

example {A B : SSet.{u}} (f : A ⟶ B)
    (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences
      (Limits.prod.map f (𝟙 (Δ[0] : SSet.{u}))) :=
  SSet.realizationWeakEquivalences.prodMap_id_of_finite_right f hf

example {A B : SSet.{u}} (f : A ⟶ B)
    (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences
      (Limits.prod.map f (𝟙 (Δ[1] : SSet.{u}))) :=
  SSet.realizationWeakEquivalences.prodMap_id_of_finite_right f hf

example {A B : SSet.{u}} (f : A ⟶ B)
    (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences
      (Limits.prod.map f (𝟙 (SSet.boundary 1 : SSet.{u}))) :=
  SSet.realizationWeakEquivalences.prodMap_id_of_finite_right f hf

example (X : SimplicialObject SSet.{u}) (n : ℕ) :
    (SSet.diagonalFiltrationFunctor X).obj n =
      (SSet.diagonalFiltration X n : SSet.{u}) :=
  rfl

example (X : SimplicialObject SSet.{u}) {n m : ℕ} (h : n ≤ m) :
    Mono ((SSet.diagonalFiltrationFunctor X).map (homOfLE h)) := by
  rw [SSet.diagonalFiltrationFunctor_map]
  infer_instance

example (X : SimplicialObject SSet.{u}) (n : ℕ) :
    (SSet.diagonalFiltrationCocone X).ι.app n =
      (SSet.diagonalFiltration X n).ι :=
  rfl

example (X : SimplicialObject SSet.{u}) :
    IsColimit (SSet.diagonalFiltrationCocone X) :=
  SSet.diagonalFiltrationCoconeIsColimit X

example {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ) :
    (SSet.diagonalFiltrationNatTrans eta).app n =
      SSet.diagonalFiltrationNatMap eta n :=
  rfl

example {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hEta : ∀ n, SSet.realizationWeakEquivalences
      (eta.app (Opposite.op (SimplexCategory.mk n)))) :
    SSet.realizationWeakEquivalences
      (SSet.simplicialDiagonalFunctor.map eta) :=
  SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences eta hEta

example {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hEta : ∀ n, SSet.realizationWeakEquivalences
      ((SSet.simplicialTransposeFunctor.map eta).app
        (Opposite.op (SimplexCategory.mk n)))) :
    SSet.realizationWeakEquivalences
      (SSet.simplicialDiagonalFunctor.map eta) :=
  SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows
    eta hEta

example (X : SimplicialObject SSet.{u}) :
    SSet.realizationWeakEquivalences
      (SSet.simplicialDiagonalFunctor.map (𝟙 X)) := by
  apply SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences
  intro n
  exact SSet.realizationWeakEquivalences.id_mem _

section UniverseOne

example {A B : SSet.{1}} (f : A ⟶ B)
    (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences
      (Limits.prod.map f (𝟙 (Δ[1] : SSet.{1}))) :=
  SSet.realizationWeakEquivalences.prodMap_id_of_finite_right f hf

example {X Y : SimplicialObject SSet.{1}} (eta : X ⟶ Y)
    (hEta : ∀ n, SSet.realizationWeakEquivalences
      (eta.app (Opposite.op (SimplexCategory.mk n)))) :
    SSet.realizationWeakEquivalences
      (SSet.simplicialDiagonalFunctor.map eta) :=
  SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences eta hEta

example {X Y : SimplicialObject SSet.{1}} (eta : X ⟶ Y)
    (hEta : ∀ n, SSet.realizationWeakEquivalences
      ((SSet.simplicialTransposeFunctor.map eta).app
        (Opposite.op (SimplexCategory.mk n)))) :
    SSet.realizationWeakEquivalences
      (SSet.simplicialDiagonalFunctor.map eta) :=
  SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows
    eta hEta

end UniverseOne

section UniverseZero

example {X Y : SimplicialObject SSet.{0}} (eta : X ⟶ Y)
    (hEta : ∀ n, SSet.realizationWeakEquivalences
      (eta.app (Opposite.op (SimplexCategory.mk n)))) :
    SSet.realizationWeakEquivalences
      (SSet.simplicialDiagonalFunctor.map eta) :=
  SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences eta hEta

example {X Y : SimplicialObject SSet.{0}} (eta : X ⟶ Y)
    (hEta : ∀ n, SSet.realizationWeakEquivalences
      ((SSet.simplicialTransposeFunctor.map eta).app
        (Opposite.op (SimplexCategory.mk n)))) :
    SSet.realizationWeakEquivalences
      (SSet.simplicialDiagonalFunctor.map eta) :=
  SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows
    eta hEta

end UniverseZero

section NoGlobalModel

example : True := by
  fail_if_success
    let _ : HomotopicalAlgebra.ModelCategory SSet.{u} := inferInstance
  fail_if_success
    let _ : HomotopicalAlgebra.ModelCategory TopCat.{u} := inferInstance
  fail_if_success
    let _ : HomotopicalAlgebra.ModelCategory SSet.{1} := inferInstance
  fail_if_success
    let _ : HomotopicalAlgebra.ModelCategory TopCat.{1} := inferInstance
  fail_if_success
    let _ : HomotopicalAlgebra.ModelCategory SSet.{0} := inferInstance
  fail_if_success
    let _ : HomotopicalAlgebra.ModelCategory TopCat.{0} := inferInstance
  trivial

end NoGlobalModel

#print axioms SSet.realizationWeakEquivalences.prodMap_id_of_finite_right
#print axioms SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences
#print axioms SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows

end MathlibExtTest.BisimplicialDiagonalWeakEquivalence
